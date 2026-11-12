import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Global.AdelicGLSiegelFinitenessStatement

/-!
# Geometry of the actual adelic Siegel sets

Torus coordinates on Siegel sets, finiteness of rational translates between compact sets,
and the multiplicity bounds for Siegel sets that follow from Siegel finiteness.
-/

noncomputable section

universe uF

open scoped Classical NNReal Pointwise
open NumberField

namespace Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

/-- **Siegel data.** -/
theorem exists_siegel_data (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F))
    (c : ℝ) (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (hc : 0 < c) :
    ∃ (Q₁ : Set (AdelicGL F n)) (K : ℝ), IsCompact Q₁ ∧ 0 ≤ K ∧
      ∀ h ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c, ∃ (Ngl : AdelicGL F n)
        (ω : Fin n → Ideles F) (x : Fin n → ℝ) (κ : AdelicGL F n),
        (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) ∈ ΩN ∧ (∀ i, ω i ∈ C) ∧
        κ ∈ PrimitiveAdelicHeight.standardCompact F n ∧ Automorphic.CuspidalL2.Chamber K x ∧
        h = Ngl * PrimitiveAdelicHeight.diagonalGL ω * AdelicGL.ofInfinite F n (torInf F n x) * κ ∧
        (AdelicGL.ofInfinite F n (torInf F n x))⁻¹ * h ∈ Q₁ := by
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  set K : ℝ := max 0 (Real.log c / Module.finrank ℚ F) with hKdef
  have hK : 0 ≤ K := le_max_left _ _
  set E₀ : Set (Adeles F) := ⋃ i : Fin n, ⋃ j : Fin n,
    ((fun N : Matrix (Fin n) (Fin n) (Adeles F) => N i j) '' ΩN ∪
      (fun N : Matrix (Fin n) (Fin n) (Adeles F) => N.adjugate i j) '' ΩN) with hE₀def
  have hE₀ : IsCompact E₀ := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    (hΩ.image (continuous_id.matrix_elem i j)).union
      (hΩ.image (continuous_id.matrix_adjugate.matrix_elem i j))
  set E : Set (Adeles F) := (fun p : ℝ × Adeles F => realScale F p.1 * p.2) ''
    (Set.Icc 0 (Real.exp (n * K)) ×ˢ E₀) with hEdef
  have hE : IsCompact E := (isCompact_Icc.prod hE₀).image
    (((continuous_realScale F).comp continuous_fst).mul continuous_snd)
  set W₁ : Set (AdelicGL F n) :=
    (fun ω : Fin n → Ideles F => (PrimitiveAdelicHeight.diagonalGL ω : AdelicGL F n)) ''
      Set.univ.pi fun _ => C with hW₁def
  have hW₁ : IsCompact W₁ := (isCompact_univ_pi fun _ => hC).image (continuous_diagonalGL F n)
  refine ⟨AdelicMatrixHeight.entryBox F n E * W₁ *
      (PrimitiveAdelicHeight.standardCompact F n : Set (AdelicGL F n)),
    K, ((AdelicMatrixHeight.isCompact_entryBox F n hE).mul hW₁).mul
      (PrimitiveAdelicHeight.isCompact_standardCompact F n), hK, fun h hh => ?_⟩
  obtain ⟨N, ω, r, κ, hhv, hN, hω, hκ, hr⟩ := hh
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, ∀ i, r i = expUnit (x i) :=
    ⟨fun i => Real.log ((r i : ℝ≥0) : ℝ), fun i => by
      apply Units.ext
      apply NNReal.eq
      rw [coe_expUnit, Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (r i).ne_zero))]⟩
  have hrx : r = fun i => expUnit (x i) := funext hx
  subst hrx
  have hch : Automorphic.CuspidalL2.Chamber K x := by
    intro i j hij
    have h1 := hr i j hij
    rw [PositiveRealIdeles.absoluteValue_full, PositiveRealIdeles.absoluteValue_full,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow,
      coe_expUnit, coe_expUnit, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h1
    have h2 : (Module.finrank ℚ F : ℝ) * x j ≤ Real.log c + Module.finrank ℚ F * x i := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    have hdpos : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.mpr hd
    have : x j - x i ≤ Real.log c / Module.finrank ℚ F := by
      rw [le_div_iff₀ hdpos]; linarith
    exact this.trans (le_max_right _ _)
  set A := AdelicGL.ofInfinite F n (torInf F n x) with hAdef
  set W : AdelicGL F n := PrimitiveAdelicHeight.diagonalGL ω with hWdef
  have hAval : (A : Matrix (Fin n) (Fin n) (Adeles F)) =
      Matrix.diagonal fun i => ((PositiveRealIdeles.full F (expUnit (x i)) : Ideles F) :
        Adeles F) :=
    ofInfinite_torInf_val F n x
  have hWA : W * A = A * W := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hAval]
    change Matrix.diagonal (fun i => ((ω i : Ideles F) : Adeles F)) * _ =
      _ * Matrix.diagonal (fun i => ((ω i : Ideles F) : Adeles F))
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  set Ngl := h * κ⁻¹ * (W * A)⁻¹ with hNgldef
  have hNgl : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) = N := by
    have e1 : (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) =
        (h : Matrix (Fin n) (Fin n) (Adeles F)) *
          ((κ⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) *
          (((W * A)⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) := by
      rw [hNgldef, Units.val_mul, Units.val_mul]
    have e2 : (h : Matrix (Fin n) (Fin n) (Adeles F)) =
        N * ((W * A : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) *
          (κ : Matrix (Fin n) (Fin n) (Adeles F)) := by
      rw [hhv, Units.val_mul, hAval, ← Matrix.mul_assoc]
      rfl
    rw [e1, e2, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have hdet : N.det = 1 := PrimitiveAdelicHeight.IsUnitriangular.det_eq_one (hΩN N hN)
  have hNtri : N.IsUpperTriangular := (hΩN N hN).1
  have hNinv : ((Ngl⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) = N.adjugate := by
    rw [Matrix.coe_units_inv, hNgl, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have hadjtri : N.adjugate.IsUpperTriangular := by
    have : Invertible (Ngl : Matrix (Fin n) (Fin n) (Adeles F)) := Units.invertible Ngl
    have h1 := Matrix.blockTriangular_inv_of_blockTriangular
      (M := (Ngl : Matrix (Fin n) (Fin n) (Adeles F))) (hNgl ▸ hNtri)
    rwa [← Matrix.coe_units_inv, hNinv] at h1
  have hhA : h = A * ((A⁻¹ * Ngl * A) * W * κ) := by
    rw [hNgldef, hWA]
    group
  refine ⟨Ngl, ω, x, κ, hNgl ▸ hN, hω, hκ, hch, ?_, ?_⟩
  · show h = Ngl * W * A * κ
    rw [hNgldef]
    group
  rw [hhA, inv_mul_cancel_left]
  refine Set.mul_mem_mul (Set.mul_mem_mul ⟨fun i j => ?_, fun i j => ?_⟩
    ⟨ω, fun i _ => hω i, rfl⟩) hκ
  · rw [Units.val_mul, Units.val_mul, hNgl]
    exact conj_apply_mem F n hK hch E₀ N hNtri
      (fun i j => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inl ⟨N, hN, rfl⟩⟩⟩) i j
  · have : (A⁻¹ * Ngl * A)⁻¹ = A⁻¹ * Ngl⁻¹ * A := by group
    rw [this, Units.val_mul, Units.val_mul, hNinv]
    exact conj_apply_mem F n hK hch E₀ N.adjugate hadjtri
      (fun i j => Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inr ⟨N, hN, rfl⟩⟩⟩) i j

/-- **Torus coordinates on a Siegel set.** Every element of a Siegel set is an archimedean
torus element in a chamber times an element of a fixed compact set. -/
theorem exists_torus_form (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F))
    (c : ℝ) (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) (hc : 0 < c) :
    ∃ (Q₁ : Set (AdelicGL F n)) (K : ℝ), IsCompact Q₁ ∧ 0 ≤ K ∧
      ∀ h ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c, ∃ (x : Fin n → ℝ) (q : AdelicGL F n),
        q ∈ Q₁ ∧ h = AdelicGL.ofInfinite F n (torInf F n x) * q ∧
          Automorphic.CuspidalL2.Chamber K x := by
  obtain ⟨Q₁, K, hQ₁, hK, hdata⟩ := exists_siegel_data F n ΩN C c hΩ hΩN hC hc
  refine ⟨Q₁, K, hQ₁, hK, fun h hh => ?_⟩
  obtain ⟨-, -, x, -, -, -, -, hch, -, hq⟩ := hdata h hh
  exact ⟨x, _, hq, (mul_inv_cancel_left _ _).symm, hch⟩

/-- Only finitely many rational matrices move a point of one compact set into another. -/
theorem finite_rational_compact (K₁ K₂ : Set (AdelicGL F n)) (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) :
    {γ : RationalGL F n | ∃ g ∈ K₁, AdelicGL.rational F n γ * g ∈ K₂}.Finite := by
  have := adeles_t2Space F
  have := principalAdeles_discreteTopology F
  have hD : IsDiscrete (principalAdeles F : Set (Adeles F)) := ⟨inferInstance⟩
  set B : Set (AdelicGL F n) := (fun p : AdelicGL F n × AdelicGL F n => p.1 * p.2⁻¹) ''
    (K₂ ×ˢ K₁) with hBdef
  have hB : IsCompact B := (hK₂.prod hK₁).image (continuous_fst.mul continuous_snd.inv)
  have hentry (i j : Fin n) : {x : F | algebraMap F (Adeles F) x ∈
      (fun g : AdelicGL F n => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) '' B}.Finite := by
    have hc : IsCompact ((fun g : AdelicGL F n => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) ''
        B) := hB.image ((Units.continuous_val.matrix_elem i j))
    have hfin := (hc.inter_right (principalAdeles_isClosed F)).finite
      (hD.mono Set.inter_subset_right)
    refine (hfin.preimage
      (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).injOn).subset ?_
    intro x hx
    exact ⟨hx, x, rfl⟩
  have hfin : (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      {x : F | algebraMap F (Adeles F) x ∈
        (fun g : AdelicGL F n => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) '' B}).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => hentry i j
  refine (hfin.preimage (f := fun γ : RationalGL F n => fun i j =>
      (γ : Matrix (Fin n) (Fin n) F) i j)
    (fun γ₁ _ γ₂ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))).subset ?_
  rintro γ ⟨g, hg, hγg⟩ i - j -
  refine ⟨AdelicGL.rational F n γ, ⟨(AdelicGL.rational F n γ * g, g), ⟨hγg, hg⟩, ?_⟩, rfl⟩
  simp

/-- A finite self-intersection set bounds the number of rational translates of a point
lying in the set. -/
theorem encard_rational_mul_mem_le (S : Set (AdelicGL F n)) (x : AdelicGL F n) :
    {γ : RationalGL F n | AdelicGL.rational F n γ * x ∈ S}.encard ≤
      {γ : RationalGL F n | ∃ g ∈ S, AdelicGL.rational F n γ * g ∈ S}.encard := by
  rcases Set.eq_empty_or_nonempty {γ : RationalGL F n | AdelicGL.rational F n γ * x ∈ S}
    with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  · refine Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_
      (fun γ₁ _ γ₂ _ h => mul_right_cancel h)
    intro γ hγ
    refine ⟨AdelicGL.rational F n γ₀ * x, hγ₀, ?_⟩
    have : AdelicGL.rational F n (γ * γ₀⁻¹) * (AdelicGL.rational F n γ₀ * x) =
        AdelicGL.rational F n γ * x := by
      rw [map_mul, map_inv, ← mul_assoc, inv_mul_cancel_right]
    rw [this]
    exact hγ

/-- A determinant-one matrix as an invertible matrix (inverse its adjugate). -/
def detOneGL (N : Matrix (Fin n) (Fin n) (Adeles F)) (hN : N.det = 1) : AdelicGL F n where
  val := N
  inv := N.adjugate
  val_inv := by rw [Matrix.mul_adjugate, hN, one_smul]
  inv_val := by rw [Matrix.adjugate_mul, hN, one_smul]

/-- The chamber condition of the Siegel set in logarithmic coordinates. -/
def siegelRatioSet (c : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i j : Fin n, i.val + 1 = j.val →
    Real.exp (x j) ^ Module.finrank ℚ F ≤ c * Real.exp (x i) ^ Module.finrank ℚ F}

theorem isClosed_siegelRatioSet (c : ℝ) : IsClosed (siegelRatioSet F n c) := by
  simp only [siegelRatioSet, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_le ((Real.continuous_exp.comp (continuous_apply j)).pow _)
    (continuous_const.mul ((Real.continuous_exp.comp (continuous_apply i)).pow _))

theorem absoluteValue_full_expUnit (x : ℝ) :
    ((IdeleAbsoluteValue.full F (PositiveRealIdeles.full F (expUnit x)) : ℝ≥0) : ℝ) =
      Real.exp x ^ Module.finrank ℚ F := by
  rw [PositiveRealIdeles.absoluteValue_full, Units.val_pow_eq_pow_val, NNReal.coe_pow,
    coe_expUnit]

/-- The parameter map of a Siegel set. -/
def siegelParamMap (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ)
    (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N) :
    ΩN × (Fin n → C) × siegelRatioSet F n c × PrimitiveAdelicHeight.standardCompact F n →
      AdelicGL F n :=
  fun p => detOneGL F n p.1.1 (PrimitiveAdelicHeight.IsUnitriangular.det_eq_one (hΩN _ p.1.2)) *
    PrimitiveAdelicHeight.diagonalGL (fun i => ((p.2.1 i : C) : Ideles F)) *
    AdelicGL.ofInfinite F n (torInf F n p.2.2.1.1) * p.2.2.2.1

theorem continuous_siegelParamMap (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F)))
    (C : Set (Ideles F)) (c : ℝ) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N) :
    Continuous (siegelParamMap F n ΩN C c hΩN) := by
  have h1 : Continuous fun p : ΩN × (Fin n → C) × siegelRatioSet F n c ×
      PrimitiveAdelicHeight.standardCompact F n =>
      detOneGL F n p.1.1 (PrimitiveAdelicHeight.IsUnitriangular.det_eq_one (hΩN _ p.1.2)) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val.comp continuous_fst,
      continuous_id.matrix_adjugate.comp (continuous_subtype_val.comp continuous_fst)⟩
  have h2 : Continuous fun p : ΩN × (Fin n → C) × siegelRatioSet F n c ×
      PrimitiveAdelicHeight.standardCompact F n =>
      (PrimitiveAdelicHeight.diagonalGL (fun i => ((p.2.1 i : C) : Ideles F)) : AdelicGL F n) :=
    (continuous_diagonalGL F n).comp
      (continuous_pi fun i => continuous_subtype_val.comp
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
  have h3 : Continuous fun p : ΩN × (Fin n → C) × siegelRatioSet F n c ×
      PrimitiveAdelicHeight.standardCompact F n =>
      AdelicGL.ofInfinite F n (torInf F n p.2.2.1.1) :=
    (map_continuous (AdelicGL.ofInfinite F n)).comp ((continuous_torInf F n).comp
      (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd))))
  have h4 : Continuous fun p : ΩN × (Fin n → C) × siegelRatioSet F n c ×
      PrimitiveAdelicHeight.standardCompact F n => (p.2.2.2.1 : AdelicGL F n) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  exact ((h1.mul h2).mul h3).mul h4

theorem range_siegelParamMap (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F)))
    (C : Set (Ideles F)) (c : ℝ) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N) :
    Set.range (siegelParamMap F n ΩN C c hΩN) = PrimitiveAdelicHeight.siegelSetGL F n ΩN C c := by
  ext h
  constructor
  · rintro ⟨⟨⟨N, hN⟩, ω, ⟨x, hx⟩, ⟨κ, hκ⟩⟩, rfl⟩
    refine ⟨N, fun i => (ω i : Ideles F), fun i => expUnit (x i), κ, ?_, hN,
      fun i => (ω i).2, hκ, fun i j hij => ?_⟩
    · simp only [siegelParamMap, Units.val_mul]
      rw [ofInfinite_torInf_val]
      rfl
    · rw [absoluteValue_full_expUnit, absoluteValue_full_expUnit]
      exact hx i j hij
  · rintro ⟨N, ω, r, κ, hv, hN, hω, hκ, hr⟩
    obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, ∀ i, r i = expUnit (x i) :=
      ⟨fun i => Real.log ((r i : ℝ≥0) : ℝ), fun i => by
        apply Units.ext
        apply NNReal.eq
        rw [coe_expUnit, Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (r i).ne_zero))]⟩
    have hrx : r = fun i => expUnit (x i) := funext hx
    subst hrx
    refine ⟨⟨⟨N, hN⟩, fun i => ⟨ω i, hω i⟩, ⟨x, fun i j hij => ?_⟩, ⟨κ, hκ⟩⟩, ?_⟩
    · have := hr i j hij
      rwa [absoluteValue_full_expUnit, absoluteValue_full_expUnit] at this
    · apply Units.ext
      simp only [siegelParamMap, Units.val_mul]
      rw [ofInfinite_torInf_val, hv]
      rfl

/-- **Siegel sets are Borel.** -/
theorem measurableSet_siegelSetGL [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]
    (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ)
    (hΩ : IsCompact ΩN) (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N)
    (hC : IsCompact C) :
    MeasurableSet (PrimitiveAdelicHeight.siegelSetGL F n ΩN C c) := by
  have := adelicGL_t2Space F n
  have : CompactSpace ΩN := isCompact_iff_compactSpace.mp hΩ
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have : CompactSpace (PrimitiveAdelicHeight.standardCompact F n) :=
    isCompact_iff_compactSpace.mp (PrimitiveAdelicHeight.isCompact_standardCompact F n)
  have : SigmaCompactSpace (siegelRatioSet F n c) :=
    (isClosed_siegelRatioSet F n c).sigmaCompactSpace
  have hsc := isSigmaCompact_range (continuous_siegelParamMap F n ΩN C c hΩN)
  rw [range_siegelParamMap] at hsc
  obtain ⟨K, hK, hKU⟩ := hsc
  rw [← hKU]
  exact MeasurableSet.iUnion fun m => (hK m).isClosed.measurableSet

/-- Left multiplication by unitriangular elements enlarges the unipotent part of a Siegel
set. -/
theorem mul_mem_siegelSetGL {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))} {C : Set (Ideles F)}
    {c : ℝ} (U : Set (AdelicGL F n)) {u h : AdelicGL F n} (hu : u ∈ U)
    (hh : h ∈ PrimitiveAdelicHeight.siegelSetGL F n ΩN C c) :
    u * h ∈ PrimitiveAdelicHeight.siegelSetGL F n
      ((fun p : AdelicGL F n × Matrix (Fin n) (Fin n) (Adeles F) =>
        (p.1 : Matrix (Fin n) (Fin n) (Adeles F)) * p.2) '' (U ×ˢ ΩN)) C c := by
  obtain ⟨N, ω, r, κ, hv, hN, hω, hκ, hr⟩ := hh
  refine ⟨(u : Matrix (Fin n) (Fin n) (Adeles F)) * N, ω, r, κ, ?_, ⟨(u, N), ⟨hu, hN⟩, rfl⟩,
    hω, hκ, hr⟩
  rw [Units.val_mul, hv]
  simp only [Matrix.mul_assoc]

theorem isCompact_mul_image {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))}
    (U : Set (AdelicGL F n)) (hU : IsCompact U) (hΩ : IsCompact ΩN) :
    IsCompact ((fun p : AdelicGL F n × Matrix (Fin n) (Fin n) (Adeles F) =>
        (p.1 : Matrix (Fin n) (Fin n) (Adeles F)) * p.2) '' (U ×ˢ ΩN)) :=
  (hU.prod hΩ).image ((Units.continuous_val.comp continuous_fst).mul continuous_snd)

theorem isUnitriangular_mul_image {ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))}
    (U : Set (AdelicGL F n))
    (hU : ∀ u ∈ U, PrimitiveAdelicHeight.IsUnitriangular (u : Matrix (Fin n) (Fin n) (Adeles F)))
    (hΩN : ∀ N ∈ ΩN, PrimitiveAdelicHeight.IsUnitriangular N) :
    ∀ M ∈ (fun p : AdelicGL F n × Matrix (Fin n) (Fin n) (Adeles F) =>
        (p.1 : Matrix (Fin n) (Fin n) (Adeles F)) * p.2) '' (U ×ˢ ΩN),
      PrimitiveAdelicHeight.IsUnitriangular M := by
  rintro _ ⟨⟨u, N⟩, ⟨hu, hN⟩, rfl⟩
  exact (hU u hu).mul (hΩN N hN)

end Langlands.Global
