import Langlands.Global.RankinSelberg.UnfoldingSteps

/-! # The transpose-inverse twist by the long Weyl element, for the dual unfolding -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global PrimitiveAdelicHeight

local instance unfoldingDualGLSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingDualGLSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Matrix

variable (n : ℕ) (R : Type*) [CommRing R]

/-- `g ↦ w ᵗg⁻¹ w⁻¹` with `w` the long Weyl element. -/
def dualConjGL : Matrix.GeneralLinearGroup (Fin n) R ≃* Matrix.GeneralLinearGroup (Fin n) R :=
  (GeneralLinear.inverseTranspose n R).trans (MulAut.conj (GeneralLinear.weylLong n R))

theorem dualConjGL_apply (g : Matrix.GeneralLinearGroup (Fin n) R) :
    dualConjGL n R g =
      GeneralLinear.weylLong n R * GeneralLinear.inverseTranspose n R g *
        GeneralLinear.weylLong n R := by
  simp [dualConjGL, MulAut.conj_apply]

theorem dualConjGL_entry (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    (dualConjGL n R g : Matrix (Fin n) (Fin n) R) i j =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
  rw [dualConjGL_apply]
  exact (GeneralLinear.weylLong_conjugate_entry n R _ i j).trans
    (GeneralLinear.inverseTranspose_entry n R g i.rev j.rev)

theorem dualConjGL_dualConjGL (g : Matrix.GeneralLinearGroup (Fin n) R) :
    dualConjGL n R (dualConjGL n R g) = g := by
  rw [dualConjGL_apply, dualConjGL_apply, map_mul, map_mul,
    GeneralLinear.inverseTranspose_weylLong, GeneralLinear.inverseTranspose_involutive]
  simp only [mul_assoc, GeneralLinear.weylLong_mul_self, mul_one]
  rw [← mul_assoc, GeneralLinear.weylLong_mul_self, one_mul]

/-- The twist commutes with entrywise ring homomorphisms. -/
theorem dualConjGL_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    dualConjGL n S (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (dualConjGL n R g) := by
  ext i j
  rw [dualConjGL_entry, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.map_apply, dualConjGL_entry]

/-- The twist of an upper unitriangular matrix whose inverse is upper unitriangular is upper
unitriangular. -/
theorem isUnitriangular_dualConjGL (g : Matrix.GeneralLinearGroup (Fin n) R)
    (hg : IsUnitriangular ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R)) :
    IsUnitriangular ((dualConjGL n R g : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [dualConjGL_entry]
    exact hg.1 (Fin.rev_lt_rev.mpr hij)
  · rw [dualConjGL_entry]
    exact hg.2 _

/-- The superdiagonal of the twist is the reversed negated superdiagonal. -/
theorem sum_superdiag_dualConjGL {r : ℕ} (g : Matrix.GeneralLinearGroup (Fin (r + 1)) R)
    (hg : IsUnitriangular (g : Matrix (Fin (r + 1)) (Fin (r + 1)) R))
    (hg' : IsUnitriangular ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (r + 1)) R) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) R)) :
    ∑ i : Fin r, (dualConjGL (r + 1) R g : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
        i.castSucc i.succ =
      -∑ i : Fin r, (g : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i.castSucc i.succ := by
  have hinv : ∀ k : Fin r,
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin (r + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
        k.castSucc k.succ = -(g : Matrix (Fin (r + 1)) (Fin (r + 1)) R) k.castSucc k.succ := by
    intro k
    have h1 := superdiag_mul_of_isUnitriangular hg' hg k
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := k)).ne] at h1
    linear_combination -h1
  simp only [dualConjGL_entry, Fin.rev_castSucc, Fin.rev_succ, hinv]
  rw [Finset.sum_neg_distrib]
  congr 1
  exact Fintype.sum_equiv Fin.revPerm _ _ fun k => rfl

end Matrix

section Points

variable (F : Type u) [Field F] [NumberField F]

/-- The twist `g ↦ w ᵗg⁻¹ w⁻¹` on adelic points. -/
def dualConj (n : ℕ) : Points F n ≃* Points F n :=
  ((GeneralLinearGroupPoints.adelicEquiv F n).trans (dualConjGL n (Adeles F))).trans
    (GeneralLinearGroupPoints.adelicEquiv F n).symm

theorem adelicEquiv_dualConj (n : ℕ) (x : Points F n) :
    GeneralLinearGroupPoints.adelicEquiv F n (dualConj F n x) =
      dualConjGL n (Adeles F) (GeneralLinearGroupPoints.adelicEquiv F n x) := by
  simp [dualConj]

theorem dualConj_dualConj (n : ℕ) (x : Points F n) : dualConj F n (dualConj F n x) = x := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_dualConj, adelicEquiv_dualConj, dualConjGL_dualConjGL]

/-- The point `w ᵗg⁻¹` at which `dualFunction` evaluates. -/
def dualPoint (n : ℕ) (g : Points F n) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (GeneralLinear.weylLong n (Adeles F) * GeneralLinear.inverseTranspose n (Adeles F)
      (GeneralLinearGroupPoints.adelicEquiv F n g))

theorem dualFunction_eq (n : ℕ) (f : Points F n → ℂ) (g : Points F n) :
    dualFunction F n f g = f (dualPoint F n g) := rfl

/-- `w ᵗ(xy)⁻¹ = (w ᵗx⁻¹ w⁻¹)(w ᵗy⁻¹)`. -/
theorem dualPoint_mul (n : ℕ) (x y : Points F n) :
    dualPoint F n (x * y) = dualConj F n x * dualPoint F n y := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [dualPoint, adelicEquiv_dualConj, map_mul, MulEquiv.apply_symm_apply,
    dualConjGL_apply]
  simp only [mul_assoc]
  rw [← mul_assoc (GeneralLinear.weylLong n (Adeles F)) (GeneralLinear.weylLong n (Adeles F)),
    GeneralLinear.weylLong_mul_self, one_mul]

theorem continuous_dualConj (n : ℕ) : Continuous (dualConj F n) := by
  have h : Continuous fun g : Matrix.GeneralLinearGroup (Fin n) (Adeles F) =>
      dualConjGL n (Adeles F) g := by
    simp only [dualConjGL_apply]
    exact (continuous_const.mul (GeneralLinear.continuous_inverseTranspose n (Adeles F))).mul
      continuous_const
  exact (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    (h.comp (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)

theorem continuous_dualPoint (n : ℕ) : Continuous (dualPoint F n) := by
  have h : Continuous fun g : Matrix.GeneralLinearGroup (Fin n) (Adeles F) =>
      GeneralLinear.weylLong n (Adeles F) * GeneralLinear.inverseTranspose n (Adeles F) g :=
    continuous_const.mul (GeneralLinear.continuous_inverseTranspose n (Adeles F))
  exact (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    (h.comp (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)

/-- The twist preserves `N_n(𝔸)`. -/
theorem dualConj_mem_unipotentAdelic {n : ℕ} (u : unipotentAdelic F n) :
    dualConj F n (u : Points F n) ∈ unipotentAdelic F n := by
  rw [mem_unipotentAdelic_iff, adelicEquiv_dualConj]
  apply isUnitriangular_dualConjGL
  rw [← map_inv]
  exact isUnitriangular_of_mem_unipotentAdelic F u⁻¹

/-- The twist as an automorphism of `N_n(𝔸)`. -/
def dualConjUnipotent (n : ℕ) : unipotentAdelic F n ≃* unipotentAdelic F n where
  toFun u := ⟨dualConj F n u, dualConj_mem_unipotentAdelic F u⟩
  invFun u := ⟨dualConj F n u, dualConj_mem_unipotentAdelic F u⟩
  left_inv u := Subtype.ext (dualConj_dualConj F n u)
  right_inv u := Subtype.ext (dualConj_dualConj F n u)
  map_mul' u v := Subtype.ext (map_mul (dualConj F n) (u : Points F n) v)

theorem coe_dualConjUnipotent {n : ℕ} (u : unipotentAdelic F n) :
    ((dualConjUnipotent F n u : unipotentAdelic F n) : Points F n) = dualConj F n u := rfl

theorem continuous_dualConjUnipotent (n : ℕ) : Continuous (dualConjUnipotent F n) :=
  ((continuous_dualConj F n).comp continuous_subtype_val).subtype_mk _

/-- The generic character of the twist is the inverse character. -/
theorem genericCharacter_dualConjUnipotent (r : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (u : unipotentAdelic F (r + 1)) :
    genericCharacter F r ψ (fun _ => 1) (dualConjUnipotent F (r + 1) u) =
      (genericCharacter F r ψ (fun _ => 1) u)⁻¹ := by
  simp only [genericCharacter, map_one, one_mul]
  rw [← AddChar.map_neg_eq_inv]
  congr 1
  change ∑ i : Fin r, ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)
      (dualConj F (r + 1) (u : Points F (r + 1))) : Matrix.GeneralLinearGroup _ _) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ = _
  rw [adelicEquiv_dualConj]
  refine sum_superdiag_dualConjGL (Adeles F) _ (isUnitriangular_of_mem_unipotentAdelic F u) ?_
  rw [← map_inv]
  exact isUnitriangular_of_mem_unipotentAdelic F u⁻¹

/-- The twist of a rational point is rational. -/
theorem dualConj_rational (n : ℕ) (q : RationalGroupPoints F (Scheme F n)) :
    dualConj F n (AdelicGroupPoints.rational F (Scheme F n) q) =
      AdelicGroupPoints.rational F (Scheme F n) ((GeneralLinearGroupPoints.rationalEquiv F n).symm
        (dualConjGL n F (GeneralLinearGroupPoints.rationalEquiv F n q))) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_dualConj, GeneralLinearGroupPoints.adelicEquiv_rational,
    GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]
  exact dualConjGL_map n F (algebraMap F (Adeles F)) _

theorem dualConj_mem_rationalSubgroup (n : ℕ) {x : Points F n}
    (hx : x ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    dualConj F n x ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  obtain ⟨q, rfl⟩ := hx
  rw [dualConj_rational]
  exact ⟨_, rfl⟩

/-- `N_n(F)` is the set of rational points lying in `N_n(𝔸)`. -/
theorem mem_unipotentRationalImage_iff_mem_inf (n : ℕ) (x : Points F n) :
    x ∈ unipotentRationalImage F n ↔
      x ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) ∧ x ∈ unipotentAdelic F n := by
  constructor
  · intro hx
    refine ⟨unipotentRationalImage_le F n hx, ?_⟩
    obtain ⟨q, rfl⟩ := hx
    exact (AdelicSubgroupPoints.rational F (Scheme F n) (upperUnipotent F n) q).property
  · rintro ⟨⟨q, rfl⟩, hN⟩
    have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
    have hU : q ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F n) (upperUnipotent F n) := by
      rw [mem_rationalPoints_upperUnipotent_iff]
      rw [mem_unipotentAdelic_iff, GeneralLinearGroupPoints.adelicEquiv_rational] at hN
      refine ⟨fun i j hij => hinj ?_, fun i => hinj ?_⟩
      · have := hN.1 hij
        rw [AdelicGL.rational_apply] at this
        rw [this, map_zero]
      · have := hN.2 i
        rw [AdelicGL.rational_apply] at this
        rw [this, map_one]
    exact ⟨⟨q, hU⟩, rfl⟩

theorem dualConj_mem_unipotentRationalImage (n : ℕ) {x : Points F n}
    (hx : x ∈ unipotentRationalImage F n) : dualConj F n x ∈ unipotentRationalImage F n := by
  rw [mem_unipotentRationalImage_iff_mem_inf] at hx ⊢
  exact ⟨dualConj_mem_rationalSubgroup F n hx.1, dualConj_mem_unipotentAdelic F ⟨x, hx.2⟩⟩

/-- The twist preserves `N_n(F)` inside `N_n(𝔸)`. -/
theorem dualConjUnipotent_mem_rationalSubgroup (n : ℕ)
    (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)) :
    dualConjUnipotent F n (l : unipotentAdelic F n) ∈
      AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) := by
  have h := dualConj_mem_unipotentRationalImage F n
    ((mem_unipotentRationalImage_iff F n _).mpr ⟨l, rfl⟩)
  obtain ⟨l', hl'⟩ := (mem_unipotentRationalImage_iff F n _).mp h
  have : (l' : unipotentAdelic F n) = dualConjUnipotent F n l := Subtype.ext hl'
  rw [← this]
  exact l'.property

end Points

section TwistMeasure

variable (F : Type u) [Field F] [NumberField F]

local instance dualUnipotentAdelicLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- The twist as a topological group automorphism of `N_n(𝔸)`. -/
def dualConjUnipotentContinuous (n : ℕ) : unipotentAdelic F n ≃ₜ* unipotentAdelic F n where
  toMulEquiv := dualConjUnipotent F n
  continuous_toFun := continuous_dualConjUnipotent F n
  continuous_invFun := continuous_dualConjUnipotent F n

theorem dualConjUnipotent_dualConjUnipotent (n : ℕ) (u : unipotentAdelic F n) :
    dualConjUnipotent F n (dualConjUnipotent F n u) = u :=
  Subtype.ext (dualConj_dualConj F n u)

/-- The preimage of the fundamental domain of `N_n(F)` under the twist is again a strict
fundamental domain. -/
theorem existsUnique_mem_preimage_dualConjUnipotent (n : ℕ) (x : unipotentAdelic F n) :
    ∃! l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n),
      (l : unipotentAdelic F n) * x ∈ dualConjUnipotent F n ⁻¹' unipotentFundamentalDomain F n := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  obtain ⟨l, hl, hlu⟩ := LeftCosetSpace.fundamentalDomain_unique _ hΛd (dualConjUnipotent F n x)
  refine ⟨⟨dualConjUnipotent F n l, dualConjUnipotent_mem_rationalSubgroup F n l⟩, ?_, ?_⟩
  · show dualConjUnipotent F n (dualConjUnipotent F n l * x) ∈ unipotentFundamentalDomain F n
    rw [map_mul, dualConjUnipotent_dualConjUnipotent]
    exact hl
  · intro l' hl'
    have h1 : (⟨dualConjUnipotent F n l', dualConjUnipotent_mem_rationalSubgroup F n l'⟩ :
        AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)) *
          dualConjUnipotent F n x ∈ unipotentFundamentalDomain F n := by
      have : dualConjUnipotent F n ((l' : unipotentAdelic F n) * x) ∈
          unipotentFundamentalDomain F n := hl'
      rwa [map_mul] at this
    have h2 := hlu _ h1
    apply Subtype.ext
    have h3 := congrArg (fun k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n)
      (upperUnipotent F n) => dualConjUnipotent F n (k : unipotentAdelic F n)) h2
    simpa [dualConjUnipotent_dualConjUnipotent] using h3

/-- The twist preserves Haar measure on `N_n(𝔸)`: the image of Haar is a multiple of Haar, and
the twist permutes the strict fundamental domains of `N_n(F)`, of equal finite positive mass. -/
theorem measurePreserving_dualConjUnipotent (n : ℕ) :
    MeasurePreserving (dualConjUnipotent F n) (Measure.haar : Measure (unipotentAdelic F n))
      Measure.haar := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  have := compactSpace_unipotentRationalQuotient F n
  have hαm : Measurable (dualConjUnipotent F n) := (continuous_dualConjUnipotent F n).measurable
  refine ⟨hαm, ?_⟩
  have hκ := Measure.isMulLeftInvariant_eq_smul
    (Measure.map (dualConjUnipotentContinuous F n) (Measure.haar : Measure (unipotentAdelic F n)))
    (Measure.haar : Measure (unipotentAdelic F n))
  set c := Measure.haarScalarFactor
    (Measure.map (dualConjUnipotentContinuous F n) (Measure.haar : Measure (unipotentAdelic F n)))
    (Measure.haar : Measure (unipotentAdelic F n))
  have hsNm := LeftCosetSpace.measurableSet_fundamentalDomain _ hΛd
  have hfd1 : IsFundamentalDomain
      (AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))
      (dualConjUnipotent F n ⁻¹' unipotentFundamentalDomain F n)
      (Measure.haar : Measure (unipotentAdelic F n)) :=
    IsFundamentalDomain.mk' (hαm hsNm).nullMeasurableSet
      (existsUnique_mem_preimage_dualConjUnipotent F n)
  have hfd2 := LeftCosetSpace.isFundamentalDomain _ hΛd
    (Measure.haar : Measure (unipotentAdelic F n))
  have heq := hfd1.measure_eq hfd2
  have h1 : Measure.map (dualConjUnipotentContinuous F n)
      (Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n) =
      (Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n) := by
    have h0 : Measure.map (dualConjUnipotentContinuous F n)
        (Measure.haar : Measure (unipotentAdelic F n)) (unipotentFundamentalDomain F n) =
        (Measure.haar : Measure (unipotentAdelic F n))
          ((dualConjUnipotentContinuous F n) ⁻¹' unipotentFundamentalDomain F n) :=
      Measure.map_apply (map_continuous _).measurable hsNm
    exact h0.trans heq
  have hne0 : (Measure.haar : Measure (unipotentAdelic F n))
      (unipotentFundamentalDomain F n) ≠ 0 := by
    rw [haar_unipotentFundamentalDomain]
    exact ENNReal.inv_ne_zero.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_top _ _ _)
  have hnetop : (Measure.haar : Measure (unipotentAdelic F n))
      (unipotentFundamentalDomain F n) ≠ ∞ := by
    rw [haar_unipotentFundamentalDomain]
    exact ENNReal.inv_ne_top.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero _ _ _)
  have hc : (c : ℝ≥0∞) = 1 := by
    rw [hκ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact (ENNReal.mul_left_inj hne0 hnetop).mp (by rw [one_mul]; exact h1)
  have hc' : c = 1 := by exact_mod_cast hc
  change Measure.map (dualConjUnipotentContinuous F n) _ = _
  rw [hκ, hc', one_smul]

/-- Integrals of left `N_n(F)`-invariant functions over the fundamental domain of `N_n(F)` in
`N_n(𝔸)` are unchanged by the twist. -/
theorem setIntegral_comp_dualConjUnipotent (n : ℕ) {G : unipotentAdelic F n → ℂ}
    (hG : ∀ (l : AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))
      (m : unipotentAdelic F n), G ((l : unipotentAdelic F n) * m) = G m) :
    ∫ m in unipotentFundamentalDomain F n, G (dualConjUnipotent F n m) ∂Measure.haar =
      ∫ m in unipotentFundamentalDomain F n, G m ∂Measure.haar := by
  have hΛd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  have := LeftCosetSpace.countable_of_isDiscrete _ hΛd
  have hαm : Measurable (dualConjUnipotent F n) := (continuous_dualConjUnipotent F n).measurable
  have hsNm := LeftCosetSpace.measurableSet_fundamentalDomain _ hΛd
  have hemb : MeasurableEmbedding (dualConjUnipotent F n) :=
    (dualConjUnipotentContinuous F n).toHomeomorph.measurableEmbedding
  have hpre : dualConjUnipotent F n ⁻¹' (dualConjUnipotent F n ⁻¹' unipotentFundamentalDomain F n) =
      unipotentFundamentalDomain F n := by
    ext m
    simp [dualConjUnipotent_dualConjUnipotent]
  have h1 := (measurePreserving_dualConjUnipotent F n).setIntegral_preimage_emb hemb G
    (dualConjUnipotent F n ⁻¹' unipotentFundamentalDomain F n)
  rw [hpre] at h1
  rw [h1]
  have hfd1 : IsFundamentalDomain
      (AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n))
      (dualConjUnipotent F n ⁻¹' unipotentFundamentalDomain F n)
      (Measure.haar : Measure (unipotentAdelic F n)) :=
    IsFundamentalDomain.mk' (hαm hsNm).nullMeasurableSet
      (existsUnique_mem_preimage_dualConjUnipotent F n)
  exact hfd1.setIntegral_eq (LeftCosetSpace.isFundamentalDomain _ hΛd _) fun l m => hG l m

end TwistMeasure

section Rectangle

variable {R : Type*} [CommRing R]

/-- `[[n g, 0], [x, h]] = diag(n, I) [[g, 0], [x, h]]`. -/
theorem lowerBlockPair_mul_left {a d : ℕ} (N G : GeneralLinear a R)
    (x : Matrix (Fin d) (Fin a) R) (hh : GeneralLinear.lowerTriangularSubgroup d R) :
    GeneralLinear.lowerBlockPair (N * G) x hh =
      GeneralLinear.rankInclusion d N * GeneralLinear.lowerBlockPair G x hh := by
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_add, GeneralLinear.rankInclusion, Matrix.one_apply]

/-- The rank inclusion of a rank inclusion, reindexed, is the padding of the Library. -/
theorem reindex_rankInclusion_rankInclusion {a d : ℕ} {n : ℕ} (e : a + d + 1 = n)
    (h : a ≤ n) (N : GeneralLinear a R) :
    GeneralLinear.reindex (finCongr e)
        (GeneralLinear.rankInclusion 1 (GeneralLinear.rankInclusion d N)) = padGL h N := by
  ext i j
  obtain ⟨i', rfl⟩ := (finCongr e).surjective i
  obtain ⟨j', rfl⟩ := (finCongr e).surjective j
  rw [padGL_apply]
  simp only [GeneralLinear.reindex, MulEquiv.coe_mk, Units.coe_mapEquiv]
  change Matrix.reindex (finCongr e) (finCongr e) _ (finCongr e i') (finCongr e j') = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp only [finCongr_apply, Fin.val_cast]
  refine Fin.addCases (fun i₁ => ?_) (fun i₃ => ?_) i' <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₃ => ?_) j'
  · refine Fin.addCases (fun i₀ => ?_) (fun i₂ => ?_) i₁ <;>
      refine Fin.addCases (fun j₀ => ?_) (fun j₂ => ?_) j₁ <;>
      (simp [GeneralLinear.rankInclusion, Matrix.one_apply, Fin.ext_iff]; try omega)
  · refine Fin.addCases (fun i₀ => ?_) (fun i₂ => ?_) i₁ <;>
      (simp [GeneralLinear.rankInclusion, Fin.ext_iff]; try omega)
  · refine Fin.addCases (fun j₀ => ?_) (fun j₂ => ?_) j₁ <;>
      (simp [GeneralLinear.rankInclusion, Fin.ext_iff]; try omega)
  · simp [GeneralLinear.rankInclusion, Matrix.one_apply, Fin.ext_iff]

end Rectangle

section RectanglePoints

variable (F : Type u) [Field F] [NumberField F]

/-- `rect(n g, x) = diag(n, I) rect(g, x)`. -/
theorem rectangularPoint_mul_left {r t : ℕ} (h : t < r) (n g : Points F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    rectangularPoint F h (n * g) x =
      pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) n * rectangularPoint F h g x := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, adelicEquiv_pad]
  simp only [rectangularPoint, MulEquiv.apply_symm_apply, map_mul]
  rw [GeneralLinear.lowerBlockLocalization, GeneralLinear.lowerBlockLocalization,
    lowerBlockPair_mul_left, map_mul, map_mul,
    reindex_rankInclusion_rankInclusion _ (Nat.le_of_lt (Nat.succ_lt_succ h))]

end RectanglePoints

end Langlands.Global.RankinSelbergGlobal.Unfolding
