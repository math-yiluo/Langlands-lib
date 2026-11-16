import Langlands.Global.RankinSelberg.WhittakerCellAdelicScaling
import Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement
import Langlands.Global.RankinSelberg.UnfoldingWhittaker
import Langlands.HarmonicAnalysis.TriangularHaarModulus
import Langlands.Analysis.Local.QuotientAutomorphismStatement

/-! # The Haar modulus of torus conjugation on `N_m(𝔸)`

Conjugation by `ι_v(ϖ^λ)` acts on the strictly upper entries of `N_m(𝔸)` by
`n_ij ↦ ι_v(ϖ)^(λ_i - λ_j) n_ij`, and left translations of `N_m(𝔸)` are triangular in
these entries. Its Haar modulus is therefore `N(v) ^ (-∑_(i<j) (λ_i - λ_j))`. The paired
Markdown records the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.UnipotentConjugationModulus

local instance conjSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance conjSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section RankTriangular

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

/-- **Haar modulus in ranked triangular coordinates.** Let `Φ : H ≃ₜ (I → A)` be
coordinates, indexed by a finite type with a rank function, in which the `k`-th coordinate
of every left translation differs from the `k`-th input coordinate by an amount depending
only on the input coordinates of smaller rank. If `ψ` acts on the `k`-th coordinate by a
measurable map `s k` with `r k • (s k)_* ν = ν` for an additive Haar measure `ν` on `A`,
then the Haar modulus of `ψ` is `∏ k, r k`. -/
theorem mulEquivHaarChar_eq_prod_of_rankTriangular (ν : Measure A) [IsAddHaarMeasure ν]
    {I : Type*} [Fintype I] (rank : I → ℕ) (Φ : H ≃ₜ (I → A))
    (htri : ∀ (g : H) (k : I) (x y : I → A), (∀ l, rank l < rank k → x l = y l) →
      Φ (g * Φ.symm x) k - x k = Φ (g * Φ.symm y) k - y k)
    (ψ : H ≃ₜ* H) (s : I → A → A) (hs : ∀ k, Measurable (s k))
    (r : I → ℝ≥0) (hr : ∀ k, r k • ν.map (s k) = ν)
    (hψ : ∀ h k, Φ (ψ h) k = s k (Φ h k)) :
    mulEquivHaarChar ψ = ∏ k, r k := by
  classical
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  have hψm : Measurable ψ := ψ.continuous.measurable
  let π : Measure (I → A) := Measure.pi fun _ => ν
  let μN : Measure H := π.map Φ.symm
  -- left invariance from the triangular translation lemma
  have hinv : IsMulLeftInvariant μN := by
    constructor
    intro g
    have hmeas : Measurable fun x : I → A => Φ (g * Φ.symm x) :=
      hΦ.comp ((measurable_const_mul g).comp hΦs)
    have hS : MeasurePreserving (fun x : I → A => Φ (g * Φ.symm x)) π π := by
      have h := HarmonicAnalysis.finiteTriangularTranslation I (fun _ => A) (fun _ => ν) rank
        (fun x k => Φ (g * Φ.symm x) k - x k) (hmeas.sub measurable_id)
        (fun k x y hxy => htri g k x y hxy)
      simpa only [sub_add_cancel] using h
    have hcomp : (fun x => g * x) ∘ Φ.symm = Φ.symm ∘ fun v => Φ (g * Φ.symm v) := by
      funext v; simp
    change Measure.map (fun x => g * x) (π.map Φ.symm) = π.map Φ.symm
    rw [Measure.map_map (measurable_const_mul g) hΦs, hcomp,
      ← Measure.map_map hΦs hS.measurable, hS.map_eq]
  have hfin : IsFiniteMeasureOnCompacts μN := IsFiniteMeasureOnCompacts.map π Φ.symm
  have hopen : IsOpenPosMeasure μN := Φ.symm.continuous.isOpenPosMeasure_map Φ.symm.surjective
  have hHaar : IsHaarMeasure μN := { }
  have : SecondCountableTopology H := Φ.isEmbedding.secondCountableTopology
  have hreg : Regular μN := by
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
    exact regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  -- the coordinatewise scalings
  have hν0 : ν ≠ 0 := NeZero.ne ν
  have hr0 : ∀ k, r k ≠ 0 := by
    intro k hk
    apply hν0
    rw [← hr k, hk, zero_smul]
  have hmap : ∀ k, ν.map (s k) = (r k)⁻¹ • ν := by
    intro k
    conv_rhs => rw [← hr k]
    rw [smul_smul, inv_mul_cancel₀ (hr0 k), one_smul]
  have hpi : π.map (fun v k => s k (v k)) = (∏ k, r k)⁻¹ • π := by
    have : ∀ k, SigmaFinite (ν.map (s k)) := fun k => by rw [hmap k]; infer_instance
    rw [Measure.pi_map_pi (fun k => (hs k).aemeasurable)]
    simp_rw [hmap]
    rw [HarmonicAnalysis.pi_nnreal_smul, ← Finset.prod_inv_distrib]
  have hψcoord : ψ ∘ Φ.symm = Φ.symm ∘ fun v k => s k (v k) := by
    funext v
    apply Φ.injective
    funext k
    simp [hψ]
  apply HarmonicAnalysis.mulEquivHaarChar_eq_of_smul_map μN ψ
  change (∏ k, r k) • Measure.map ψ (π.map Φ.symm) = π.map Φ.symm
  have hsm : Measurable fun (v : I → A) k => s k (v k) :=
    measurable_pi_iff.mpr fun k => (hs k).comp (measurable_pi_apply k)
  rw [Measure.map_map hψm hΦs, hψcoord, ← Measure.map_map hΦs hsm, hpi,
    Measure.map_smul _ hΦs.aemeasurable, smul_smul,
    mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hr0 k), one_smul]

end RankTriangular

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation `x ↦ g x g⁻¹` as a continuous automorphism. -/
def conjugation (g : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj g
  continuous_toFun := by
    change Continuous fun x => g * x * g⁻¹
    fun_prop
  continuous_invFun := by
    change Continuous fun x => g⁻¹ * x * g
    fun_prop

@[simp] theorem conjugation_apply (g x : G) : conjugation g x = g * x * g⁻¹ := rfl

end Conjugation

theorem prod_zpow_eq_zpow_sum {I G : Type*} [CommGroup G] (g : G) (s : Finset I) (e : I → ℤ) :
    ∏ i ∈ s, g ^ e i = g ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

section Coordinates

variable {F : Type u} [Field F] [NumberField F] {m : ℕ}

/-- The strictly upper entry positions `(i, j)`, `i < j`, of an `m × m` matrix. -/
abbrev UpperIndex (m : ℕ) := Σ i : Fin m, {j : Fin m // i < j}

/-- The adelic matrix of an adelic point of `GL_m`. -/
def matrixOf (x : Points F m) : Matrix (Fin m) (Fin m) (Adeles F) :=
  ((GeneralLinearGroupPoints.adelicEquiv F m x : AdelicGL F m) :
    Matrix (Fin m) (Fin m) (Adeles F))

theorem matrixOf_mul (x y : Points F m) : matrixOf (x * y) = matrixOf x * matrixOf y := by
  simp only [matrixOf, map_mul, Units.val_mul]

theorem continuous_matrixOf : Continuous (matrixOf : Points F m → _) :=
  Units.continuous_val.comp (GeneralLinearGroupPoints.adelicHomeomorph F m).continuous

theorem matrixOf_inv_of_diagonal {a : Points F m} {d : Fin m → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F)) :
    matrixOf a⁻¹ = Matrix.diagonal fun i => (((d i)⁻¹ : (Adeles F)ˣ) : Adeles F) := by
  change (((GeneralLinearGroupPoints.adelicEquiv F m a⁻¹ : AdelicGL F m)) :
    Matrix (Fin m) (Fin m) (Adeles F)) = _
  rw [map_inv]
  apply Units.inv_eq_of_mul_eq_one_right
  change matrixOf a * _ = 1
  rw [ha, Matrix.diagonal_mul_diagonal]
  simp

theorem matrixOf_conj_apply {a : Points F m} {d : Fin m → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F)) (x : Points F m)
    (i j : Fin m) :
    matrixOf (a * x * a⁻¹) i j =
      (d i : Adeles F) * matrixOf x i j * (((d j)⁻¹ : (Adeles F)ˣ) : Adeles F) := by
  rw [matrixOf_mul, matrixOf_mul, matrixOf_inv_of_diagonal ha, ha, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

theorem mem_unipotentAdelic_iff (x : Points F m) :
    x ∈ unipotentAdelic F m ↔ PrimitiveAdelicHeight.IsUnitriangular (matrixOf x) :=
  Unfolding.mem_unipotentAdelic_iff F x

theorem conj_mem_of_diagonal {a : Points F m} {d : Fin m → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F)) {x : Points F m}
    (hx : x ∈ unipotentAdelic F m) : a * x * a⁻¹ ∈ unipotentAdelic F m := by
  rw [mem_unipotentAdelic_iff] at hx ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [matrixOf_conj_apply ha, hx.1 hij, mul_zero, zero_mul]
  · rw [matrixOf_conj_apply ha, hx.2 i, mul_one, Units.mul_inv]

/-- A point with diagonal adelic matrix normalizes `N_m(𝔸)`. -/
theorem conj_mem_iff_of_diagonal {a : Points F m} {d : Fin m → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F)) (x : Points F m) :
    conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m := by
  rw [conjugation_apply]
  refine ⟨fun hx => ?_, conj_mem_of_diagonal ha⟩
  have h := conj_mem_of_diagonal (matrixOf_inv_of_diagonal ha) hx
  have he : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [he] at h

/-- The unitriangular matrix with prescribed strictly upper entries. -/
def upperMatrix (c : UpperIndex m → Adeles F) : Matrix (Fin m) (Fin m) (Adeles F) :=
  fun i j => if h : i < j then c ⟨i, j, h⟩ else if i = j then 1 else 0

theorem isUnitriangular_upperMatrix (c : UpperIndex m → Adeles F) :
    PrimitiveAdelicHeight.IsUnitriangular (upperMatrix c) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    simp [upperMatrix, not_lt.mpr hij'.le, hij'.ne']
  · simp [upperMatrix]

theorem continuous_upperMatrix :
    Continuous (upperMatrix : (UpperIndex m → Adeles F) → _) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold upperMatrix
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const

/-- The adelic point with unitriangular matrix of prescribed strictly upper entries. -/
def pointOf (c : UpperIndex m → Adeles F) : Points F m :=
  (GeneralLinearGroupPoints.adelicEquiv F m).symm
    (Unfolding.unitriangularUnit (upperMatrix c) (isUnitriangular_upperMatrix c))

theorem matrixOf_pointOf (c : UpperIndex m → Adeles F) :
    matrixOf (pointOf c) = upperMatrix c := by
  simp only [matrixOf, pointOf, MulEquiv.apply_symm_apply]
  rfl

theorem pointOf_mem (c : UpperIndex m → Adeles F) : pointOf c ∈ unipotentAdelic F m := by
  rw [mem_unipotentAdelic_iff, matrixOf_pointOf]
  exact isUnitriangular_upperMatrix c

theorem continuous_pointOf : Continuous (pointOf : (UpperIndex m → Adeles F) → Points F m) := by
  have hu : Continuous fun c : UpperIndex m → Adeles F =>
      Unfolding.unitriangularUnit (upperMatrix c) (isUnitriangular_upperMatrix c) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_upperMatrix, continuous_upperMatrix.matrix_adjugate⟩
  exact (GeneralLinearGroupPoints.adelicHomeomorph F m).symm.continuous.comp hu

variable (F m) in
/-- **Entry coordinates on `N_m(𝔸)`**: the strictly upper entries of the adelic matrix. -/
def coordinates : unipotentAdelic F m ≃ₜ (UpperIndex m → Adeles F) where
  toFun h p := matrixOf (h : Points F m) p.1 p.2.1
  invFun c := ⟨pointOf c, pointOf_mem c⟩
  left_inv h := by
    apply Subtype.ext
    apply (GeneralLinearGroupPoints.adelicEquiv F m).injective
    apply Units.ext
    change matrixOf (pointOf _) = matrixOf (h : Points F m)
    rw [matrixOf_pointOf]
    have hu := (mem_unipotentAdelic_iff _).mp h.property
    ext i j
    unfold upperMatrix
    split_ifs with h1 h2
    · rfl
    · subst h2
      exact (hu.2 i).symm
    · have hji : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      exact (hu.1 hji).symm
  right_inv c := by
    funext p
    change matrixOf (pointOf c) p.1 p.2.1 = c p
    rw [matrixOf_pointOf]
    simp [upperMatrix, p.2.2]
  continuous_toFun := continuous_pi fun p =>
    ((continuous_apply p.2.1).comp (continuous_apply p.1)).comp
      (continuous_matrixOf.comp continuous_subtype_val)
  continuous_invFun := continuous_pointOf.subtype_mk _

theorem coordinates_apply (h : unipotentAdelic F m) (p : UpperIndex m) :
    coordinates F m h p = matrixOf (h : Points F m) p.1 p.2.1 :=
  rfl

theorem matrixOf_coordinates_symm (c : UpperIndex m → Adeles F) :
    matrixOf ((coordinates F m).symm c : Points F m) = upperMatrix c :=
  matrixOf_pointOf c

/-- Left translations of `N_m(𝔸)` are triangular in the entry coordinates, for the rank
`m - i` of the entry `(i, j)`. -/
theorem coordinates_mul_sub_eq (g : unipotentAdelic F m) (p : UpperIndex m)
    (x y : UpperIndex m → Adeles F)
    (hxy : ∀ l : UpperIndex m, m - (l.1 : ℕ) < m - (p.1 : ℕ) → x l = y l) :
    coordinates F m (g * (coordinates F m).symm x) p - x p =
      coordinates F m (g * (coordinates F m).symm y) p - y p := by
  have hg := (mem_unipotentAdelic_iff _).mp g.property
  have key : ∀ z : UpperIndex m → Adeles F,
      coordinates F m (g * (coordinates F m).symm z) p - z p =
        ∑ k, (matrixOf (g : Points F m) - 1) p.1 k * upperMatrix z k p.2.1 := by
    intro z
    have hz : z p = upperMatrix z p.1 p.2.1 := by simp [upperMatrix, p.2.2]
    rw [coordinates_apply, Subgroup.coe_mul, matrixOf_mul, matrixOf_coordinates_symm, hz,
      ← Matrix.mul_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply]
  rw [key x, key y]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hik : p.1 < k
  · congr 1
    unfold upperMatrix
    split_ifs with hkj
    · apply hxy
      have := k.isLt
      change m - (k : ℕ) < m - (p.1 : ℕ)
      have : (p.1 : ℕ) < k := hik
      omega
    · rfl
    · rfl
  · have h0 : (matrixOf (g : Points F m) - 1) p.1 k = 0 := by
      rw [Matrix.sub_apply]
      rcases (not_lt.mp hik).lt_or_eq with hki | hki
      · rw [hg.1 hki, Matrix.one_apply_ne hki.ne', sub_zero]
      · subst hki
        rw [hg.2, Matrix.one_apply_eq, sub_self]
    rw [h0, zero_mul, zero_mul]

/-- Conjugation by a point with diagonal adelic matrix scales the entry `(i, j)` by
`d_i d_j⁻¹`. -/
theorem coordinates_conj_of_diagonal {a : Points F m} {d : Fin m → (Adeles F)ˣ}
    (ha : matrixOf a = Matrix.diagonal fun i => (d i : Adeles F))
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m)
    (h : unipotentAdelic F m) (p : UpperIndex m) :
    coordinates F m (QuotientIntegration.subgroupAutomorphism (unipotentAdelic F m)
        (conjugation a) hα h) p =
      ((d p.1 * (d p.2.1)⁻¹ : (Adeles F)ˣ) : Adeles F) * coordinates F m h p := by
  rw [coordinates_apply, QuotientIntegration.subgroupAutomorphism_apply, conjugation_apply,
    matrixOf_conj_apply ha, coordinates_apply, Units.val_mul]
  ring

end Coordinates

section LocalPoint

variable {F : Type u} [Field F] [NumberField F] {m : ℕ}

theorem coe_finiteIdeleInclusion (v : FinitePlace F) (u : (FiniteCompletion F v)ˣ) :
    ((finiteIdeleInclusion F v u : (Adeles F)ˣ) : Adeles F) =
      ((1 : InfiniteAdeles F),
        ((WhittakerCellAdelicScaling.finiteSingle F v u : (FiniteAdeles F)ˣ) :
          FiniteAdeles F)) :=
  rfl

/-- The adelic matrix of `ι_v(ϖ^λ)` is the diagonal matrix of the ideles `ι_v(ϖ^(λ_i))`. -/
theorem matrixOf_localPoint_torus (v : FinitePlace F) (ϖ : (FiniteCompletion F v)ˣ)
    (lam : Fin m → ℤ) :
    matrixOf (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) =
      Matrix.diagonal fun i =>
        ((finiteIdeleInclusion F v (ϖ ^ lam i) : (Adeles F)ˣ) : Adeles F) := by
  classical
  set x := FiniteAdelicGL.localInclusion F m v (GeneralLinear.Iwasawa.torus ϖ lam)
  have hpt : GeneralLinearGroupPoints.adelicEquiv F m
      (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) = AdelicGL.ofFinite F m x := by
    rw [localPoint, MulEquiv.apply_symm_apply]
  ext i j
  change @Eq (InfiniteAdeles F × FiniteAdeles F) _ _
  have h1 : (matrixOf (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) i j).1 =
      AdelicGL.infinite F m (AdelicGL.ofFinite F m x) i j := by
    rw [AdelicGL.infinite_apply, ← hpt]
    rfl
  have h2 : (matrixOf (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) i j).2 =
      AdelicGL.finite F m (AdelicGL.ofFinite F m x) i j := by
    rw [AdelicGL.finite_apply, ← hpt]
    rfl
  have hinf : AdelicGL.infinite F m (AdelicGL.ofFinite F m x) = 1 := by
    apply Units.ext; rfl
  have hfin : AdelicGL.finite F m (AdelicGL.ofFinite F m x) = x := by
    apply Units.ext; rfl
  apply Prod.ext
  · rw [h1, hinf]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, coe_finiteIdeleInclusion]
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp [Matrix.one_apply_ne hij]
      rfl
  · rw [h2, hfin]
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    have hx : (x i j : FiniteAdeles F) w = FiniteAdelicGL.localProjection F m w x i j := rfl
    rw [hx]
    by_cases hw : w = v
    · subst hw
      rw [FiniteAdelicGL.localProjection_localInclusion]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, coe_finiteIdeleInclusion]
        change ((GeneralLinear.Iwasawa.torus ϖ lam).val i i) =
          ((WhittakerCellAdelicScaling.finiteSingle F w (ϖ ^ lam i) : FiniteAdeles F)) w
        rw [WhittakerCellAdelicScaling.finiteSingle_apply_self, GeneralLinear.Iwasawa.torus_val,
          Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij]
        change ((GeneralLinear.Iwasawa.torus ϖ lam).val i j) = (0 : FiniteAdeles F) w
        rw [GeneralLinear.Iwasawa.torus_val, Matrix.diagonal_apply_ne _ hij]
        rfl
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F m v w hw]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, coe_finiteIdeleInclusion]
        change ((1 : FiniteLocalGL F m w).val i i) =
          ((WhittakerCellAdelicScaling.finiteSingle F v (ϖ ^ lam i) : FiniteAdeles F)) w
        rw [WhittakerCellAdelicScaling.finiteSingle_apply_of_ne F hw, Units.val_one,
          Matrix.one_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij]
        change ((1 : FiniteLocalGL F m w).val i j) = (0 : FiniteAdeles F) w
        rw [Units.val_one, Matrix.one_apply_ne hij]
        rfl

variable (F) in
/-- `ι_v(ϖ^λ)` normalizes `N_m(𝔸)`. -/
theorem conj_localPoint_torus_mem_iff (v : FinitePlace F) (ϖ : (FiniteCompletion F v)ˣ)
    (lam : Fin m → ℤ) (x : Points F m) :
    conjugation (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) x ∈
        unipotentAdelic F m ↔ x ∈ unipotentAdelic F m :=
  conj_mem_iff_of_diagonal (matrixOf_localPoint_torus v ϖ lam) x

theorem sum_upperIndex (e : Fin m → Fin m → ℤ) :
    ∑ p : UpperIndex m, e p.1 p.2.1 = ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, e i j := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Finset.sum_subtype (Finset.Ioi i) (fun j => Finset.mem_Ioi) (e i)).symm

variable (F) in
/-- **The modulus of `ι_v(ϖ^λ)` on `N_m(𝔸)`.** Conjugation by `ι_v(ϖ^λ)` scales Haar
measure on `N_m(𝔸)` by `N(v) ^ (-∑_(i<j) (λ_i - λ_j))`. -/
theorem mulEquivHaarChar_conj_localPoint_torus
    [MeasurableSpace (unipotentAdelic F m)] [BorelSpace (unipotentAdelic F m)]
    [LocallyCompactSpace (unipotentAdelic F m)]
    (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (WhittakerCellAdelicScaling.valuation F v) ϖ)
    (lam : Fin m → ℤ)
    (hα : ∀ x, conjugation (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) x ∈
      unipotentAdelic F m ↔ x ∈ unipotentAdelic F m) :
    mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism (unipotentAdelic F m)
        (conjugation (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam))) hα) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-modulusExponent lam) := by
  classical
  let := adeles_locallyCompactSpace F
  have := adeles_secondCountableTopology F
  let : MeasurableSpace (Adeles F) := borel _
  have : BorelSpace (Adeles F) := ⟨rfl⟩
  set t := finiteIdeleInclusion F v ϖ
  set d : Fin m → (Adeles F)ˣ := fun i => t ^ lam i
  have ha : matrixOf (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)) =
      Matrix.diagonal fun i => (d i : Adeles F) := by
    rw [matrixOf_localPoint_torus]
    simp only [d, t, map_zpow]
  let c : UpperIndex m → (Adeles F)ˣ := fun p => d p.1 * (d p.2.1)⁻¹
  rw [mulEquivHaarChar_eq_prod_of_rankTriangular (addHaar : Measure (Adeles F))
    (fun p : UpperIndex m => m - (p.1 : ℕ)) (coordinates F m)
    (fun g k x y hxy => coordinates_mul_sub_eq g k x y hxy) _
    (fun p y => (c p : Adeles F) * y)
    (fun p => (continuous_const.mul continuous_id).measurable)
    (fun p => WhittakerCellAdelicScaling.mulLeftHaarChar (c p))
    (fun p => addEquivAddHaarChar_smul_map _ (ContinuousAddEquiv.mulLeft (c p)))
    (fun h p => coordinates_conj_of_diagonal ha hα h p)]
  rw [← map_prod]
  have hprod : ∏ p, c p = t ^ modulusExponent lam := by
    have hc : ∀ p : UpperIndex m, c p = t ^ (lam p.1 - lam p.2.1) := fun p => by
      simp only [c, d, zpow_sub]
    simp_rw [hc]
    rw [prod_zpow_eq_zpow_sum, modulusExponent,
      sum_upperIndex (fun i j => lam i - lam j)]
  rw [hprod, WhittakerCellAdelicScaling.mulLeftHaarChar_apply]
  exact WhittakerCellAdelicScaling.addEquivAddHaarChar_mulLeft_finiteIdeleInclusion_zpow F v hϖ _

end LocalPoint

end Langlands.Global.RankinSelbergGlobal.UnipotentConjugationModulus
