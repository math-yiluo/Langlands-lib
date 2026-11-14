import Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicFamily
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.FiniteAlgebraIdempotentTorus
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.SplitTorus

/-! # A split torus of dimension the Witt index in the connected isometry group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteAlgebraUnits

/-! ### Scaling a family of orthogonal idempotent pairs -/

section FamilyScaling

variable {K A : Type u} [Field K] [Ring A] [Algebra K A] {I : Type*} [Fintype I] [DecidableEq I]

/-- A family of pairs `(pₖ, p'ₖ)` of idempotents of `A` which are all mutually orthogonal:
`pₖ pₗ = δₖₗ pₖ`, `p'ₖ p'ₗ = δₖₗ p'ₖ` and `pₖ p'ₗ = p'ₖ pₗ = 0`. -/
structure IsOrthogonalIdempotentPairs (p p' : I → A) : Prop where
  left_left : ∀ k l, p k * p l = if k = l then p k else 0
  left_right : ∀ k l, p k * p' l = 0
  right_left : ∀ k l, p' k * p l = 0
  right_right : ∀ k l, p' k * p' l = if k = l then p' k else 0

variable (p p' : I → A) (R : Type u) [CommRing R] [Algebra K R]

/-- The summand `(tₖ - 1) pₖ + (tₖ⁻¹ - 1) p'ₖ` of `R ⊗[K] A`. -/
def familyScalingSummand (t : I → Rˣ) (k : I) : R ⊗[K] A :=
  ((t k : R) - 1) • ((1 : R) ⊗ₜ[K] p k) + ((((t k)⁻¹ : Rˣ) : R) - 1) • ((1 : R) ⊗ₜ[K] p' k)

/-- The element `1 + ∑ₖ ((tₖ - 1) pₖ + (tₖ⁻¹ - 1) p'ₖ)` of `R ⊗[K] A`, which scales each `pₖ` by
`tₖ` and each `p'ₖ` by `tₖ⁻¹`. -/
def familyScalingValue (t : I → Rˣ) : R ⊗[K] A :=
  1 + ∑ k, familyScalingSummand (K := K) p p' R t k

omit [Fintype I] [DecidableEq I] in
theorem familyScalingSummand_eq (t : I → Rˣ) (k : I) :
    familyScalingSummand (K := K) p p' R t k =
      ((t k : R) - 1) ⊗ₜ[K] p k + ((((t k)⁻¹ : Rˣ) : R) - 1) ⊗ₜ[K] p' k := by
  simp [familyScalingSummand, TensorProduct.smul_tmul']

omit [DecidableEq I] in
@[simp] theorem familyScalingValue_one : familyScalingValue (K := K) p p' R 1 = 1 := by
  simp [familyScalingValue, familyScalingSummand]

variable {p p'} (h : IsOrthogonalIdempotentPairs p p')
include h

omit [Fintype I] in
theorem IsOrthogonalIdempotentPairs.summand_mul_of_ne (t s : I → Rˣ) {k l : I} (hkl : k ≠ l) :
    familyScalingSummand (K := K) p p' R t k * familyScalingSummand (K := K) p p' R s l = 0 := by
  simp only [familyScalingSummand, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, h.left_left, h.left_right, h.right_left,
    h.right_right, hkl, ite_false, TensorProduct.tmul_zero, smul_zero, add_zero]

omit [Fintype I] in
theorem IsOrthogonalIdempotentPairs.summand_mul (t s : I → Rˣ) (k : I) :
    familyScalingSummand (K := K) p p' R (t * s) k =
      familyScalingSummand (K := K) p p' R t k + familyScalingSummand (K := K) p p' R s k +
        familyScalingSummand (K := K) p p' R t k * familyScalingSummand (K := K) p p' R s k := by
  simp only [familyScalingSummand, Pi.mul_apply, mul_inv_rev, Units.val_mul, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    h.left_left, h.left_right, h.right_left, h.right_right, ite_true, TensorProduct.tmul_zero,
    smul_zero, add_zero, zero_add]
  module

/-- Orthogonal idempotent pairs give the multiplicative law on every coefficient algebra. -/
theorem IsOrthogonalIdempotentPairs.familyScalingValue_mul (t s : I → Rˣ) :
    familyScalingValue (K := K) p p' R (t * s) =
      familyScalingValue (K := K) p p' R t * familyScalingValue (K := K) p p' R s := by
  have hcross : (∑ k, familyScalingSummand (K := K) p p' R t k) *
      (∑ l, familyScalingSummand (K := K) p p' R s l) =
      ∑ k, familyScalingSummand (K := K) p p' R t k *
        familyScalingSummand (K := K) p p' R s k := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Finset.sum_eq_single k (fun l _ hlk => h.summand_mul_of_ne R t s (Ne.symm hlk))
      (fun hk => absurd (Finset.mem_univ k) hk)
  simp only [familyScalingValue, h.summand_mul R t s, Finset.sum_add_distrib, add_mul, mul_add,
    one_mul, mul_one, hcross]
  abel

/-- The coefficient-algebra unit homomorphism scaling each `pₖ` by `tₖ` and `p'ₖ` by `tₖ⁻¹`. -/
def IsOrthogonalIdempotentPairs.scalingUnits : (I → Rˣ) →* (R ⊗[K] A)ˣ where
  toFun t :=
    { val := familyScalingValue (K := K) p p' R t
      inv := familyScalingValue (K := K) p p' R t⁻¹
      val_inv := by rw [← h.familyScalingValue_mul R, mul_inv_cancel, familyScalingValue_one]
      inv_val := by rw [← h.familyScalingValue_mul R, inv_mul_cancel, familyScalingValue_one] }
  map_one' := Units.ext (familyScalingValue_one p p' R)
  map_mul' t s := Units.ext (h.familyScalingValue_mul R t s)

@[simp] theorem IsOrthogonalIdempotentPairs.scalingUnits_val (t : I → Rˣ) :
    ((h.scalingUnits R t : (R ⊗[K] A)ˣ) : R ⊗[K] A) =
      familyScalingValue (K := K) p p' R t := rfl

/-- Multiplying by `pⱼ` extracts the `j`-th parameter: `pⱼ · v(t) = tⱼ ⊗ pⱼ`. -/
theorem IsOrthogonalIdempotentPairs.tmul_mul_familyScalingValue (t : I → Rˣ) (j : I) :
    ((1 : R) ⊗ₜ[K] p j) * familyScalingValue (K := K) p p' R t = (t j : R) ⊗ₜ[K] p j := by
  simp only [familyScalingValue, familyScalingSummand, mul_add, mul_one, Finset.mul_sum,
    mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, h.left_left, h.left_right,
    TensorProduct.tmul_zero, smul_zero, add_zero, TensorProduct.tmul_ite, smul_ite,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [show (t j : R) ⊗ₜ[K] p j = (t j : R) • ((1 : R) ⊗ₜ[K] p j) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  module

omit [Fintype I] [DecidableEq I] h in
/-- Extension of scalars from a field does not kill a nonzero vector. -/
theorem eq_zero_of_tmul_eq_zero {r : R} {a : A} (ha : a ≠ 0) (hr : r ⊗ₜ[K] a = 0) : r = 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K ha
  have h1 := congrArg ((TensorProduct.rid K R).toLinearMap ∘ₗ LinearMap.lTensor R φ) hr
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at h1
  have h2 := congrArg (fun z : R => (φ a)⁻¹ • z) h1
  simpa only [smul_smul, inv_mul_cancel₀ hφ, one_smul, smul_zero] using h2

theorem IsOrthogonalIdempotentPairs.scalingUnits_injective (hp : ∀ k, p k ≠ 0) :
    Function.Injective (h.scalingUnits (K := K) R) := by
  intro t s hts
  funext j
  apply Units.ext
  have h1 := congrArg (fun u : (R ⊗[K] A)ˣ => ((1 : R) ⊗ₜ[K] p j) * (u : R ⊗[K] A)) hts
  simp only [h.scalingUnits_val R, h.tmul_mul_familyScalingValue R] at h1
  have h2 : ((t j : R) - (s j : R)) ⊗ₜ[K] p j = 0 := by
    rw [TensorProduct.sub_tmul, h1, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_tmul_eq_zero (K := K) R (hp j) h2)

variable {R} in
/-- This unit construction commutes with every coefficient-algebra homomorphism. -/
theorem IsOrthogonalIdempotentPairs.scalingUnits_map {S : Type u} [CommRing S] [Algebra K S]
    (φ : R →ₐ[K] S) (t : I → Rˣ) :
    Units.map (Algebra.TensorProduct.map φ (AlgHom.id K A)).toMonoidHom
        (h.scalingUnits R t) =
      h.scalingUnits S (fun k => Units.map φ.toMonoidHom (t k)) := by
  apply Units.ext
  change Algebra.TensorProduct.map φ (AlgHom.id K A) (familyScalingValue (K := K) p p' R t) =
    familyScalingValue (K := K) p p' S _
  simp [familyScalingValue, familyScalingSummand_eq, map_sum]

end FamilyScaling

end FiniteAlgebraUnits

namespace Quaternionic

/-! ### Defects of scaling elements -/

namespace IsometryCut

open FiniteAlgebraUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A] (τ : FirstKindInvolution K A) (Q : A)
  (M : Submodule K A)

/-- Let `p, p'` be such that `p Q + Q τp - p Q τp' - p' Q τp`, its analogue with `p, p'`
exchanged, `p Q τp` and `p' Q τp'` lie in `M`. Then `1 + (t - 1) p + (t⁻¹ - 1) p'` has defect in
`R ⊗ M` for every unit `t` of every coefficient algebra `R`. -/
theorem defect_idempotentScalingValue_mem {p p' : A}
    (h1 : p * Q + Q * τ p - p * Q * τ p' - p' * Q * τ p ∈ M)
    (h2 : p' * Q + Q * τ p' - p' * Q * τ p - p * Q * τ p' ∈ M)
    (h3 : p * Q * τ p ∈ M) (h4 : p' * Q * τ p' ∈ M)
    (R : Type u) [CommRing R] [Algebra K R] (t : Rˣ) :
    defect τ Q (idempotentScalingValue (K := K) p p' R t) ∈ M.baseChange R := by
  set a : R := (t : R) - 1 with ha
  set b : R := ((t⁻¹ : Rˣ) : R) - 1 with hb
  have hab : a * b = -(a + b) := by
    have ht : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
    rw [ha, hb]
    linear_combination ht
  let incl := (Algebra.TensorProduct.includeRight : A →ₐ[K] R ⊗[K] A)
  have hincl : ∀ z : A, (1 : R) ⊗ₜ[K] z = incl z := fun z => rfl
  have key : defect τ Q (idempotentScalingValue (K := K) p p' R t) =
      a • incl (p * Q + Q * τ p - p * Q * τ p' - p' * Q * τ p) +
        b • incl (p' * Q + Q * τ p' - p' * Q * τ p - p * Q * τ p') +
        (a * a) • incl (p * Q * τ p) + (b * b) • incl (p' * Q * τ p') := by
    simp only [defect, idempotentScalingValue, map_add, FirstKindInvolution.map_one, map_smul,
      FirstKindInvolution.baseChange_tmul]
    simp only [hincl, map_add, map_sub, map_mul]
    rw [← ha, ← hb]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    linear_combination (norm := module)
      hab • (incl p * incl Q * incl (τ p') + incl p' * incl Q * incl (τ p))
  rw [key]
  have hm : ∀ z ∈ M, incl z ∈ M.baseChange R := fun z hz =>
    Submodule.tmul_mem_baseChange_of_mem 1 hz
  exact add_mem (add_mem (add_mem (Submodule.smul_mem _ a (hm _ h1))
    (Submodule.smul_mem _ b (hm _ h2))) (Submodule.smul_mem _ _ (hm _ h3)))
    (Submodule.smul_mem _ _ (hm _ h4))

variable {τ Q M}

/-- If each single scaling `1 + (tₖ - 1) pₖ + (tₖ⁻¹ - 1) p'ₖ` has defect in `R ⊗ M` and `R ⊗ M`
is stable, so does the scaling of the whole orthogonal family. -/
theorem defect_familyScalingValue_mem (hM : IsStable τ M) {I : Type*} [Fintype I]
    [DecidableEq I] {p p' : I → A} (h : IsOrthogonalIdempotentPairs p p')
    (R : Type u) [CommRing R] [Algebra K R] (t : I → Rˣ)
    (hX : ∀ k, defect τ Q (1 + familyScalingSummand (K := K) p p' R t k) ∈ M.baseChange R) :
    defect τ Q (familyScalingValue (K := K) p p' R t) ∈ M.baseChange R := by
  have hs : ∀ s : Finset I,
      defect τ Q (1 + ∑ k ∈ s, familyScalingSummand (K := K) p p' R t k) ∈ M.baseChange R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, add_zero, defect_one]
      exact zero_mem _
    | @insert j s hj ih =>
      have heq : 1 + ∑ k ∈ insert j s, familyScalingSummand (K := K) p p' R t k =
          (1 + familyScalingSummand (K := K) p p' R t j) *
            (1 + ∑ k ∈ s, familyScalingSummand (K := K) p p' R t k) := by
        rw [Finset.sum_insert hj, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum,
          Finset.sum_eq_zero (fun k hk => h.summand_mul_of_ne R t t
            (ne_of_mem_of_not_mem hk hj).symm), add_zero]
        abel
      rw [heq, defect_mul]
      exact add_mem (hM R _ _ ih) (hX j)
  exact hs Finset.univ

end IsometryCut

/-! ### The split torus of a hyperbolic family -/

namespace FirstKindInvolution

open FiniteAlgebraUnits

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {σ : FirstKindInvolution K D} {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {I : Type u} [Fintype I] [DecidableEq I] {x y : I → n → D}

namespace IsHyperbolicFamily

variable (h : σ.IsHyperbolicFamily q x y)
include h

omit [FiniteDimensional K D] [Fintype I] in
/-- The line matrices `Pₖ = (z ↦ h(z, yₖ) xₖ)` and `P'ₖ = (z ↦ h(z, xₖ) yₖ)` of a hyperbolic
family form a family of orthogonal idempotent pairs. -/
theorem isOrthogonalIdempotentPairs :
    IsOrthogonalIdempotentPairs (fun k => σ.hyperbolicLineMatrix q (x k) (y k))
      (fun k => σ.hyperbolicLineMatrix q (y k) (x k)) :=
  ⟨h.lineMatrix_mul_left_left, h.lineMatrix_mul_left_right, h.lineMatrix_mul_right_left,
    h.lineMatrix_mul_right_right⟩

omit [FiniteDimensional K D] in
/-- Over every coefficient algebra, the scaling of a hyperbolic family is an isometry of `q`. -/
theorem defect_familyScalingValue_mem (R : Type u) [CommRing R] [Algebra K R] (t : I → Rˣ) :
    IsometryCut.defect (σ.matrix n) (Quotient.out q)
        (familyScalingValue (K := K) (fun k => σ.hyperbolicLineMatrix q (x k) (y k))
          (fun k => σ.hyperbolicLineMatrix q (y k) (x k)) R t) ∈
      (σ.quadraticKernel n).baseChange R := by
  refine IsometryCut.defect_familyScalingValue_mem IsometryCut.isStable_alternatingSubspace
    h.isOrthogonalIdempotentPairs R t fun k => ?_
  have hQ : (Submodule.Quotient.mk (Quotient.out q) : σ.QuadraticForms n) = q :=
    Submodule.Quotient.mk_out q
  have hk := h.isHyperbolicPair k
  rw [familyScalingSummand, ← add_assoc]
  exact IsometryCut.defect_idempotentScalingValue_mem (σ.matrix n) _ _
    (hk.lineMatrix_polar_mem _ hQ) (hk.symm.lineMatrix_polar_mem _ hQ)
    (hk.lineMatrix_congr_mem _ hQ) (hk.symm.lineMatrix_congr_mem _ hQ) R (t k)

local notation "𝕊" => splitTorus (Spec (CommRingCat.of K)) I
local notation "𝕌" => FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))

/-- The scaling of the hyperbolic family on actual points of the matrix unit group. -/
def unitTorusPoints (T : Over (Spec (CommRingCat.of K))) : (T ⟶ (𝕊).X) →* (T ⟶ (𝕌).X) :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T).symm.toMonoidHom.comp
    ((h.isOrthogonalIdempotentPairs.scalingUnits ((algΓ (CommRingCat.of K)).obj T).unop).comp
      (splitTorus.pointsEquiv I T).toMonoidHom)

theorem pointsEquiv_unitTorusPoints (T : Over (Spec (CommRingCat.of K))) (z : T ⟶ (𝕊).X) :
    FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T (h.unitTorusPoints T z) =
      h.isOrthogonalIdempotentPairs.scalingUnits ((algΓ (CommRingCat.of K)).obj T).unop
        (splitTorus.pointsEquiv I T z) :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T).apply_symm_apply _

theorem unitTorusPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (z : T ⟶ (𝕊).X) :
    h.unitTorusPoints T' (a ≫ z) = a ≫ h.unitTorusPoints T z := by
  apply (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T').injective
  rw [FiniteAlgebraUnits.pointsEquiv_naturality, pointsEquiv_unitTorusPoints,
    pointsEquiv_unitTorusPoints, splitTorus.pointsEquiv_naturality]
  exact (h.isOrthogonalIdempotentPairs.scalingUnits_map
    (((algΓ (CommRingCat.of K)).map a).unop.hom) _).symm

/-- The split torus `𝔾ₘ^I` of the matrix unit group scaling each `xₖ` by `tₖ` and each `yₖ`
by `tₖ⁻¹`, fixing the orthogonal complement of the hyperbolic family. -/
def unitTorus : 𝕊 ⟶ 𝕌 :=
  homOfPoints h.unitTorusPoints h.unitTorusPoints_naturality

theorem pointsEquiv_unitTorus {T : Over (Spec (CommRingCat.of K))} (z : T ⟶ (𝕊).X) :
    FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T
        (z ≫ h.unitTorus.hom.hom) =
      h.isOrthogonalIdempotentPairs.scalingUnits ((algΓ (CommRingCat.of K)).obj T).unop
        (splitTorus.pointsEquiv I T z) := by
  rw [unitTorus, comp_homOfPoints, pointsEquiv_unitTorusPoints]

instance mono_unitTorus : Mono h.unitTorus.hom.hom := by
  constructor
  intro Z g g' hgg
  apply (splitTorus.pointsEquiv I Z).injective
  have h1 := congrArg (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) Z) hgg
  rw [pointsEquiv_unitTorus, pointsEquiv_unitTorus] at h1
  exact h.isOrthogonalIdempotentPairs.scalingUnits_injective
    ((algΓ (CommRingCat.of K)).obj Z).unop h.lineMatrix_ne_zero h1

/-- The scaling torus of a hyperbolic family factors through the isometry group `O(q)`. -/
theorem exists_isometryTorus :
    ∃ f : 𝕊 ⟶ σ.isometryGroup q, f ≫ σ.isometryGroupι q = h.unitTorus := by
  let j := (σ.isometryGroupι q).hom.hom
  have : IsClosedImmersion j.left := σ.isClosedSubgroup_isometryGroupι q
  have : Mono j.left := ((IsClosedImmersion.iff_isFinite_and_mono _).mp this).2
  have : Mono j := Over.mono_of_mono_left _
  have hmem : 𝟙 (𝕊).X ≫ h.unitTorus.hom.hom ∈
      (SubgroupFunctor.range (σ.isometryGroupι q)).carrier (𝕊).X := by
    rw [σ.mem_range_isometryGroupι_iff q (Quotient.out q) (Submodule.Quotient.mk_out q),
      pointsEquiv_unitTorus]
    exact h.defect_familyScalingValue_mem _ _
  obtain ⟨l, hl⟩ := SubgroupFunctor.mem_range.mp hmem
  rw [Category.id_comp] at hl
  have : IsMonHom l :=
    { one_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.mul_hom, Category.assoc,
          IsMonHom.mul_hom, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, hl] }
  exact ⟨Grp.homMk l, Grp.hom_ext _ _ hl⟩

/-- The scaling torus of a hyperbolic family, as a homomorphism into `O(q)`. -/
def isometryTorus : 𝕊 ⟶ σ.isometryGroup q :=
  Classical.choose h.exists_isometryTorus

@[reassoc (attr := simp)] theorem isometryTorus_comp :
    h.isometryTorus ≫ σ.isometryGroupι q = h.unitTorus :=
  Classical.choose_spec h.exists_isometryTorus

variable [Smooth (σ.isometryGroup q).X.hom]

/-- The scaling torus of a hyperbolic family lands in the identity component `O(q)⁰`. -/
def connectedTorus : 𝕊 ⟶ σ.connectedIsometryGroup q := by
  have : ConnectedSpace (𝕊).X.left :=
    IsSplitTorus.connectedSpace (isSplitTorus_splitTorus (S := Spec (CommRingCat.of K)) I)
  exact IdentityComponent.factor (σ.isometryGroup q) h.isometryTorus

@[reassoc (attr := simp)] theorem connectedTorus_comp :
    h.connectedTorus ≫ identityComponentι (σ.isometryGroup q) ≫ σ.isometryGroupι q =
      h.unitTorus := by
  rw [connectedTorus, IdentityComponent.factor_identityComponentι_assoc, h.isometryTorus_comp]

instance mono_connectedTorus : Mono h.connectedTorus.hom.hom := by
  have hm : Mono (h.connectedTorus ≫ identityComponentι (σ.isometryGroup q) ≫
      σ.isometryGroupι q).hom.hom := by
    rw [h.connectedTorus_comp]
    infer_instance
  change Mono (h.connectedTorus.hom.hom ≫
    (identityComponentι (σ.isometryGroup q) ≫ σ.isometryGroupι q).hom.hom) at hm
  exact mono_of_mono _ (identityComponentι (σ.isometryGroup q) ≫ σ.isometryGroupι q).hom.hom

/-- The scaling torus of a hyperbolic family is a closed split subtorus of `O(q)⁰`. -/
theorem isClosedSubgroup_connectedTorus : IsClosedSubgroup h.connectedTorus := by
  have := isAffineHom_splitTorus (Spec (CommRingCat.of K)) I
  exact IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (isSplitTorus_splitTorus _)) _

/-- A hyperbolic family indexed by `I` gives split rank at least `|I|` for `O(q)⁰`. -/
theorem card_le_splitRank_connectedIsometryGroup :
    (Nat.card I : ℕ∞) ≤ splitRank (σ.connectedIsometryGroup q) :=
  card_le_splitRank I h.connectedTorus h.isClosedSubgroup_connectedTorus

end IsHyperbolicFamily

/-- **Lower bound.** For a nondegenerate `q`, the split rank of `O(q)⁰` is at least the Witt
index of `q`. -/
theorem quadraticWittIndex_le_splitRank_connectedIsometryGroup (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom] (hq : σ.IsNondegenerateQuadratic q) :
    (σ.quadraticWittIndex q : ℕ∞) ≤ splitRank (σ.connectedIsometryGroup q) := by
  obtain ⟨x, y, h⟩ := exists_isHyperbolicFamily q hq
  have h' := (h.comp (fun k : ULift.{u} (Fin (σ.quadraticWittIndex q)) => k.down)
    ULift.down_injective).card_le_splitRank_connectedIsometryGroup
  simpa using h'

end FirstKindInvolution

end Quaternionic

end Langlands.GroupScheme
