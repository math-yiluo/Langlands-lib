import Langlands.GroupScheme.CliffordSpin.CentralIsogeny
import Langlands.GroupScheme.CliffordSpin.ReflectionCoordinates
import Langlands.GroupScheme.Rational.NumberFieldScalarSpinHasseReduction

/-! # The scalar Clifford Kummer boundary is the spinor norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic GaloisPoint Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000
set_option synthInstance.maxHeartbeats 100000

@[reducible] local instance invertibleTwo (F : Type u) [Field F] [CharZero F] : Invertible (2 : F) :=
  invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)

variable {F : Type u} [Field F] [CharZero F] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "P" => groupScheme Q b
local notation "π" => projection q
local notation "C[" A "]" => A ⊗[F] CliffordAlgebra Q

private abbrev Pair (A : Type u) [CommRing A] [Algebra F A] := (C[A])ˣ × GL (Fin n) A

private def pairMap {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) : Pair q A →* Pair q B :=
  (Units.map (tensorMap Q f).toMonoidHom).prodMap (Matrix.GeneralLinearGroup.map f.toRingHom)

private def pairScale (A : Type u) [CommRing A] [Algebra F A] : Aˣ →* Pair q A :=
  (Units.map (algebraMap A (C[A]))).prod (1 : Aˣ →* GL (Fin n) A)

omit [CharZero F] [NeZero n] in
private theorem pairMap_scale {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) (a : Aˣ) :
    pairMap q f (pairScale q A a) = pairScale q B (Units.map f.toMonoidHom a) := by
  apply Prod.ext
  · apply Units.ext
    change tensorMap Q f (algebraMap A (C[A]) (a : A)) = algebraMap B (C[B]) (f (a : A))
    simp [Algebra.TensorProduct.algebraMap_apply]
  · exact map_one (Matrix.GeneralLinearGroup.map f.toRingHom)

omit [CharZero F] [NeZero n] in
private theorem pairScale_val (A : Type u) [CommRing A] [Algebra F A] (a : Aˣ) (p : Pair q A) :
    (((pairScale q A a * p).1 : (C[A])ˣ) : C[A]) = (a : A) • (p.1 : C[A]) :=
  (Algebra.smul_def (a : A) (p.1 : C[A])).symm

omit [CharZero F] [NeZero n] in
private theorem pairScale_matrix (A : Type u) [CommRing A] [Algebra F A] (a : Aˣ) (p : Pair q A) :
    (pairScale q A a * p).2 = p.2 := one_mul _

private abbrev ambient := Corepresented.groupScheme (ambientFunctor (n := n) Q) (ambientCorepresentation Q b)

private instance ambient_isAffine : IsAffine (ambient q).X.left := by
  change IsAffine (Spec (CommRingCat.of (ambientAlgebra Q b)))
  infer_instance

private def ambientPairs (A : Type u) [CommRing A] [Algebra F A] :
    (ambient q).affinePoints (CommAlgCat.of F A) ≃* Pair q A :=
  Corepresented.affinePointsEquiv (ambientFunctor (n := n) Q) (ambientCorepresentation Q b) _

omit [NeZero n] in
set_option maxHeartbeats 1800000 in
private theorem ambientPairs_naturality {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) (x : (ambient q).affinePoints (CommAlgCat.of F A)) :
    ambientPairs q B (GroupScheme.affinePointMap (ambient q) (CommAlgCat.ofHom f) x) =
      pairMap q f (ambientPairs q A x) := by
  let functor := ambientFunctor (n := n) Q
  let corep := ambientCorepresentation Q b
  exact Corepresented.affinePointsEquiv_naturality functor corep (CommAlgCat.ofHom f) x

private def spinPairs (A : Type u) [CommRing A] [Algebra F A] :
    (P).affinePoints (CommAlgCat.of F A) →* Pair q A :=
  (coefficientSubgroup Q b A).subtype.comp (affinePairEquiv Q b (CommAlgCat.of F A)).toMonoidHom

omit [NeZero n] in
private theorem spinPairs_injective (A : Type u) [CommRing A] [Algebra F A] :
    Function.Injective (spinPairs q A) := Subtype.val_injective.comp (affinePairEquiv Q b _).injective

omit [NeZero n] in
private theorem spinPairs_naturality {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) (x : (P).affinePoints (CommAlgCat.of F A)) :
    spinPairs q B (GroupScheme.affinePointMap (P) (CommAlgCat.ofHom f) x) =
      pairMap q f (spinPairs q A x) :=
  affinePairEquiv_naturality Q b (CommAlgCat.ofHom f) x

private theorem spinPairs_kernel (hq : (τ).IsNondegenerateQuadratic q)
    (A : Type u) [Field A] [Algebra F A] (t : rootsOfUnity 2 A) :
    spinPairs q A ((isCentralIsogeny_projection q hq).kernelPointInclusion A
      (((isCentralIsogeny_projection q hq).kernelRootsEquiv 2 (kernelIso q hq) A).symm t)) =
      pairScale q A (t : Aˣ) := by
  let x := (mu.affinePointsEquiv 2 (Spec.algebraMap F A)).symm t
  change (affinePairEquiv Q b (CommAlgCat.of F A)
      ((x ≫ (kernelIso q hq).inv.hom.hom) ≫ (kernelι (π)).hom.hom)).val = _
  rw [affinePair_kernelIso_inv q hq (CommAlgCat.of F A)]
  change (scalarPair Q A (mu.affinePointsEquiv 2 (Spec.algebraMap F A) x)).val = _
  rw [show mu.affinePointsEquiv 2 (Spec.algebraMap F A) x = t from MulEquiv.apply_symm_apply _ _, scalarPair_val]
  rfl

variable {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
  [IsScalarTower F K M]

private abbrev extendCoeff := IsScalarTower.toAlgHom F K M
private abbrev conjugateCoeff (σ : M ≃ₐ[K] M) := (σ.restrictScalars F).toAlgHom

omit [CharZero F] [NeZero n] in
private theorem pairScale_fixed_iff (z : Mˣ) (x : Pair q M) (σ : M ≃ₐ[K] M) :
    pairMap q (conjugateCoeff σ) (pairScale q M z * x) = pairScale q M z * x ↔
      pairScale q M (KummerCocycle.value z σ) = x * (pairMap q (conjugateCoeff σ) x)⁻¹ := by
  have h : Units.map (conjugateCoeff (F := F) σ).toMonoidHom z =
      z * KummerCocycle.value z σ := by
    change σ • z = z * (σ • z / z)
    rw [mul_comm, div_mul_cancel]
  rw [map_mul, pairMap_scale, h, map_mul, mul_assoc, eq_mul_inv_iff_mul_eq]
  exact mul_right_inj _

omit [NeZero n] in
private theorem pair_fixed_of_extend (p : Pair q K) (σ : M ≃ₐ[K] M) :
    pairMap q (conjugateCoeff σ) (pairMap q (extendCoeff (F := F) (K := K) (M := M)) p) =
      pairMap q (extendCoeff (F := F) (K := K) (M := M)) p := by
  let x := (ambientPairs q K).symm p
  have hx : ambientPairs q K x = p := MulEquiv.apply_symm_apply _ _
  have h := congrArg (ambientPairs q M) (relativeConjugate_extend F K M (ambient q) σ x)
  change ambientPairs q M (GroupScheme.affinePointMap (ambient q) (CommAlgCat.ofHom (conjugateCoeff σ))
    (GroupScheme.affinePointMap (ambient q) (CommAlgCat.ofHom (extendCoeff (F := F) (K := K) (M := M))) x)) =
    ambientPairs q M (GroupScheme.affinePointMap (ambient q)
      (CommAlgCat.ofHom (extendCoeff (F := F) (K := K) (M := M))) x) at h
  rw [ambientPairs_naturality q (conjugateCoeff σ),
    ambientPairs_naturality q (extendCoeff (F := F) (K := K) (M := M)), hx] at h
  exact h

omit [NeZero n] in
private theorem exists_pair_of_fixed [FiniteDimensional K M] [IsGalois K M]
    (p : Pair q M) (hp : ∀ σ : M ≃ₐ[K] M, pairMap q (conjugateCoeff σ) p = p) :
    ∃ y : Pair q K, pairMap q (extendCoeff (F := F) (K := K) (M := M)) y = p := by
  let x := (ambientPairs q M).symm p
  have hx : ambientPairs q M x = p := MulEquiv.apply_symm_apply _ _
  let w : relativeFixedSubgroup F K M (ambient q) := ⟨x, fun σ => by
    apply (ambientPairs q M).injective
    change ambientPairs q M (GroupScheme.affinePointMap (ambient q)
      (CommAlgCat.ofHom (conjugateCoeff σ)) x) = ambientPairs q M x
    rw [ambientPairs_naturality, hx, hp σ]⟩
  let y := relativeDescend F K M (ambient q) w
  refine ⟨ambientPairs q K y, ?_⟩
  rw [← ambientPairs_naturality]
  change ambientPairs q M (relativeExtend F K M (ambient q) y) = p
  rw [relativeExtend_descend, show w.val = x from rfl, hx]

omit [NeZero n] in
private theorem tensorMap_extend_injective : Function.Injective
    (tensorMap Q (extendCoeff (F := F) (K := K) (M := M))) := by
  change Function.Injective (TensorProduct.map
    (extendCoeff (F := F) (K := K) (M := M)).toLinearMap (LinearMap.id (R := F) (M := CliffordAlgebra Q)))
  exact TensorProduct.map_injective_of_flat_flat _ _ (algebraMap K M).injective Function.injective_id

omit [NeZero n] in
private theorem reversionNorm_spinPair {A : Type u} [CommRing A] [Algebra F A]
    (x : (P).affinePoints (CommAlgCat.of F A)) : reversionNorm Q ((spinPairs q A x).1 : C[A]) = 1 :=
  sub_eq_zero.mp ((mem_coefficientSubgroup_iff Q b _ _).mp (affinePairEquiv Q b _ x).property).2.1

/-- Kummer coboundaries in the scalar Clifford lift group are precisely the spinor-norm
classes, computed from even reflection words over the intermediate coefficient field. -/
theorem scalarSpinorNormBoundary_projection (hq : (τ).IsNondegenerateQuadratic q) :
    ScalarSpinorNormBoundary (isCentralIsogeny_projection q hq) (kernelIso q hq) Q := by
  intro K M _ _ _ _ _ _ _ _ a z hz
  let R := CommAlgCat.of F M
  let f : K →ₐ[F] M := extendCoeff
  have hi : Function.Injective (tensorMap Q f) := tensorMap_extend_injective q
  have hz' : (z : M) ^ 2 = algebraMap K M (a : K) := congrArg Units.val hz
  constructor
  · rintro ⟨x, hx⟩
    let p := spinPairs q M x
    have hfix (σ : M ≃ₐ[K] M) :
        pairMap q (conjugateCoeff σ) (pairScale q M z * p) = pairScale q M z * p := by
      apply (pairScale_fixed_iff q z p σ).mpr
      have h := congrArg (spinPairs q M) (hx σ)
      rw [spinPairs_kernel q hq, map_mul, map_inv] at h
      change _ = p * (spinPairs q M (GroupScheme.affinePointMap (P)
        (CommAlgCat.ofHom (conjugateCoeff σ)) x))⁻¹ at h
      rw [spinPairs_naturality] at h
      exact h
    obtain ⟨y, hy⟩ := exists_pair_of_fixed q (pairScale q M z * p) hfix
    change pairMap q f y = _ at hy
    have hu : tensorMap Q f (y.1 : C[K]) = (z : M) • (p.1 : C[M]) :=
      (congrArg (fun z : Pair q M => (z.1 : C[M])) hy).trans (pairScale_val q M z p)
    have hg : Matrix.GeneralLinearGroup.map f.toRingHom y.2 = p.2 :=
      (congrArg Prod.snd hy).trans (pairScale_matrix q M z p)
    have hp : p ∈ coefficientSubgroup Q b M := (affinePairEquiv Q b R x).property
    obtain ⟨hgrade, _, hdet, hact⟩ := (mem_coefficientSubgroup_iff Q b p.1 p.2).mp hp
    refine exists_even_reflectionWord_of_pair Q b (nondegenerate_polar_baseChange q hq K)
      y.1 y.2 (a : K) (hi ?_) (hi ?_) ?_ (fun i => hi ?_)
    · rw [tensorMap_gradeDefect, hu, gradeDefect_smul, hgrade, smul_zero, map_zero]
    · rw [tensorMap_reversionNorm, hu, reversionNorm_smul, reversionNorm_spinPair q x,
        hz', ← Algebra.algebraMap_eq_smul_one]
      simp [Algebra.TensorProduct.algebraMap_apply, f]
    · have hm := Matrix.GeneralLinearGroup.map_det f.toRingHom y.2
      rw [hg, hdet, ← map_one (Units.map f.toRingHom.toMonoidHom)] at hm
      exact Units.map_injective (f := f.toRingHom.toMonoidHom) f.toRingHom.injective hm.symm
    · rw [tensorMap_actionDefect, hu, hg, actionDefect_smul, hact i, smul_zero, map_zero]
  · rintro ⟨l, t, hl, ht, hv⟩
    obtain ⟨u, g, hgrade, hnorm, hdet, hact⟩ := exists_pair_of_even_reflectionWord Q b l hl
    let y : Pair q K := (u, g)
    let w := pairMap q f y
    let t₀ := Units.mk0 t ht
    let r := z * Units.map (algebraMap K M) t₀
    let p := pairScale q M r⁻¹ * w
    have hR : (r : M) ^ 2 = f (reflectionWordValue ((Q).baseChange K) l) := by
      change ((z : M) * algebraMap K M t) ^ 2 = algebraMap K M _
      rw [mul_pow, hz', hv, map_mul, map_pow]
    have hN : reversionNorm Q (w.1 : C[M]) = algebraMap M (C[M]) ((r : M) ^ 2) := by
      change reversionNorm Q (tensorMap Q f (u : C[K])) = _
      rw [← tensorMap_reversionNorm, hnorm, hR]
      simp [Algebra.TensorProduct.algebraMap_apply]
    have hp : p ∈ coefficientSubgroup Q b M := by
      apply (mem_coefficientSubgroup_iff Q b p.1 p.2).mpr
      rw [show (p.1 : C[M]) = ((r⁻¹ : Mˣ) : M) • (w.1 : C[M]) from pairScale_val q M _ _,
        show p.2 = w.2 from pairScale_matrix q M _ _]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [gradeDefect_smul]
        change ((r⁻¹ : Mˣ) : M) • gradeDefect Q M (tensorMap Q f (u : C[K])) = 0
        rw [← tensorMap_gradeDefect, hgrade, map_zero, smul_zero]
      · rw [← reversionNorm_sub_one, reversionNorm_smul, hN,
          Algebra.algebraMap_eq_smul_one, smul_smul, ← mul_pow, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_pow, one_smul, sub_self]
      · change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) = 1
        rw [Matrix.GeneralLinearGroup.map_det, hdet, map_one]
      · intro i
        rw [actionDefect_smul]
        change ((r⁻¹ : Mˣ) : M) • actionDefect Q b M (tensorMap Q f (u : C[K]))
          (Matrix.GeneralLinearGroup.map f.toRingHom g) i = 0
        rw [← tensorMap_actionDefect, hact i, map_zero, smul_zero]
    have hw : pairScale q M z * p = pairMap q f (pairScale q K t₀⁻¹ * y) := by
      rw [map_mul, pairMap_scale]
      change pairScale q M z * (pairScale q M r⁻¹ * w) =
        pairScale q M (Units.map f.toMonoidHom t₀⁻¹) * w
      have hunit : z * r⁻¹ = Units.map f.toMonoidHom t₀⁻¹ := by
        change z * (z * Units.map f.toMonoidHom t₀)⁻¹ = Units.map f.toMonoidHom t₀⁻¹
        rw [map_inv, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
      rw [← mul_assoc, ← map_mul, hunit]
    let x := (affinePairEquiv Q b R).symm ⟨p, hp⟩
    have hx : spinPairs q M x = p := congrArg Subtype.val (MulEquiv.apply_symm_apply _ _)
    refine ⟨x, fun σ => (spinPairs_injective q M) ?_⟩
    rw [spinPairs_kernel q hq, map_mul, map_inv, hx]
    change _ = p * (spinPairs q M (GroupScheme.affinePointMap (P)
      (CommAlgCat.ofHom (conjugateCoeff σ)) x))⁻¹
    rw [spinPairs_naturality, hx]
    apply (pairScale_fixed_iff q z p σ).mp
    rw [hw]
    exact pair_fixed_of_extend q _ σ

/-- The actual scalar Clifford lift group of a regular form of dimension at least four
has trivial Hasse kernel for cocycles on every finite Galois cover of a number field. -/
def ScalarCliffordSpinGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q → 4 ≤ n →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle (groupScheme ((FirstKindInvolution.scalar F).polar q).toQuadraticForm'
        (Pi.basisFun F (Fin n))) (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The actual Kummer-boundary calculation discharges the scalar spin Hasse reduction. -/
theorem scalarCliffordSpinGaloisHasseKernel : ScalarCliffordSpinGaloisHasseKernelStatement.{u} := by
  intro F _ _ n _ q hq hn L _ _ _ _ ξ hξ
  exact isTrivial_scalarSpinCover_of_boundary q hq hn (isCentralIsogeny_projection q hq)
    (kernelIso q hq) (scalarSpinorNormBoundary_projection q hq) ξ hξ

end Langlands.GroupScheme.CliffordSpin
