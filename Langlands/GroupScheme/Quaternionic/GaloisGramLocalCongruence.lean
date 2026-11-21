import Langlands.GroupScheme.Quaternionic.GaloisGramDescent
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction

/-! # Local Gram congruence from triviality on the full completion pullback -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open GaloisPoint

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
  {n : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) D)

local notation "A" => Matrix (Fin n) (Fin n) D
local notation "U" => CentralSimpleUnits.groupScheme F A
local notation "G" => σ.symplecticGroup H
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" => FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)
local notation "τ" => σ.matrix (Fin n)
local notation "j" => σ.symplecticAmbientι H

/-- The two Gram matrices become congruent over the actual tensor algebra of coefficients. -/
def TensorGramCongruent (H' : A) (K : Type u) [Field K] [Algebra F K] : Prop :=
  ∃ P : (K ⊗[F] A)ˣ, ((τ).baseChange K).gramTransform P ((1 : K) ⊗ₜ[F] H) = (1 : K) ⊗ₜ[F] H'

section Relative

variable {R S : Type u} [Field R] [Field S] [Algebra F R] [Algebra F S]
  [Algebra R S] [IsScalarTower F R S]

omit [Algebra.IsCentral F D] [NeZero n] in
private theorem relative_tensorUnit (x : (U).affinePoints (Rₐ R)) :
    unitEquiv[S] (relativeExtend F R S U x) =
      Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F R S) (AlgHom.id F A)).toMonoidHom
        (unitEquiv[R] x) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom F R S)) x

end Relative

variable {L K : Type u} [Field L] [Algebra F L] [IsGalois F L] [Field K] [Algebra F K]
  {ξ : Cocycle (σ.symplecticGroup H) (GaloisCocycle.cover F L)}
  (d : SymplecticGramDescent (L := L) σ H ξ)

section ComparisonField

variable (M : Type u) [Field M] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [FiniteDimensional K M] [IsGalois K M]

private theorem exists_relative_primitive_correction
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ (r : (U).affinePoints (Rₐ K)) (y : (G).affinePoints (Rₐ M)),
      relativeExtend F K M U r =
        ((G).affinePointsTarget j (Rₐ M) y)⁻¹ * relativeExtend F L M U (SymplecticGramDescent.primitive (L := L) d) := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) ξ h
  let B := relativeExtend F L M U (SymplecticGramDescent.primitive (L := L) d)
  let J := (G).affinePointsTarget j (Rₐ M)
  let Y := J y
  let act := relativeConjugate F K M U
  have hfix (s : M ≃ₐ[K] M) : act s (Y⁻¹ * B) = Y⁻¹ * B := by
    let s₀ := s.restrictScalars F
    let s₁ := s₀.restrictNormal L
    let c := GaloisCocycle.value ξ s₁
    have h₁ : J (relativeExtend F L M G c) =
        relativeExtend F L M U ((G).affinePointsTarget j (Rₐ L) c) := by
      change (GaloisCocycle.coverMap F L M ≫ c) ≫ (j).hom.hom =
        GaloisCocycle.coverMap F L M ≫ (c ≫ (j).hom.hom)
      exact Category.assoc _ _ _
    have h₂ : J (conjugate F M G s₀ y) = act s Y := by
      change (GaloisCocycle.arrow F M s₀ ≫ y) ≫ (j).hom.hom =
        GaloisCocycle.arrow F M s₀ ≫ (y ≫ (j).hom.hom)
      exact Category.assoc _ _ _
    have h₃ : relativeExtend F L M U (conjugate F L U s₁ (SymplecticGramDescent.primitive (L := L) d)) = act s B := by
      change GaloisCocycle.coverMap F L M ≫ GaloisCocycle.arrow F L s₁ ≫ (SymplecticGramDescent.primitive (L := L) d) =
        GaloisCocycle.arrow F M s₀ ≫ GaloisCocycle.coverMap F L M ≫ (SymplecticGramDescent.primitive (L := L) d)
      rw [← Category.assoc, ← Category.assoc, GaloisCocycle.arrow_coverMap]
    have he := congrArg J (hy s)
    change J (relativeExtend F L M G c) = J (y * (conjugate F M G s₀ y)⁻¹) at he
    rw [h₁, d.coboundary, _root_.map_mul, _root_.map_inv, h₃,
      _root_.map_mul, _root_.map_inv, h₂] at he
    rw [_root_.map_mul, _root_.map_inv]
    have he' := congrArg (fun x => Y⁻¹ * x * act s B) he
    change Y⁻¹ * (B * (act s B)⁻¹) * act s B =
      Y⁻¹ * (Y * (act s Y)⁻¹) * act s B at he'
    group at he'
    simpa only [_root_.zpow_neg_one] using he'.symm
  let z : relativeFixedSubgroup F K M U := ⟨Y⁻¹ * B, hfix⟩
  exact ⟨(relativeFixedEquiv F K M U).symm z, y, relativeExtend_descend F K M U z⟩

include M in
private theorem exists_tensor_gramTransform_of_comparisonField
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    σ.TensorGramCongruent H d.gram K := by
  obtain ⟨r, y, hr⟩ := exists_relative_primitive_correction σ H d M h
  let B := unitEquiv[M] (relativeExtend F L M U (SymplecticGramDescent.primitive (L := L) d))
  let Y := unitEquiv[M] ((G).affinePointsTarget j (Rₐ M) y)
  let P := (unitEquiv[K] r)⁻¹
  let k := IsScalarTower.toAlgHom F K M
  have hP : Units.map (Algebra.TensorProduct.map k (AlgHom.id F A)).toMonoidHom P = B⁻¹ * Y := by
    change Units.map (Algebra.TensorProduct.map k (AlgHom.id F A)).toMonoidHom
      ((unitEquiv[K] r)⁻¹) = _
    rw [_root_.map_inv, ← relative_tensorUnit r, hr, _root_.map_mul, _root_.map_inv]
    change (Y⁻¹ * B)⁻¹ = B⁻¹ * Y
    group
  have hy : ((τ).baseChange M).gramTransform Y ((1 : M) ⊗ₜ[F] H) = (1 : M) ⊗ₜ[F] H := by
    apply sub_eq_zero.mp
    apply (σ.mem_range_symplecticAmbientι_affine_iff H hσ hH hu (Rₐ M) _).mp
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have hB : ((τ).baseChange M).gramTransform B⁻¹ ((1 : M) ⊗ₜ[F] H) = (1 : M) ⊗ₜ[F] (SymplecticGramDescent.gram (L := L) d) := by
    let l := IsScalarTower.toAlgHom F L M
    have e := congrArg (Algebra.TensorProduct.map l (AlgHom.id F A)) d.tensor_gram
    rw [map_gramTransform τ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      _root_.map_one, AlgHom.id_apply, AlgHom.id_apply, _root_.map_inv,
      ← relative_tensorUnit (SymplecticGramDescent.primitive (L := L) d)] at e
    exact e
  refine ⟨P, ?_⟩
  have hinj : Function.Injective (Algebra.TensorProduct.map k (AlgHom.id F A)) :=
    TensorProduct.map_injective_of_flat_flat k.toLinearMap (LinearMap.id : A →ₗ[F] A)
      k.injective Function.injective_id
  apply hinj
  rw [map_gramTransform τ, hP, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    _root_.map_one, AlgHom.id_apply, AlgHom.id_apply, gramTransform_mul, hy, hB]

end ComparisonField

variable [FiniteDimensional F L] [CharZero K]

/-- A local primitive on the full base-changed cover gives Gram congruence over the new field. -/
theorem SymplecticGramDescent.exists_tensor_gramTransform_of_baseChange_isTrivial
    (hσ : Module.finrank F σ.symmetricSubspace =
      Langlands.CentralSimple.reducedDegree F D * (Langlands.CentralSimple.reducedDegree F D + 1) / 2)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    σ.TensorGramCongruent H d.gram K := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  exact exists_tensor_gramTransform_of_comparisonField σ H d M hσ hH hu h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
