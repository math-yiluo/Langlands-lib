import Langlands.GroupScheme.Rational.HermitianGaloisGramDescent
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction

/-! # Hermitian Gram congruence over a completion coefficient algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root Quaternionic Quaternionic.FirstKindInvolution GaloisPoint FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] {n : ℕ}

local instance : FiniteDimensional F E :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)

local notation "A" => Matrix (Fin n) (Fin n) E
local notation "τ" => FirstKindInvolution.matrix (quadraticConjugationInvolution F E) (Fin n)
local notation "σ" => quadraticConjugationInvolution F E
local notation "U" => ambientUnits F E n
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" => FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)

variable {G : GroupScheme (Spec (CommRingCat.of F))} {H : Form (fieldInvolution F E) (Fin n)}
  (p : SchemeModel.Presentation F E H G)
  {L K : Type u} [Field L] [Algebra F L] [IsGalois F L] [Field K] [Algebra F K]
  {ξ : Cocycle G (GaloisCocycle.cover F L)} (d : GaloisGramDescent p ξ)
  (M : Type u) [Field M] [Algebra F M] [Algebra K M] [Algebra L M]
  [IsScalarTower F K M] [IsScalarTower F L M] [FiniteDimensional K M] [IsGalois K M]

omit [Algebra.IsSeparable F E] in
private theorem relative_unitEquiv {B C : Type u} [Field B] [Field C] [Algebra F B] [Algebra F C]
    [Algebra B C] [IsScalarTower F B C] (b : (U).affinePoints (Rₐ B)) :
    (unitEquiv[C]) (relativeExtend F B C U b) =
      Units.map (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F B C) (AlgHom.id F A)).toMonoidHom
        ((unitEquiv[B]) b) :=
  FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom (IsScalarTower.toAlgHom F B C)) b

private theorem exists_local_primitive_correction
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ (r : (U).affinePoints (Rₐ K)) (y : G.affinePoints (Rₐ M)),
      relativeExtend F K M U r = (toAmbient p M y)⁻¹ * relativeExtend F L M U d.primitive := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) ξ h
  let B := relativeExtend F L M U d.primitive
  let Y := toAmbient p M y
  let act := relativeConjugate F K M U
  have hfix (s : M ≃ₐ[K] M) : act s (Y⁻¹ * B) = Y⁻¹ * B := by
    let s₀ := s.restrictScalars F
    let s₁ := s₀.restrictNormal L
    let c := GaloisCocycle.value ξ s₁
    have h₁ : toAmbient p M (relativeExtend F L M G c) =
        relativeExtend F L M U (toAmbient p L c) :=
      toAmbient_naturality p (IsScalarTower.toAlgHom F L M) c
    have h₂ : toAmbient p M (conjugate F M G s₀ y) = act s Y :=
      toAmbient_naturality p s₀.toAlgHom y
    have h₃ : relativeExtend F L M U (conjugate F L U s₁ d.primitive) = act s B := by
      change GaloisCocycle.coverMap F L M ≫ GaloisCocycle.arrow F L s₁ ≫ d.primitive =
        GaloisCocycle.arrow F M s₀ ≫ GaloisCocycle.coverMap F L M ≫ d.primitive
      rw [← Category.assoc, ← Category.assoc, GaloisCocycle.arrow_coverMap]
    have he := congrArg (fun z => toAmbient p M z) (hy s)
    change toAmbient p M (relativeExtend F L M G c) = toAmbient p M (y * (conjugate F M G s₀ y)⁻¹) at he
    rw [h₁, d.coboundary s₁, _root_.map_mul, _root_.map_inv, h₃, _root_.map_mul, _root_.map_inv, h₂] at he
    rw [_root_.map_mul, _root_.map_inv]
    have he' := congrArg (fun z => Y⁻¹ * z * act s B) he
    change Y⁻¹ * (B * (act s B)⁻¹) * act s B =
      Y⁻¹ * (Y * (act s Y)⁻¹) * act s B at he'
    group at he'
    simpa only [_root_.zpow_neg_one] using he'.symm
  let z : relativeFixedSubgroup F K M U := ⟨Y⁻¹ * B, hfix⟩
  exact ⟨(relativeFixedEquiv F K M U).symm z, y, relativeExtend_descend F K M U z⟩

include M in
private theorem localGram_of_comparisonField
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    GramCongruentOver F E H.inverse d.gram K := by
  obtain ⟨r, y, hr⟩ := exists_local_primitive_correction p d M h
  let B := (unitEquiv[M]) (relativeExtend F L M U d.primitive)
  let Y := (unitEquiv[M]) (toAmbient p M y)
  let P := ((unitEquiv[K]) r)⁻¹
  let k := IsScalarTower.toAlgHom F K M
  have hP : Units.map (Algebra.TensorProduct.map k (AlgHom.id F A)).toMonoidHom P = B⁻¹ * Y := by
    change Units.map (Algebra.TensorProduct.map k (AlgHom.id F A)).toMonoidHom (((unitEquiv[K]) r)⁻¹) = _
    rw [_root_.map_inv, ← relative_unitEquiv r, hr, _root_.map_mul, _root_.map_inv]
    change (Y⁻¹ * B)⁻¹ = B⁻¹ * Y
    group
  have hy : ((τ).baseChange M).gramTransform Y ((1 : M) ⊗ₜ[F] (H.inverse.gram : A)) =
      (1 : M) ⊗ₜ[F] (H.inverse.gram : A) := gramTransform_toAmbient p M y
  have hB : ((τ).baseChange M).gramTransform B⁻¹ ((1 : M) ⊗ₜ[F] (H.inverse.gram : A)) =
      (1 : M) ⊗ₜ[F] (d.gram.gram : A) := by
    let l := IsScalarTower.toAlgHom F L M
    have e := congrArg (fun x => Algebra.TensorProduct.map l (AlgHom.id F A) x) d.tensor_gram
    rw [map_gramTransform τ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      _root_.map_one, AlgHom.id_apply, AlgHom.id_apply, _root_.map_inv, ← relative_unitEquiv d.primitive] at e
    exact e
  have hinj : Function.Injective (Algebra.TensorProduct.map k (AlgHom.id F A)) :=
    TensorProduct.map_injective_of_flat_flat k.toLinearMap (LinearMap.id : A →ₗ[F] A)
      k.injective Function.injective_id
  have hP' : ((τ).baseChange K).gramTransform P ((1 : K) ⊗ₜ[F] (H.inverse.gram : A)) =
      (1 : K) ⊗ₜ[F] (d.gram.gram : A) := by
    apply hinj
    rw [map_gramTransform τ, hP, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      _root_.map_one, AlgHom.id_apply, AlgHom.id_apply, gramTransform_mul, hy, hB]
  let e := coefficientEquiv (m := Fin n) F E K
  refine ⟨Units.map e.toMonoidHom P, ?_⟩
  have h := congrArg (fun x => e x) hP'
  change e ((P : K ⊗[F] A) * ((1 : K) ⊗ₜ[F] (H.inverse.gram : A)) * (τ).baseChange K P) =
    e ((1 : K) ⊗ₜ[F] (d.gram.gram : A)) at h
  simp only [e, _root_.map_mul, coefficientEquiv_matrix_baseChange, coefficientEquiv_one_tmul_eq_map] at h
  exact h

/-- Triviality on the full base-change cover yields Hermitian Gram congruence over the
new field's entire tensor algebra of coefficients. -/
theorem GaloisGramDescent.gramCongruentOver_of_baseChange_isTrivial
    [FiniteDimensional F L] [CharZero K]
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    GramCongruentOver F E H.inverse d.gram K := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  exact localGram_of_comparisonField p d M h

end Langlands.GroupScheme.HermitianMatrix
