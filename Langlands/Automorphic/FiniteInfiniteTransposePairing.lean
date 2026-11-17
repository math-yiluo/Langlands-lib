import Langlands.Automorphic.ArchimedeanPlaceTransposePairing
import Langlands.Automorphic.TransposeContragredient

/-! # The intrinsic global transpose pairing from finite and archimedean forms -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped TensorProduct

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL Langlands.GeneralLinear NumberField IsDedekindDomain

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance globalTransposeRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance globalTransposeContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance globalTransposeSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance globalTransposeFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance globalTransposeStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance globalTransposeSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (A : Subrepresentation S.finiteRepresentation)

local instance globalTransposeFiniteFactorGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

theorem finiteMultiplicityEvaluation_lie (X : ComplexLieAlgebra F n)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEvaluation A
        (TensorProduct.map LinearMap.id (S.finiteMultiplicityLie A X) t) =
      S.complexLieAction X (S.finiteMultiplicityEvaluation A t) :=
  S.finiteMultiplicityEvaluation_enveloping A (envelopingGenerator F n X) t

/-- Tensor actual finite and archimedean transpose forms, then transport by
evaluation onto the actual full realization. -/
def finiteInfiniteTransposePairing
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation)
    (C : A.toSubmodule →ₗ[ℂ] A.toSubmodule →ₗ[ℂ] ℂ)
    (hC : ∀ d a b, C (A.toRepresentation d a)
      (A.toRepresentation (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d) b) = C a b)
    (hC0 : C ≠ 0)
    (D : S.FiniteMultiplicity A →ₗ[ℂ] S.FiniteMultiplicity A →ₗ[ℂ] ℂ)
    (hDk : ∀ k x y, D (S.finiteMultiplicityCompact A k x)
      (S.finiteMultiplicityCompact A (compactTranspose F n k) y) = D x y)
    (hDl : ∀ X x y, D (S.finiteMultiplicityLie A X x) y +
      D x (S.finiteMultiplicityLie A (complexLieIota F n X) y) = 0)
    (hD0 : D ≠ 0) :
    {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ // S.IsTransposeInvariantPairing B ∧ B ≠ 0} := by
  let e := S.finiteMultiplicityEquiv A hS hne hA ha
  let B := TensorPairing.transport e C D
  refine ⟨B, ⟨?_, ?_, ?_⟩, TensorPairing.transport_ne_zero e C D hC0 hD0⟩
  · intro d x y
    exact TensorPairing.transport_invariant e C D
      (A.toRepresentation d)
      (A.toRepresentation (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d))
      LinearMap.id LinearMap.id
      (S.finiteRepresentation d)
      (S.finiteRepresentation (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d))
      (hC d) (fun _ _ => rfl)
      (S.finiteMultiplicityEvaluation_finite A d)
      (S.finiteMultiplicityEvaluation_finite A
        (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d)) x y
  · intro k x y
    exact TensorPairing.transport_invariant e C D
      LinearMap.id LinearMap.id
      (S.finiteMultiplicityCompact A k)
      (S.finiteMultiplicityCompact A (compactTranspose F n k))
      (S.compactRepresentation k) (S.compactRepresentation (compactTranspose F n k))
      (fun _ _ => rfl) (hDk k)
      (S.finiteMultiplicityEvaluation_compact A k)
      (S.finiteMultiplicityEvaluation_compact A (compactTranspose F n k)) x y
  · intro X x y
    have h := TensorPairing.transport_lie_right e C D
      (S.finiteMultiplicityLie A (complexify F n X))
      (S.finiteMultiplicityLie A (complexLieIota F n (complexify F n X)))
      (S.complexLieAction (complexify F n X))
      (S.complexLieAction (complexLieIota F n (complexify F n X)))
      (hDl (complexify F n X))
      (S.finiteMultiplicityEvaluation_lie A (complexify F n X))
      (S.finiteMultiplicityEvaluation_lie A (complexLieIota F n (complexify F n X))) x y
    simpa only [B, lieAction, complexLieAction_apply, complexify_apply,
      complexLieIota_tmul] using h

namespace PlaceDensityModels

variable {S} (P : S.PlaceDensityModels)

local instance globalTransposeSourceGroup (i : InfinitePlaceFamily.Index F) :
    AddCommGroup (P.subspace i) := Submodule.addCommGroup _

/-- Actual local archimedean forms and an actual finite-factor form give
the nonzero intrinsic global pairing. -/
def fullTransposePairing
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation)
    (C : A.toSubmodule →ₗ[ℂ] A.toSubmodule →ₗ[ℂ] ℂ)
    (hC : ∀ d a b, C (A.toRepresentation d a)
      (A.toRepresentation (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d) b) = C a b)
    (hC0 : C ≠ 0)
    (hr : ∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      Archimedean.HasNonzeroTransposeGKPairing ℝ n
        (P.sourceCompact (.inl v)) (P.sourceLie (.inl v)))
    (hc : ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      Archimedean.HasNonzeroTransposeGKPairing ℂ n
        (P.sourceCompact (.inr v)) (P.sourceLie (.inr v))) :
    {B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ // S.IsTransposeInvariantPairing B ∧ B ≠ 0} :=
  let D := P.transposeMultiplicityPairing A hS hne hA ha hr hc
  S.finiteInfiniteTransposePairing A hS hne hA ha C hC hC0
    D.val D.property.1.1 D.property.1.2 D.property.2

end PlaceDensityModels
end OperatorRealization
end Langlands.Automorphic
