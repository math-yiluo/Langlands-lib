import Langlands.Global.Factors.CuspidalSupportIdentityEvaluation

/-! # Common cuspidal support from restored identity coefficients -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean Langlands.GeneralLinear
open FiniteParametrizedBlockInduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 1600000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance restoredIdentityRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance restoredIdentityContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance restoredIdentitySmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance restoredIdentityFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance restoredIdentityStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance restoredIdentityRealizationGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance restoredIdentityOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- A common operator quotient and restored cuspidal coefficient evaluation at identity.
The finite subquotient uses the half-modulus-normalized blocks. The compact and
Lie equations at the identity are stated on the restored, unnormalized blocks. -/
def HasRestoredCuspidalIdentityRealization {r : ℕ} (Q : IrreducibleOperatorSubquotient F r) : Prop :=
  ∃ (c : ℕ) (m : Fin c → ℕ) (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i)),
    let B : BlockShape (r + 1) := ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
    HasSubquotient B (fun i => ((normalizedCuspidalBlocks hm T) i).realization.finiteRepresentation)
      Q.subquotient.finiteRepresentation ∧
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ W)
      (q : Representation.IntertwiningMap A.toMonoidHom Q.representation)
      (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((T i).Space))),
      Function.Surjective q.toLinearMap ∧
      (∀ w, (∀ k g, compactFiniteCoefficientEvaluation A ev k g w = 0) → w = 0) ∧
      (∀ v : RP,
        IsRealGKModule (r + 1) (sourceRealPlaceCompact A v) (sourceRealPlaceLie A v) ∧
        IsBlockCompactEvaluation (B := B) (sourceRealPlaceCompact A v)
          (fun i => (T i).realization.realPlaceCompactRepresentation v) ev ∧
        IsUnnormalizedBlockLieEvaluation B (sourceRealPlaceLie A v)
          (fun i X => (T i).realization.realPlaceLieAction v (1 ⊗ₜ X)) ev) ∧
      ∀ v : CP,
        IsComplexGKModule (r + 1) (sourceComplexPlaceCompact A v) (sourceComplexPlaceLie A v) ∧
        IsBlockCompactEvaluation (B := B) (sourceComplexPlaceCompact A v)
          (fun i => (T i).realization.complexPlaceCompactRepresentation v) ev ∧
        IsUnnormalizedBlockLieEvaluation B (sourceComplexPlaceLie A v)
          (fun i X => (T i).realization.complexPlaceLieAction v (1 ⊗ₜ X)) ev

/-- Normalize the one common block tuple and transport the identity equations to
all complementary compact and finite translates of the source. -/
theorem hasProjectedCuspidalBlockRealization_of_restoredIdentity {r : ℕ}
    (Q : IrreducibleOperatorSubquotient F r) (h : HasRestoredCuspidalIdentityRealization Q) :
    HasProjectedCuspidalBlockRealization Q := by
  obtain ⟨c, m, hm, T, hF, W, _, _, A, q, ev, hq, hsep, hR, hC⟩ := h
  let T' := normalizedCuspidalBlocks hm T
  let e := (normalizedCuspidalCoefficientEquiv hm T).toLinearEquiv
  let ev' := e.toLinearMap.comp ev
  have hsep' (w : W) (hw : ∀ k g, compactFiniteCoefficientEvaluation A ev' k g w = 0) :
      w = 0 := by
    apply hsep w
    intro k g
    apply e.injective
    rw [map_zero]
    exact hw k g
  refine ⟨c, m, hm, T', hF, W, _, _, q.toLinearMap, hq, ?_, ?_⟩
  · intro v
    obtain ⟨hgk, hK, hL⟩ := hR v
    exact hasRealCuspidalBlockEvaluations_of_identity hm T' Q A q ev' v hgk
      (normalizedCuspidalBlocks_realCompactEvaluation hm T v _ ev hK)
      (normalizedCuspidalBlocks_realLieEvaluation hm T v _ ev hL) hsep'
  · intro v
    obtain ⟨hgk, hK, hL⟩ := hC v
    exact hasComplexCuspidalBlockEvaluations_of_identity hm T' Q A q ev' v hgk
      (normalizedCuspidalBlocks_complexCompactEvaluation hm T v _ ev hK)
      (normalizedCuspidalBlocks_complexLieEvaluation hm T v _ ev hL) hsep'

end Langlands.Global
