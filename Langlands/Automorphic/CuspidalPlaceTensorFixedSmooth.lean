import Langlands.Automorphic.CuspidalHilbertPlaceFixedLevel
import Langlands.Automorphic.IndexedHilbertPlaceFixedLevel
import Langlands.Automorphic.CuspidalPlaceTensorSlice

/-! # Smooth fixed-level embeddings of the actual cuspidal tensor slices -/

noncomputable section
universe u
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
set_option Elab.async false

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global OperatorDeterminantSlice
open InfinitePlaceFamily OperatorUnitaryFormCore.AdelicCompletion

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance tensorFixedRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorFixedContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorFixedSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorFixedFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorFixedStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorFixedSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- At every infinite place, a slice with nonzero fixed factors has a common compact
open level and a continuous extension of its Hilbert inclusion at that level. -/
def PlaceTensorFixedSmoothStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (band : T.realization.UnitaryForm) (hband : ComputesBandInnerProduct T.realization band)
    (i : Index K) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j),
    a ≠ 0 → (∀ j, j ≠ i → b j ≠ 0) →
    let B := adelicCompletion T χ hχ hTχ band hband
    ∃ U : OpenSubgroup (FiniteAdelicGL K (r + 1)),
      IsCompact (U : Set (FiniteAdelicGL K (r + 1))) ∧
      B.HasIndexedPlaceFixedSmoothRealization T.realization.placeLieFamily i U.toSubgroup
        (LinearMap.range (T.placeTensorSlice i a b))

theorem placeTensorFixedSmooth : PlaceTensorFixedSmoothStatement.{u} := by
  intro K _ _ _ r T χ hχ hTχ band hband i a b ha hb
  let B := adelicCompletion T χ hχ hTχ band hband
  have hS := OperatorRealization.cuspidalHilbertPlaceFixedLevel K r T χ hχ hTχ band hband
  exact B.hasIndexedPlaceFixedSmoothRealization_of_slice T.realization.placeLieFamily
    hS.1 hS.2 i (T.placeTensorSlice i a b) (placeTensorSliceStatement K r T i a b ha hb)

end Langlands.Automorphic.CuspidalOperatorRealization
