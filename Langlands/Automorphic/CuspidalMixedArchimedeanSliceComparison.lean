import Langlands.Automorphic.CuspidalPlaceTensorFixedSmooth
import Langlands.Automorphic.PlaceTensorSliceNonzero
import Langlands.Automorphic.IndexedPlaceMixedWhittaker

/-! # Archimedean slice comparisons for the actual cuspidal mixed functions -/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000
set_option Elab.async false

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global RankinSelbergGlobal OperatorDeterminantSlice
open RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth InfinitePlaceFamily
open Langlands.HarmonicAnalysis OperatorUnitaryFormCore.AdelicCompletion
universe u
attribute [local instance] regSchemeAffine regSchemeSmooth
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance mixedSliceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance mixedSliceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance mixedSliceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance mixedSliceFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance mixedSliceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance mixedSliceSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Any two mixed Whittaker functionals for a standard additive character
are proportional on each specified archimedean tensor slice with nonzero
first restriction, given local unitary Whittaker uniqueness. -/
def CuspidalMixedArchimedeanSliceComparisonStatement : Prop :=
  UnitaryWhittakerMultiplicityOneStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (band : T.realization.UnitaryForm) (hband : ComputesBandInnerProduct T.realization band)
    (i : Index K) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j),
    let B := adelicCompletion T χ hχ hTχ band hband
    B.HasIndexedWhittakerSliceComparison (T.placeTensorSlice i a b)

theorem cuspidalMixedArchimedeanSliceComparison : CuspidalMixedArchimedeanSliceComparisonStatement.{u} := by
  intro hUnique K _ _ _ r T χ hχ hTχ band hband i a b
  let B := adelicCompletion T χ hχ hTχ band hband
  let A := T.finiteInfiniteDecomposition
  let D := T.placeDensityModels
  refine B.hasIndexedWhittakerSliceComparison_of_fixedLevel T.realization.placeLieFamily
    hUnique i (T.placeTensorSlice i a b) ?_
  intro hs
  let f := Classical.choose hs
  have hfix := D.tensorSlice_fixedFactors_ne_zero A.finite T.irreducible A.nonzero A.irreducible
    A.admissible i a b f (Classical.choose_spec hs)
  exact placeTensorFixedSmooth K r T χ hχ hTχ band hband i a b hfix.1 hfix.2

end Langlands.Automorphic.CuspidalOperatorRealization
