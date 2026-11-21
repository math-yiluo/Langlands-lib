import Langlands.Automorphic.CuspidalPlaceTensorDecomposition
import Langlands.Representation.TensorProduct.FunctionalSliceComparison

/-! # Comparing functionals on the actual cuspidal tensor carrier -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000
open scoped Classical TensorProduct

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global InfinitePlaceFamily

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

local instance comparisonRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance comparisonStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance comparisonSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _
local instance comparisonFactorGroup (i : Index F) :
    AddCommGroup (T.placeDensityModels.subspace i) := Submodule.addCommGroup _
local instance comparisonFiniteGroup : AddCommGroup T.finiteInfiniteDecomposition.finite.toSubmodule :=
  Submodule.addCommGroup _

/-- The two original functionals have proportional restrictions to each
fixed-context slice of the actual finite and infinite tensor model whenever
the restriction of the first functional is nonzero. -/
def HaveProportionalTensorSlices (ℓ₀ ℓ₁ : T.Space →ₗ[ℂ] ℂ) : Prop :=
  HaveProportionalSlices (ℓ₀.comp T.allPlaceTensorEquiv.toLinearMap)
    (ℓ₁.comp T.allPlaceTensorEquiv.toLinearMap)

/-- The local slice comparisons imply a single scalar on the whole
original cuspidal carrier. -/
theorem proportional_of_tensorSlices (ℓ₀ ℓ₁ : T.Space →ₗ[ℂ] ℂ) (hne : ℓ₀ ≠ 0)
    (h : HaveProportionalTensorSlices T ℓ₀ ℓ₁) : ∃ c : ℂ, ℓ₁ = c • ℓ₀ := by
  let : Fintype (Index F) := Fintype.ofFinite _
  exact functional_proportional_of_tensorEquiv T.allPlaceTensorEquiv ℓ₀ ℓ₁ hne h

end Langlands.Automorphic.CuspidalOperatorRealization
