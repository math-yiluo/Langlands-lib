import Langlands.Automorphic.CuspidalPlaceTensorSlice
import Langlands.Representation.TensorProduct.FunctionalSliceComparison

/-! # The tensor functional slot on an actual cuspidal slice -/

noncomputable section
open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global InfinitePlaceFamily
universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance tensorSlotRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorSlotContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorSlotSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorSlotFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorSlotStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorSlotSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

local instance tensorSlotFiniteGroup : AddCommGroup T.finiteInfiniteDecomposition.finite.toSubmodule :=
  Submodule.addCommGroup _
local instance tensorSlotInfiniteGroup (i : Index F) : AddCommGroup (T.placeDensityModels.subspace i) :=
  Submodule.addCommGroup _

/-- Evaluating a tensor functional in a single varying infinite slot is
restriction along the actual algebraic place slice. -/
theorem tensorFunctionalMultilinearSlice_eq_comp_placeTensorSlice
    (ℓ : T.Space →ₗ[ℂ] ℂ) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j) (i : Index F) :
    (tensorFunctionalMultilinearSlice (ℓ.comp T.allPlaceTensorEquiv.toLinearMap) a).toLinearMap b i =
      ℓ.comp (T.placeTensorSlice i a b) :=
  LinearMap.ext fun _ => rfl

end CuspidalOperatorRealization
end Langlands.Automorphic
