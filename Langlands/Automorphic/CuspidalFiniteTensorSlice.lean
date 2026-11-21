import Langlands.Automorphic.CuspidalPlaceTensorDecomposition

/-! # Restricting the actual cuspidal carrier to a finite factor -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000
open scoped TensorProduct Matrix.Norms.Operator

namespace Langlands.Automorphic.CuspidalOperatorRealization

open Langlands.Global InfinitePlaceFamily

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)

local instance finiteSliceRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteSliceContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteSliceSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteSliceFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance finiteSliceStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteSliceSpaceGroup : AddCommGroup T.Space := Submodule.addCommGroup _
local instance finiteSliceFactorGroup (i : Index F) :
    AddCommGroup (T.placeDensityModels.subspace i) := Submodule.addCommGroup _
local instance finiteSliceFiniteGroup : AddCommGroup T.finiteInfiniteDecomposition.finite.toSubmodule :=
  Submodule.addCommGroup _

local notation "A" => T.finiteInfiniteDecomposition.finite

/-- The actual tensor slice with the infinite tensor fixed and the
finite factor varying. -/
def finiteTensorSlice (p : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) :
    (A).toRepresentation.IntertwiningMap T.realization.finiteRepresentation where
  toLinearMap := T.allPlaceTensorEquiv.toLinearMap.comp ((TensorProduct.mk ℂ _ _).flip p)
  isIntertwining' d := LinearMap.ext fun a =>
    T.placeDensityModels.fullTensorEquiv_finite A T.irreducible
      T.finiteInfiniteDecomposition.nonzero T.finiteInfiniteDecomposition.irreducible
      T.finiteInfiniteDecomposition.admissible d a p

@[simp]
theorem finiteTensorSlice_apply (p : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (a : (A).toSubmodule) :
    T.finiteTensorSlice p a = T.allPlaceTensorEquiv (a ⊗ₜ[ℂ] p) :=
  rfl

end Langlands.Automorphic.CuspidalOperatorRealization
