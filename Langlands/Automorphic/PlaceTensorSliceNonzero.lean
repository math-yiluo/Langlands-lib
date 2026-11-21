import Langlands.Automorphic.CuspidalPlaceTensorSlice

/-! # Nonvanishing of the fixed factors of a cuspidal tensor slice -/

noncomputable section
open scoped Classical TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000

namespace Langlands.Automorphic.OperatorRealization.PlaceDensityModels

open Langlands.Global InfinitePlaceFamily
universe u
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem multilinearSlice_eq_zero
    {I : Type*} [DecidableEq I] {M : I → Type*} {E : Type*}
    [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)] [AddCommGroup E] [Module ℂ E]
    (m : MultilinearMap ℂ M E) (b : ∀ j, M j) {i j : I} (hj : j ≠ i) (hbj : b j = 0) :
    m.toLinearMap b i = 0 :=
  LinearMap.ext fun x => m.map_coord_zero j ((Function.update_of_ne hj x b).trans hbj)

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

variable {S : OperatorRealization F n} (D : S.PlaceDensityModels)
  (A : Subrepresentation S.finiteRepresentation)

local instance nonzeroFactorGroup (i : Index F) : AddCommGroup (D.subspace i) := Submodule.addCommGroup _
local instance nonzeroFiniteGroup : AddCommGroup A.toSubmodule := Submodule.addCommGroup _

/-- A nonzero restriction to the slice forces all fixed factors to be nonzero. -/
theorem tensorSlice_fixedFactors_ne_zero
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (hadm : IsAdmissible A.toRepresentation)
    (i : Index F) (a : A.toSubmodule) (b : ∀ j, D.subspace j) (f : S.Space →ₗ[ℂ] ℂ)
    (hn : f.comp (D.tensorSlice A hS hne hA hadm i a b) ≠ 0) :
    a ≠ 0 ∧ ∀ j, j ≠ i → b j ≠ 0 := by
  constructor
  · intro ha
    apply hn
    unfold tensorSlice
    simp only [ha, LinearMap.map_zero, LinearMap.zero_comp, LinearMap.comp_zero]
  · intro j hj hbj
    apply hn
    have hzero := multilinearSlice_eq_zero (PiTensorProduct.tprod ℂ) b hj hbj
    unfold tensorSlice
    simp only [hzero, LinearMap.comp_zero]

end Langlands.Automorphic.OperatorRealization.PlaceDensityModels
