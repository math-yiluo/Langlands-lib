import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct

/-! # Reference pure tensors and one-place Whittaker coefficient maps -/

noncomputable section
open NumberField
open scoped Classical TensorProduct CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open Langlands.Automorphic ContinuousRationalFunctions InfinitePlaceFamily
  Langlands.Global.CuspidalPairFunctionalEquation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {T : CuspidalOperatorRealization F r}

local notation "n" => r + 1

private abbrev PlaceSource (T : CuspidalOperatorRealization F r) (i : Index F) : Type u :=
  T.placeDensityModels.subspace i

local notation "V" => PlaceSource T

private local instance (m : ℕ) : AlgebraicGeometry.IsAffine (Scheme F m).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
private local instance (m : ℕ) : AlgebraicGeometry.Smooth (Scheme F m).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
private local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup T.Space := Submodule.addCommGroup _
private local instance (i : Index F) : AddCommGroup (V i) := Submodule.addCommGroup _

variable (P : CuspidalSpectralPresentation.{u, uQ} T)
  (hP : HasIrreducibleAdmissibleComponents P) (χ : AddChar (Adeles F) ℂ)
  (hχ : IsStandardAdditiveCharacter F χ)

omit [CompactSpace (AdeleQuotient F)] in
theorem placeTuplePoint_one : placeTuplePoint n (1 : PlaceTuple (F := F) n) = 1 := by
  change adelicPoint F n (placeGL F n 1) 1 = 1
  rw [map_one, ArchimedeanWhittakerEvaluation.adelicPoint_one]

include hχ in
/-- Some actual pure tensor has nonzero Whittaker value at the adelic identity. -/
theorem exists_tensorWhittaker_one_ne_zero :
    ∃ (a : FiniteTensor P) (b : ∀ i, V i), tensorWhittaker P hP χ a b 1 ≠ 0 := by
  by_contra! hz
  let e := P.allPlaceTensorEquiv hP
  let L := (UnramifiedWhittaker.whittakerFunctional F χ hχ T 1).comp e.toLinearMap
  have hpure (a : FiniteTensor P) (b : ∀ i, V i) :
      L (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) = 0 := by
    let x : T.Space := e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)
    exact (congrArg (cuspWhittaker F T χ x) (placeTuplePoint_one (F := F) (r := r))).symm.trans
      (hz a b)
  have hall : L = 0 := by
    apply TensorProduct.ext'
    intro a t
    have hpartial : L.comp (TensorProduct.mk ℂ _ _ a) = 0 := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      exact hpure a
    change (L.comp (TensorProduct.mk ℂ _ _ a)) t = 0
    exact DFunLike.congr_fun hpartial t
  obtain ⟨x, hx⟩ := ArchimedeanWhittakerEvaluation.exists_cuspWhittaker_one_ne_zero T χ hχ
  obtain ⟨t, rfl⟩ := e.surjective x
  exact hx (DFunLike.congr_fun hall t)

omit hχ in
/-- Insert a single variable place vector into a pure tensor with prescribed other factors. -/
def sliceVector (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j) : V i →ₗ[ℂ] T.Space :=
  (P.allPlaceTensorEquiv hP).toLinearMap.comp
    ((TensorProduct.mk ℂ _ _ a).comp ((PiTensorProduct.tprod ℂ).toLinearMap b i))

/-- Freeze the finite vector, the other infinite vector factors and the other
infinite group coordinates. The resulting coefficient is linear in the remaining
local vector. -/
def sliceMap (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) : V i →ₗ[ℂ] (PlaceGroup n i → ℂ) :=
  LinearMap.pi fun h =>
    (UnramifiedWhittaker.whittakerFunctional F χ hχ T
        (placeTuplePoint n (Function.update g i h))).comp (sliceVector P hP a i b)

theorem sliceMap_apply (a : FiniteTensor P) (i : Index F) (b : ∀ j, V j)
    (g : PlaceTuple (F := F) n) (v : V i) (h : PlaceGroup n i) :
    sliceMap P hP χ hχ a i b g v h =
      tensorWhittaker P hP χ a (Function.update b i v) (Function.update g i h) := rfl

/-- The slices through a single pure tensor give local maps with identity value one. -/
def referenceModel (a : FiniteTensor P) (b : ∀ j, V j) (i : Index F) :
    V i →ₗ[ℂ] (PlaceGroup n i → ℂ) :=
  (tensorWhittaker P hP χ a b 1)⁻¹ • sliceMap P hP χ hχ a i b 1

theorem referenceModel_normalized (a : FiniteTensor P) (b : ∀ j, V j)
    (hne : tensorWhittaker P hP χ a b 1 ≠ 0) (i : Index F) :
    referenceModel P hP χ hχ a b i (b i) 1 = 1 := by
  have hb : Function.update b i (b i) = b := Function.update_eq_self_iff.mpr rfl
  have hg : Function.update (1 : PlaceTuple (F := F) n) i 1 = 1 :=
    Function.update_eq_self_iff.mpr rfl
  simp only [referenceModel, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, sliceMap_apply,
    hb, hg, inv_mul_cancel₀ hne]

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
