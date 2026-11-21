import Langlands.Automorphic.AdelicHilbertPlaceFixedLevel
import Langlands.Automorphic.ArchimedeanPlaceOperatorFamily

/-! # Fixed-level Hilbert comparisons indexed by the infinite places -/

noncomputable section
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global ArchimedeanGL RankinSelbergGlobal OperatorDeterminantSlice
open InfinitePlaceFamily
universe u uV uX uY
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F n) V}
  {κ : Representation ℂ (standardInfiniteCompact F n) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)
  (d : ∀ i : Index F, Lie n i →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The fixed-level comparison in the chart for the indexed real or complex place. -/
def HasIndexedPlaceFixedSmoothRealization (i : Index F) (U : Subgroup (FiniteAdelicGL F n))
    (W : Submodule ℂ V) : Prop :=
  let R := B.action.comp (infiniteCoordinateInclusion F n)
  let P := B.action.comp (AdelicGL.ofFinite F n).toMonoidHom
  match i with
  | .inl w => HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F n) R P
      (realPlaceGL F n w) b.toHilbert (Unitary.toUnits :
        Matrix.unitaryGroup (Fin n) ℝ →* (Matrix (Fin n) (Fin n) ℝ)ˣ)
      (κ.comp (compactInclusion n (.inl w)).toMonoidHom) (d (.inl w))
      (coordinateActions_commute B.action) U W
  | .inr w => HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F n) R P
      (complexPlaceGL F n w) b.toHilbert (Unitary.toUnits :
        Matrix.unitaryGroup (Fin n) ℂ →* (Matrix (Fin n) (Fin n) ℂ)ˣ)
      (κ.comp (compactInclusion n (.inr w)).toMonoidHom) (d (.inr w))
      (coordinateActions_commute B.action) U W

/-- The compact open level of a supplied algebraic slice gives its fixed-level smooth realization. -/
theorem hasIndexedPlaceFixedSmoothRealization_of_slice
    (hR : ∀ w : {v : NumberField.InfinitePlace F // v.IsReal},
      B.SupportsRealPlaceFixedSmoothRealization w (d (.inl w)))
    (hC : ∀ w : {v : NumberField.InfinitePlace F // v.IsComplex},
      B.SupportsComplexPlaceFixedSmoothRealization w (d (.inr w)))
    (i : Index F) {Y : Type uY} [AddCommGroup Y] [Module ℂ Y] (L : Y →ₗ[ℂ] V)
    (h : Function.Injective L ∧
      PlaceComponent.IsIrreducible (κ.comp (compactInclusion n i).toMonoidHom) (d i)
        (LinearMap.range L) ∧
      PlaceComponent.IsAdmissible (κ.comp (compactInclusion n i).toMonoidHom) (LinearMap.range L) ∧
      ∃ U : OpenSubgroup (FiniteAdelicGL F n), IsCompact (U : Set (FiniteAdelicGL F n)) ∧
        ∀ g ∈ U, ∀ y, ρ g (L y) = L y) :
    ∃ U : OpenSubgroup (FiniteAdelicGL F n), IsCompact (U : Set (FiniteAdelicGL F n)) ∧
      B.HasIndexedPlaceFixedSmoothRealization d i U.toSubgroup (LinearMap.range L) := by
  obtain ⟨_, hirr, hadm, U, hU, hfix⟩ := h
  have hfixW (l : U) (v : LinearMap.range L) : ρ (l : FiniteAdelicGL F n) v = v := by
    obtain ⟨x, hx⟩ := v.property
    exact (congrArg (fun z => ρ (l : FiniteAdelicGL F n) z) hx).symm.trans
      ((hfix l l.property x).trans hx)
  refine ⟨U, hU, ?_⟩
  cases i with
  | inl w => exact hR w U.toSubgroup (LinearMap.range L) hirr hadm hfixW
  | inr w => exact hC w U.toSubgroup (LinearMap.range L) hirr hadm hfixW

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
