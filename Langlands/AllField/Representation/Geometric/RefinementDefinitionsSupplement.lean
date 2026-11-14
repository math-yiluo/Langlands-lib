import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.Geometric.RefinementDefinitions
/-! Intrinsic projection and explicit modulus for a parabolic in a product Levi. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

section Topology

end Topology
end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.Geometric
open Langlands.AllField.Geometric
open scoped BigOperators NNReal

universe u
variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : BlockRefinement B)

/-- The positive half on the refined parabolic. -/
def refinedParabolicHalfModulus : refinedParabolic F B S →* ℂˣ :=
  (T.refinedLeviHalfModulus B S).comp (refinedLeviProjection F B S)

theorem refinedLeviInverseHalfModulus_eq_inv :
    T.refinedLeviInverseHalfModulus B S = (T.refinedLeviHalfModulus B S)⁻¹ := rfl

@[simp] theorem refinedParabolicHalfModulus_apply (g : refinedParabolic F B S) :
    T.refinedParabolicHalfModulus B S g =
      T.refinedLeviHalfModulus B S (refinedLeviProjection F B S g) := rfl

/-- The compatible field topology makes inner-block evaluation continuous. -/
theorem continuous_refinedLeviBlock (i : Fin B.length) :
    let := T.topology
    Continuous (refinedLeviBlock (F := F) B S i) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ((S i).leviEquivContinuous F).symm.continuous.comp
    (continuous_refinedLeviEval F B S i)

/-- The finite intersection of factor kernels is an open subgroup of the full kernel. -/
theorem isOpen_ker_refinedLeviModulus :
    let := T.topology
    IsOpen ((T.refinedLeviModulus B S).ker : Set (refinedLevi F B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let K : Subgroup (refinedLevi F B S) :=
    ⨅ i : Fin B.length, ((T.leviModulus (S i)).comp (refinedLeviBlock B S i)).ker
  have hK : IsOpen (K : Set (refinedLevi F B S)) := by
    have h : ∀ i : Fin B.length,
        IsOpen {m : refinedLevi F B S |
          T.leviModulus (S i) (refinedLeviBlock B S i m) = 1} := fun i =>
      (T.isOpen_ker_leviModulus (S i)).preimage (T.continuous_refinedLeviBlock B S i)
    convert isOpen_iInter_of_finite h using 1
    ext m
    simp [K]
  apply Subgroup.isOpen_mono (show K ≤ (T.refinedLeviModulus B S).ker from ?_) hK
  intro m hm
  have h : ∀ i, T.leviModulus (S i) (refinedLeviBlock B S i m) = 1 := by
    simpa only [K, Subgroup.mem_iInf, MonoidHom.mem_ker, MonoidHom.comp_apply] using hm
  change T.refinedLeviModulus B S m = 1
  simp [T.refinedLeviModulus_apply B S, h]

end Langlands.LocalFieldData
