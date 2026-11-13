import Langlands.Representation.Whittaker.CoordinateJacquetKernelStatement
import Langlands.AllField.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Jacquet.Parabolic
/-!
# Uniform Whittaker vanishing on a coordinate Jacquet kernel

An internal derived prerequisite for the Jacquet-kernel step in JPS (1979),
Proposition (2.2). The threshold is uniform over the full diagonal torus,
with only the selected adjacent ratio restricted. This module defines a
closed proposition; it does not prove the vanishing assertion.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CoordinateJacquetKernelStatement
open Langlands.AllField.Whittaker

open scoped BigOperators

universe uF uV

/-- Every vector in the actual two-block Jacquet kernel has Whittaker
coefficient zero whenever the selected simple-root coordinate is small enough,
uniformly over all other diagonal entries and the common central scalar. -/
def CoordinateJacquetKernelStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
      (ψ : AddChar F ℂ),
      Continuous ψ → (∀ x, ‖ψ x‖ = 1) → IsSmooth ρ →
      let unipotent := fun g : GeneralLinear (n + 1) F =>
        (∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1
      let θ := fun g : GeneralLinear (n + 1) F =>
        ∏ j : Fin n, ψ (g.val j.castSucc j.succ)
      let torus : (Fin (n + 1) → Fˣ) →* GeneralLinear (n + 1) F :=
        (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F).toMonoidHom).comp
          MulEquiv.piUnits.symm.toMonoidHom
      ∀ ℓ : Module.Dual ℂ V,
        (∀ g, unipotent g → ∀ w, ℓ (ρ g w) = θ g * ℓ w) →
        ∀ i : Fin n,
          let B := CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val (by omega)
          ∀ v : V, B.jacquetMk ρ v = 0 →
            ∃ ε : ℝ, 0 < ε ∧
              ∀ a : Fin (n + 1) → Fˣ,
                T.normalizedAbs ((a i.castSucc / a i.succ : Fˣ) : F) < ε →
                ℓ (ρ (torus a) v) = 0

end Langlands.AllField.Whittaker
