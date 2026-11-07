import Langlands.VirtualRepresentation.Weil.ExactRealization
import Langlands.VirtualRepresentation.Weil.LocalUnitaryOperations
import Langlands.VirtualRepresentation.ExactDual
import Langlands.VirtualRepresentation.ExactTwist

/-! # Duality and twisting of actual exact expansions -/

noncomputable section

universe uG uV

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Forgetting irreducibility commutes with the actual continuous character twist. -/
theorem basisContinuousClass_twistBasisEquiv (χ : G →ₜ* ℂˣ)
    (b : IrreducibleBasis.{uG, uV} G) :
    basisContinuousClass G (twistBasisEquiv χ b) =
      ExactGrothendieckGroup.twistClassWith χ.toMonoidHom _ _
        (fun _ hA => FiniteRepresentation.isContinuous_twist χ hA)
        (basisContinuousClass G b) := by
  rcases b with ⟨n, c, hc⟩
  induction c using Quotient.inductionOn with
  | h A => rfl

/-- Realization in exact K0 intertwines the genuine irreducible and exact twists. -/
@[simp]
theorem realizeExact_twistLatticeEquiv (χ : G →ₜ* ℂˣ)
    (x : IrreducibleLattice.{uG, uV} G) :
    realizeExact G (twistLatticeEquiv χ x) =
      ExactGrothendieckGroup.continuousTwist χ (realizeExact G x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    have hs : Finsupp.single b m = m • generator b := by simp [generator]
    rw [hs]
    simp only [map_smul]
    congr 1
    rw [twistLatticeEquiv_generator, realizeExact_generator, realizeExact_generator]
    change ExactGrothendieckGroup.ofClass _ _ =
      ExactGrothendieckGroup.twist χ.toMonoidHom _ _
        (fun _ hA => FiniteRepresentation.isContinuous_twist χ hA)
        (ExactGrothendieckGroup.ofClass _ _)
    rw [ExactGrothendieckGroup.twist_ofClass, basisContinuousClass_twistBasisEquiv]

/-- Every supplied exact expansion twists term by term. -/
theorem ExactExpansion.twist {x : ContinuousExactGroup.{uG, uV} G}
    {v : IrreducibleLattice.{uG, uV} G} (h : ExactExpansion G x v)
    (χ : G →ₜ* ℂˣ) :
    ExactExpansion G (ExactGrothendieckGroup.continuousTwist χ x)
      (twistLatticeEquiv χ v) := by
  change realizeExact G _ = _
  rw [realizeExact_twistLatticeEquiv, h]

/-- The actual twist map on the fiber of supplied irreducible expansions. -/
def twistExpansion (χ : G →ₜ* ℂˣ) {x : ContinuousExactGroup.{uG, uV} G}
    (v : {v : IrreducibleLattice.{uG, uV} G // ExactExpansion G x v}) :
    {v : IrreducibleLattice.{uG, uV} G //
      ExactExpansion G (ExactGrothendieckGroup.continuousTwist χ x) v} :=
  ⟨twistLatticeEquiv χ v.val, v.property.twist χ⟩

/-- Modulus-one twists transport a supplied exact expansion in the unitary lattice. -/
theorem ExactExpansion.unitaryTwist {x : ContinuousExactGroup.{uG, uV} G}
    {v : UnitaryLattice.{uG, uV} G} (h : ExactExpansion G x (includeUnitary G v))
    (χ : G →ₜ* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    ExactExpansion G (ExactGrothendieckGroup.continuousTwist χ x)
      (includeUnitary G (unitaryTwistLatticeEquiv χ hχ v)) := by
  rw [includeUnitary_twist]
  exact h.twist χ

variable [IsTopologicalGroup G]

/-- Forgetting irreducibility commutes with actual continuous duality. -/
theorem basisContinuousClass_dualBasisEquiv (b : IrreducibleBasis.{uG, uV} G) :
    basisContinuousClass G (dualBasisEquiv b) =
      ExactGrothendieckGroup.dualClassWith _
        (fun A hA => (FiniteRepresentation.isContinuous_dual_iff A).mpr hA)
        (basisContinuousClass G b) := by
  rcases b with ⟨n, c, hc⟩
  induction c using Quotient.inductionOn with
  | h A => rfl

/-- Realization in exact K0 intertwines genuine irreducible and exact duality. -/
@[simp]
theorem realizeExact_dualLatticeEquiv (x : IrreducibleLattice.{uG, uV} G) :
    realizeExact G (dualLatticeEquiv x) =
      ExactGrothendieckGroup.continuousDual (realizeExact G x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    have hs : Finsupp.single b m = m • generator b := by simp [generator]
    rw [hs]
    simp only [map_smul]
    congr 1
    rw [dualLatticeEquiv_generator, realizeExact_generator, realizeExact_generator,
      ExactGrothendieckGroup.continuousDual_ofClass, basisContinuousClass_dualBasisEquiv]

/-- Every supplied exact expansion dualizes term by term. -/
theorem ExactExpansion.dual {x : ContinuousExactGroup.{uG, uV} G}
    {v : IrreducibleLattice.{uG, uV} G} (h : ExactExpansion G x v) :
    ExactExpansion G (ExactGrothendieckGroup.continuousDual x)
      (dualLatticeEquiv v) := by
  change realizeExact G _ = _
  rw [realizeExact_dualLatticeEquiv, h]

/-- The actual dual map on the fiber of supplied irreducible expansions. -/
def dualExpansion {x : ContinuousExactGroup.{uG, uV} G}
    (v : {v : IrreducibleLattice.{uG, uV} G // ExactExpansion G x v}) :
    {v : IrreducibleLattice.{uG, uV} G //
      ExactExpansion G (ExactGrothendieckGroup.continuousDual x) v} :=
  ⟨dualLatticeEquiv v.val, v.property.dual⟩

/-- Actual unitary duality transports a supplied exact expansion. -/
theorem ExactExpansion.unitaryDual {x : ContinuousExactGroup.{uG, uV} G}
    {v : UnitaryLattice.{uG, uV} G} (h : ExactExpansion G x (includeUnitary G v)) :
    ExactExpansion G (ExactGrothendieckGroup.continuousDual x)
      (includeUnitary G (unitaryDualLatticeEquiv v)) := by
  rw [includeUnitary_dual]
  exact h.dual

end Langlands.VirtualRepresentation.Weil
