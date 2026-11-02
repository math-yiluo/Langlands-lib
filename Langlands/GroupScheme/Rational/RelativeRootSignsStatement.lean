import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Relative-root signs determine the dynamic subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a maximal split torus of a connected reductive group over any field,
agreement of nonnegative, zero, and positive pairings on every actual relative
root identifies the dynamic parabolic, centralizer, and unipotent subgroup
functors on all test schemes. -/
def RelativeRootSignsDetermineDynamicStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i)
    (zeta eta : cocharacterLattice T),
    haveI := hG.isAffineHom
    (∀ α ∈ relativeRoots i,
      (0 ≤ latticePairing T α zeta ↔ 0 ≤ latticePairing T α eta) ∧
      (latticePairing T α zeta = 0 ↔ latticePairing T α eta = 0) ∧
      (0 < latticePairing T α zeta ↔ 0 < latticePairing T α eta)) →
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) ∧
      Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) =
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)

end Langlands.GroupScheme
