import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Actual relative-root signs and dynamic subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Nonnegative actual-root support detects inclusion of dynamic parabolic
subgroup functors, and positive actual-root support containment implies
inclusion of dynamic unipotent subgroup functors. -/
def RelativeRootSignInclusionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i)
    (zeta eta : cocharacterLattice T),
    haveI := hG.isAffineHom
    (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
      ∀ α ∈ relativeRoots i,
        0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta) ∧
    ((∀ α ∈ relativeRoots i,
        0 < latticePairing T α zeta → 0 < latticePairing T α eta) →
      Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i))

end Langlands.GroupScheme
