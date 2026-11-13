import Langlands.GroupScheme.Torus.Induced
import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Z-extensions of actual connected reductive field groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The derived subgroup of `G` is simply connected, expressed using an actual
closed representative of its full scheme-theoretic derived subgroup. -/
def HasSimplyConnectedDerivedGroup (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsDerivedSubgroup d ∧ IsSimplyConnected D

/-- KP §11.4: `1 → Z → H → G → 1` is a z-extension. Exactness is fppf
exactness with the full scheme-theoretic kernel, including nonreduced tests. -/
structure IsZExtension
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    (i : Z.toGrp ⟶ H) (p : H ⟶ G) : Prop where
  induced : IsInducedTorus Z
  closed : IsClosedSubgroup i
  central : IsCentral i
  quotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p
  source_reductive : IsConnectedReductive H
  target_reductive : IsConnectedReductive G
  derived_simplyConnected : HasSimplyConnectedDerivedGroup H

/-- The actual groups and maps of one z-extension of `G`; there is no point
surjectivity or Kottwitz homomorphism supplied as a field. -/
structure ZExtension (G : GroupScheme (Spec (CommRingCat.of k))) : Type (u + 1) where
  Z : CommGroupScheme (Spec (CommRingCat.of k))
  H : GroupScheme (Spec (CommRingCat.of k))
  i : Z.toGrp ⟶ H
  p : H ⟶ G
  isZExtension : IsZExtension i p

end Langlands.GroupScheme
