# Rational conjugation of a parabolic split torus into a supplied Levi

Authors: Worker 117 and Worker 3483 (named Worker 15 in the route note).
Worker 3483 supplied the composition route; Worker 117 instantiated it with
the canonical published proofs.

`Langlands.GroupScheme.parabolicSplitTorusLeviConjugacy` proves exactly
`Langlands.GroupScheme.ParabolicSplitTorusLeviConjugacyStatement.{u}`, defined
in `Langlands.GroupScheme.Rational.ParabolicDoubleCosetRepresentatives`, at
the published arbitrary universe `u`. The theorem adds no hypotheses.

For every field, let `G` be connected reductive, `p : P ⟶ G` a parabolic and
`l : M ⟶ P` a supplied rational Levi. If the ambient maximal split torus
`i : T.toGrp ⟶ G` has a supplied factor `f ≫ p = i`, there are a point
`u ∈ P(k)` and a morphism `a : T.toGrp ⟶ M` such that
`a ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p u)).hom`.
The original torus source and supplied Levi are preserved.

The proof applies the published reduction
`Langlands.GroupScheme.parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy`
from `Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly`. Every
input theorem is a published unconditional proof:

| Input theorem | Module |
| --- | --- |
| `Langlands.GroupScheme.parabolicDynamic` | `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` |
| `Langlands.GroupScheme.smoothMaximalSplitTorusConjugacy` | `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof` |

Inside the reduction, the supplied factorization gives containment of the
all-test subgroup functors. The published supplied-Levi construction then
produces the rational point and actual factorization equation. Both
structural premises of the reduction are discharged at universe `u`.

This is derived content from those Library results and the route recorded in
`notes/group-schemes/smooth-split-torus-conjugacy-route.md`. The statement's
paired Markdown explains its geometric provenance. This proof uses the
published dynamic and smooth-group conjugacy reduction, with every field
and characteristic retained and no extra splitting, perfectness or infinitude
condition.
