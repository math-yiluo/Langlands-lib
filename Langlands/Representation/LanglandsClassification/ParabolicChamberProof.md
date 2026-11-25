# Assembly of the parabolic chamber proofs

Module
`Langlands.Representation.LanglandsClassification.ParabolicChamberProof`,
namespace `Langlands.GroupScheme`.

The theorem `Langlands.GroupScheme.parabolicChamber.{u}` has exactly the type
`Langlands.GroupScheme.ParabolicChamberStatement.{u}`. The published
[statement module](ParabolicChamberStatements.md) defines this proposition as
`ParabolicChamberLinearAlgebraStatement.{u} ∧
ParabolicSplitComponentChamberStatement.{u}`.

The implemented proof is the conjunction constructor applied to:

- `parabolicChamberLinearAlgebra.{u}`, imported from
  [ParabolicChamberLinearAlgebraProof](ParabolicChamberLinearAlgebraProof.md);
- `parabolicSplitComponentChamber.{u}`, imported from
  [ParabolicSplitComponentChamberProof](ParabolicSplitComponentChamberProof.md).

Each imported theorem proves the corresponding conjunct at the same universe
parameter `u`. Pairing them proves the named target without additional
premises. All chamber mathematics is supplied by those published proofs;
this module contributes only their conjunction.

The scope remains that of the published statements: an arbitrary field `k`,
a connected reductive group scheme `G`, a maximal split torus
`i : T.toGrp ⟶ G`, a generic cocharacter `ν`, and supplied integral relative
reflection data `D`. Only standard parabolics are treated, encoded by sets
`J ⊆ simpleRelativeRoots i ν`. In the ambient space `𝔞^*_∅`, restrictions
`α|_{𝔞_M}` and `ϖ_α|_{𝔞_M}` are realized by projections to `𝔞^*_M` along
`span J`. Fundamental weights and coweights use the published predicates
`IsRealFundamentalWeight` and `IsRealFundamentalCoweight`.

For the split-component conjunct, the data further include a closed subgroup
`j : L ⟶ G` representing the standard Levi of `J`, a split component
`a : A.toGrp ⟶ L`, and a factor `f : A ⟶ T` satisfying
`CommGroupScheme.groupHom f ≫ i = a ≫ j`.

The target's source comparison is with David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`,
V.3.14–V.3.16, printed pp.113–114 / PDF pp.119–120. This assembly is derived
from the two Library proofs above; its provenance and scope are inherited
from the published target and its paired Markdown. The informal V.3.14
remarks that `Δ(P)` is in general not a set of simple roots and that `β̌` is
not a coroot are not formalized by the target or by this theorem.
