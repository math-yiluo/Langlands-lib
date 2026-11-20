# Casselman's criterion from Bruhat–Tits availability

`Langlands.Aubert.General.RepresentedParabolic.CasselmanFromBuildingStatement`
states the corrected Renard VII.1.2 biconditional under the published
`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`. That
premise is existence of an actual assignment of building and
integral-model data satisfying the ten corrected Kaletha–Prasad
availability axioms over the nonarchimedean local fields of
universe `u`. The conclusion is the existing
`ArbitraryParabolicCasselmanCriterionStatement.{u,v}` at independent
field and representation-carrier universes.
[Building premise](../../Geometry/Building/BruhatTitsAvailabilityStatement.md) · [Criterion](ArbitraryParabolicCasselmanStatement.md)

For every admissible smooth complex representation with unitary
central character and every displayed quotient Haar measure, the
criterion identifies square integrability modulo the full center with
strict positivity of the simple-root coefficients of each normalized
Jacquet exponent, tested in each compatible root presentation.
It uses the \(q^{-s}\) real part and the strict root cone from the final
decay test of Renard's proof. The positivity condition and all
quantifiers come from the published criterion.

Renard uses the Cartan decomposition and simultaneous compact-open
Iwahori bases of V.5.1–2. The Library obtains these at a common special
vertex from a valid assignment and the published simultaneous basis
theorem. The sufficiency reduction takes this joint structural result
as input. The necessity theorem holds independently. This proposition
packages the resulting biconditional with the building existence
premise visible.
[Joint structural assembly](../../BruhatTits/SpecialCompact/JointBasisFinalAssembly.md) · [Sufficiency reduction](CasselmanSufficiencyReduction.md) · [Necessity](CasselmanNecessity.md)

The unconditional `ArbitraryParabolicCasselmanCriterionStatement`
remains the exact target of Task 4712
(`2e8d370f-f1ed-4ad4-a529-5083212ebae0`).

Source. David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026. VII.1.2, printed pp. 221–224
(PDF pp. 227–230), and V.5.1–2, printed pp. 122–123
(PDF pp. 128–129). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
