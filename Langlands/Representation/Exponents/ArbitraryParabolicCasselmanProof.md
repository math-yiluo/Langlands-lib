# Proof of Casselman's criterion for actual rational parabolics

Module `Langlands.Representation.Exponents.ArbitraryParabolicCasselmanProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. The theorem

```lean
theorem arbitraryParabolicCasselmanCriterion :
    ArbitraryParabolicCasselmanCriterionStatement.{u, v}
```

proves the published statement `ArbitraryParabolicCasselmanCriterionStatement`
(module `ArbitraryParabolicCasselmanStatement`, see
[its Markdown](ArbitraryParabolicCasselmanStatement.md)) at its own universes: `u`
for the field and `v` for the representation carrier. It adds no hypothesis.

## What is proved

Let `k` be a Hausdorff nonarchimedean local field of any characteristic and `G` a
connected reductive group over `k`. Give `G(k)` the canonical point topology,
assumed locally compact and nonarchimedean. Let `haar` be any Haar measure on
`G(k) ⧸ Z(G(k))` for a Borel measurable structure, and let `π` be an admissible
smooth complex representation of `G(k)` with a unitary central character. Then the
following are equivalent:

- `π` is square integrable modulo the center for `haar`
  (`IsSquareIntegrableModCenter`);
- for every actual rational parabolic `p` with rational Levi `l`, matching
  geometric unipotent radical `r` (multiplication an isomorphism) and split
  component `a`, every compatible `pres : ParabolicRootPresentation p l a` and
  every normalized Jacquet exponent `χ`, the `q^(-s)` real part
  `Plancherel.SplitTorus.normalizedRealPart … χ` lies in the strictly positive root
  cone `pres.positiveCone`.

This is Renard VII.1.2 with the corrected cone and the explicit real-part
normalization described in the statement's Markdown. Admissibility and the
unitary central character are the only hypotheses on `π`. There is no
irreducibility, finite-length, Jacquet-admissibility, Cartan-decomposition,
Iwahori-contraction or presentation-existence premise.

## Proof as implemented

The Lean term is

```lean
casselmanFromBuilding.{u, v} Langlands.Geometry.Building.bruhatTitsAvailability.{u}
```

- `casselmanFromBuilding : CasselmanFromBuildingStatement.{u, v}` (module
  `Langlands.Representation.Exponents.CasselmanFromBuildingProof`, see
  [its Markdown](CasselmanFromBuildingProof.md)) proves the implication
  `Geometry.Building.BruhatTitsAvailabilityStatement.{u} →
  ArbitraryParabolicCasselmanCriterionStatement.{u, v}`.
- `Langlands.Geometry.Building.bruhatTitsAvailability :
  BruhatTitsAvailabilityStatement.{u}` (module
  `Langlands.Geometry.Building.BruhatTitsAvailabilityProof`) proves its premise.
  It gives one assignment of building data to the connected reductive groups over
  nonarchimedean local fields of universe `u` that satisfies the corrected axioms
  of Kaletha–Prasad, Definition 4.1.26. Its proof is
  `bruhatTitsAvailabilityReduction groupAxiomsExistence`.

The module adds only this application. It uses the following published results,
all through `casselmanFromBuilding`:

1. **Structural input.**
   `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence_of_availability_and_basis`
   (module `JointBasisFinalAssembly`), applied to the availability theorem and to
   `availableSimultaneousStandardBasis` (module `AvailableBasisProof`), gives
   `JointSpecialCompactBasisExistenceStatement.{u}`. This is one special vertex of
   one apartment with its special compact subgroup `K₀`, the standard-Levi
   inheritance, the ambient and Levi Iwasawa products, the ambient and Levi Cartan
   comparisons and a simultaneous basis of `K₀` with Iwahori decompositions, all
   at the same witnesses. In Renard these are V.5.1 and V.5.2. The same term is the
   Library theorem `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`.
2. **Sufficiency.**
   `arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis.{u, v}`
   (module `CasselmanSufficiencyReduction`) turns step 1 into
   `ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}`, the right-to-left
   implication. It goes through the strict Jacquet square-integrability statement
   and the published sufficiency assembly. The standard-parabolic presentations
   that the reverse implication needs come from
   `standardCasselmanPresentationOfGeometry` (module
   `CasselmanStandardPresentationConstruction`), built from a maximal split torus
   and a generic cocharacter. They are constructed, not assumed.
3. **Necessity.** `arbitraryParabolicCasselmanNecessity` (module
   `CasselmanNecessity`) is the left-to-right implication. It uses no structural
   premise.

`casselmanFromBuilding` introduces the binders of the criterion: the affine and
smooth instances of `G` from `hG`, and the point topology of `G(k)`. It then pairs
the necessity and sufficiency implications.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VII.1.2
"Critère de Casselman", printed pp.221–224 / PDF pp.227–230. Renard's proof uses
the Cartan decomposition (V.5.1, printed p.122 / PDF p.128), the Iwahori
decomposition of compact open subgroups (V.5.2, printed p.123 / PDF p.129) and
Casselman's asymptotics (VI.9). The implemented route takes the structural input
from the Bruhat–Tits availability theorem as in step 1. The building axioms follow
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 4.1.26, in
the authors' corrected form. The statement's Markdown explains how its cone and
real part differ from the printed statement.
