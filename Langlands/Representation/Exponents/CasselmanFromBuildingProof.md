# Proof of Casselman's criterion under Bruhat–Tits availability

Module `Langlands.Representation.Exponents.CasselmanFromBuildingProof`. The theorem

```lean
theorem Langlands.Aubert.General.RepresentedParabolic.casselmanFromBuilding :
    CasselmanFromBuildingStatement.{u, v}
```

proves `CasselmanFromBuildingStatement` (module `CasselmanFromBuildingStatement`) at independent
field and representation-carrier universes `u`, `v`. The statement is the implication

```lean
Geometry.Building.BruhatTitsAvailabilityStatement.{u} →
  ArbitraryParabolicCasselmanCriterionStatement.{u, v}
```

In words: if some assignment of building and integral-model data to every connected reductive
group over every nonarchimedean local field of universe `u` satisfies the ten corrected
availability axioms (`BruhatTitsAvailabilityStatement`, module
`Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`), then the corrected criterion of
Renard VII.1.2 holds (`ArbitraryParabolicCasselmanCriterionStatement`, module
`ArbitraryParabolicCasselmanStatement`): for a connected reductive group `G` over a
nonarchimedean local field `k`, a Haar measure on `G(k)/Z(G(k))` and an admissible smooth complex
representation `π` with a unitary central character, `π` is square integrable modulo the centre
if and only if, for every actual rational parabolic with Levi, matching unipotent radical and
split component, every compatible root presentation and every normalized Jacquet exponent `χ`,
the normalized real part of `χ` lies in the strictly positive root cone. Its complete text is
given in the statement module.

## Proof as implemented

Assume the building premise `hBuilding`.

1. `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence_of_availability_and_basis`
   (module `Langlands.BruhatTits.SpecialCompact.JointBasisFinalAssembly`), applied to
   `hBuilding` and to the Library theorem `availableSimultaneousStandardBasis` (module
   `Langlands.BruhatTits.SpecialCompact.AvailableBasisProof`), gives
   `JointSpecialCompactBasisExistenceStatement.{u}`: a common special vertex with its Cartan
   decomposition and a simultaneous compact-open basis with Iwahori decompositions.
2. `arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis.{u, v}` (module
   `CasselmanSufficiencyReduction`) turns this into
   `ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}`, the reverse implication of the
   criterion.
3. For the field, group, Haar measure and representation of the criterion, the forward
   implication is `arbitraryParabolicCasselmanNecessity` (module `CasselmanNecessity`), which
   needs no building premise, and the reverse implication is step 2. The proof introduces the
   affine and smooth instances of `G` and the point topology of `G(k)` used by the statement and
   pairs the two implications.

## Declarations

- `casselmanFromBuilding : CasselmanFromBuildingStatement.{u, v}` (theorem).

## Provenance

D. Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques` (PDF page = printed page
+ 6):

- VII.1.2 "Critère de Casselman", Théorème, printed p. 221 (PDF page 227): a smooth admissible
  representation with unitary central character is square integrable modulo the centre if and
  only if, for every parabolic subgroup `P = MN` and every normalized exponent `χ` of `π` for
  `P`, `ℜ(χ) ∈ ^G_P[𝔞*_M]^+`; proof on printed pp. 221–224 (PDF pages 227–230).
- V.5.1 "Sous-groupes compacts maximaux", Théorème (4), the Cartan decomposition, printed p. 122
  (PDF page 128), and V.5.2 "Décomposition d'Iwahori des sous-groupes compacts ouverts",
  Théorème, printed p. 123 (PDF page 129): the structural results used in the proof of VII.1.2,
  which the Library obtains at a common special vertex from a valid building assignment
  (`JointSpecialCompactBasisExistenceStatement`).
