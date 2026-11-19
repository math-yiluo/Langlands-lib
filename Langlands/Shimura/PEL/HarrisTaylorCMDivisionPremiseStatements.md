# The three division-case premises of CM representability as closed statements

Worker 3269. This module packages the three premises of the published theorem
`divisionCMRepresentabilityStatement_of_criteria` (module
`HarrisTaylorCMDivisionCriteria`) as three closed `Prop` definitions. Proof
tasks can then target each premise exactly. The module proves that the three
statements together imply `DivisionCMRepresentabilityStatement`. It does not
prove any of the three statements, and it does not prove the target.

All declarations live in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry the same variables
and named prerequisite hypotheses as `DivisionCMRepresentabilityStatement` in
`HarrisTaylorCMDivisionRepresentabilityStatement`: the number fields `E`, `F`,
`L`, the algebra `A`, the central simple unitary data `D`, the signature
charts `C`, the named prerequisite statements `preservation` through
`polarizationStability`, the Weil transition compatibility `compatibility`,
the adelic comparison `h` and the torsion statement `htor`. Below, "…" stands
for that argument list. `SmallCMLevel D` is the Library type of small levels.
The per-level notions are those of `HarrisTaylorCMDivisionCriteria`, whose
Markdown explains them in detail.

## Statements

- `DivisionCMQuasiProjectiveRepresentabilityStatement …`. If `D.IsDivision`,
  then for every small level `U` there exist data
  `CMLevelQuasiProjectiveRepresentation … U`. Such data consist of a scheme
  over `Spec F`, an immersion of it into a finite projective space `ℙ^dim_F`
  over `Spec F`, and a natural isomorphism from its functor of points,
  restricted to the componentwise admissible test category, to the existing
  normalized class presheaf at `U`. No smoothness, properness or admissibility
  of the scheme is required.
- `DivisionCMArtinianLiftingStatement …`. If `D.IsDivision`, then
  `CMLevelArtinianLiftingStatement … U` holds for every small level `U`. Let
  `φ : B' →+* B` be a surjection of local Artinian rings in `Type` with
  `maximalIdeal B' * ker φ = ⊥`, and let `β : Spec B' ⟶ Spec F` be any
  structure morphism. Then every normalized class at level `U` over `Spec B`,
  with structure morphism `Spec φ ≫ β`, is the restriction of a class over
  `Spec B'`.
- `DivisionCMDiscreteValuativeExistenceStatement …`. If `D.IsDivision`, then
  `CMLevelDiscreteValuativeExistenceStatement … U` holds for every small
  level `U`. Let `V` be a discrete valuation ring in `Type` with fraction
  field `K`, and let `β : Spec V ⟶ Spec F` be any structure morphism. Then
  every normalized class at level `U` over `Spec K`, with structure morphism
  `Spec (algebraMap V K) ≫ β`, is the restriction of a class over `Spec V`.

Each statement is a `def` of type `Prop`. Each keeps the hypothesis
`D.IsDivision`, as the criteria theorem does. For the valuative statement
this is essential: without it the moduli space is expected to be non-proper,
and the statement is then expected to fail. The other two statements are
expected to hold without the division hypothesis. Keeping it makes them
weaker, so a proof without it still proves them, and the three statements
stay uniform.

## Theorem

- `divisionCMRepresentabilityStatement_of_premiseStatements hrep hlift hval`.
  If the three statements hold, then `DivisionCMRepresentabilityStatement …`
  holds. The Lean proof is the published
  `divisionCMRepresentabilityStatement_of_criteria hrep hlift hval`. The three
  definitions unfold to exactly its three hypotheses.

## Expected sources of proofs

None of the three statements is proved here. Their expected routes are:

- Quasi-projective representability: the PEL locus over the ordinary
  polarized moduli scheme (Task 3449), then level comparison and finite
  quotients.
- Artinian lifting: deformation theory of the PEL data, that is, lifting of
  abelian schemes with their polarization, `A`-action, Lie determinant
  condition and level structure along square-zero thickenings.
- Discrete valuative existence: in the division case, potentially good
  reduction and Néron extension of the abelian variety with its PEL
  structure.

These are informal counterparts of the representability, smoothness and
projectivity steps of Kottwitz, *Points on some Shimura varieties over finite
fields* (1992), §5, pp.390–392 (`kottwitz-1992-points-shimura-finite-fields`),
in characteristic zero. The Lean statements are not transcriptions of those
statements.

## Provenance

Internal. The three definitions restate, without change, the hypotheses of
the published theorem `divisionCMRepresentabilityStatement_of_criteria`. No
literature definition is transcribed. The compiled axioms of the theorem are
`propext`, `Classical.choice` and `Quot.sound`.
