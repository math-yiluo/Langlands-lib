# Proof of heterogeneous three-block induction associativity

Author: Worker 832.

This module proves the Library proposition
`Langlands.Parabolic.ThreeBlockInductionAssociativityStatement.{uF, uV0, uV1, uV2}`
as the theorem `Langlands.Parabolic.threeBlockInductionAssociativity`. The
statement is unchanged, with all four universe parameters independent. For
positive ranks `C`, `A`, `B` and smooth complex representations `ρ0`, `ρ1`,
`ρ2` of `GL_C(F)`, `GL_A(F)`, `GL_B(F)` on carriers in independent universes,
the theorem proves `Nonempty` of an actual `Representation.Equiv`. Its source
is the normalized induction `ρ0 × (ρ1 × ρ2)`, built literally from
`canonicalNormalizedProductInduced`, `Shahidi.twoBlocks` and
`Shahidi.pairFamily` with the statement's `ULift` conjugations. That action is
precomposed with the entry-preserving rank transport along `Nat.add_assoc`.
The target is the normalized induction `(ρ0 × ρ1) × ρ2`.

## Implemented proof

The proof is a composition of three published results:

1. `Langlands.Parabolic.orderedProductRegrouping` from
   `OrderedProductRegroupingProof`, used at carrier universe
   `max uF uV0 uV1 uV2` for every `F` with
   `T = F.canonicalTopologicalData`. It is the general ordered regrouping of
   normalized GL products.
2. `commonUniverseThreeBlockAssociativity_of_regrouping` from
   `ThreeBlockRegroupingAssembly`, at carrier universe `max uV0 uV1 uV2`. From
   that regrouping hypothesis it proves the common-universe proposition
   `CommonUniverseThreeBlockAssociativity.{uF, max uV0 uV1 uV2}`. It regroups
   the three-block product into each bracketing, using the three-block
   refinement data of `ThreeBlockRefinementGeometry`, and joins the two
   regroupings by the rank cast along `Nat.add_assoc C A B`.
3. `threeBlockInductionAssociativity_of_common` from
   `ThreeBlockUniverseReduction`. It reduces the literal heterogeneous
   statement, with its eight `ULift` conjugations at the four induction
   nodes, to the common-universe proposition at carrier universe
   `max uV0 uV1 uV2`.

No hypothesis is added: the theorem has no irreducibility, admissibility,
finite-length, unitarity or supplied-isomorphism assumptions. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal composition of Library constructions. The mathematical content,
the regrouping of normalized parabolic induction in stages, is carried by
`orderedProductRegrouping`. Bernstein–Zelevinsky (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, printed pp. 444–446, supplies the
normalization and induction-in-stages context. This module adds no new
mathematics beyond the composition described above.
