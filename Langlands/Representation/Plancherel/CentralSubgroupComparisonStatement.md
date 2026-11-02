# Coefficient comparison on the two actual central quotients

This internal comparison target connects the published Waldspurger-style
predicate on `G/A` with the existing full-center predicate on `G/Z(G)`.
Its motivation is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques*, III.1, printed p.263 (PDF p.29), which defines square-integrability
on `A_G \ G` with a unitary central character. I.1, printed pp.238–239
(PDF pp.4–5), identifies `A_G` as the rational points of the maximal split
central torus. This comparison is a derived analytic adapter, not an
assertion quoted from those passages. This file defines propositions and
supplies no proofs.

The input is a locally compact Hausdorff topological group `G`, an actual
normal subgroup `A`, a proof that `A` is contained in the full group center,
and a proof that `A` is closed. The compactness premise is

`CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))`.

Here `A.subgroupOf (Subgroup.center G)` is the actual inverse image of `A`
under the center inclusion. Since `A` is central, this is precisely `A`
regarded as a subgroup of the center. The quotient has its induced quotient
topology. Compactness of this quotient is an explicit premise of the
generic adapter; this target does not prove it for a reductive group.

`CentralQuotientCompactKernelStatement` states that the published actual map
`centralQuotientProjection A hA : G/A → G/Z(G)` is surjective and open, that
its homomorphism kernel is a compact subset of `G/A`, and that it is proper.
The map sends the class of `g` to the full-center class of the same `g`.
The compact-kernel assertion must be proved from the stated compact quotient
of the actual center, not supplied as an unrelated hypothesis.

`CentralSubgroupCoefficientLpComparisonStatement` additionally assumes that
`G` is second countable, both quotient measurable structures are their Borel
structures, and a Haar measure is supplied on each quotient. It has two
conclusions for every complex representation on an additive group `V`:

- For every prescribed unitary central character, every algebraic dual
  functional, every smooth vector and every extended nonnegative exponent,
  the actual coefficient norm on `G/A` belongs to `MemLp` exactly when the
  coefficient norm on `G/Z(G)` does.
- `IsSquareIntegrableModCentralSubgroup A hA ρ μA` is equivalent to the
  existing `Langlands.IsSquareIntegrableModCenter ρ μZ`.

There is no topology on `V` and its universe is independent of the group
universe. The first conclusion explicitly requires a smooth vector because
coefficient continuity is derived from smoothness. The second has no added
smoothness premise: both predicates include admissibility, which itself
includes smoothness, and quantify over every smooth-dual functional and
every vector. They also retain the same actual unitary central-character
witness. No irreducibility, finite length or unitarizability is required.

`CentralSubgroupSquareIntegrabilityComparisonStatement` is the conjunction
of these topology and analytic targets.

The intended proof composes the published
`UnitaryCentralCharacter.continuous_coefficientNorm` with the actual central
projection and applies the generic compact-kernel Haar/Lp comparison.
The coefficient on `G/A` is already defined as that exact pullback in
`CentralSubgroupCoefficients`. Haar pushforward and positive finite scalar
comparison justify the change of measure; the target does not assert that
arbitrarily chosen Haar measures make the projection measure preserving.

For the source specialization `A=A_G`, the actual split central subgroup,
its closedness, the rational-point topology, and compactness of
`Z(G)/A_G` remain separate structural-realization or derived proof
obligations. They are recorded in the program's structural ledger and
requested from the designated algebraic-group and rational-point programs.
No compactness assertion or desired analytic conclusion is thereby added to
the permitted external Renard Chapter V hypotheses. This proposition is
only the generic bridge after those premises are justified.
