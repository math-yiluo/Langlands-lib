# Jacquet Hom multiplicity one and irreducible induction

This derived helper module constructs
`Langlands.Aubert.General.jacquetScalarEquiv` for the actual normalized
induction and normalized Jacquet functors. It also proves their multiplicity-one
irreducibility criterion. Its generic topological-group hypotheses include
local compactness, the nonarchimedean group property, a semidirect decomposition
`P = M U`, a closed radical `U`, and unimodularity of the radical's conjugation
modulus. Group and representation-carrier universes are independent.

## Provenance

This is internal linear algebra and a derived consequence of the published
`FirstAdjointness.equiv`,
`RepresentedParabolic.exists_nonscalar_endomorphism_of_semisimple`,
`nontrivial_normalizedInduction` and `admissibleUnitarySemisimplicity`.
It implements the scalar-endomorphism step relevant to Waldspurger IV.2.2(i),
but makes no new source-based assertion about actual Jacquet multiplicities.

## Construction and results

Write `I σ` for the actual normalized induced object and `J(I σ)` for its
actual same-parabolic normalized Jacquet module. `jacquetScalarMap` is the
complex-linear map

`c ↦ FirstAdjointness.equiv (c • id) : Hom(J(I σ), σ)`.

Thus `1` maps to the actual descended evaluation counit. If `I σ` is nonzero
and the cardinal-valued complex dimension of `Hom(J(I σ), σ)` is at most one,
`jacquetScalarMap_bijective` proves this map bijective and
`jacquetScalarEquiv` packages the resulting linear equivalence with `ℂ`.
The bound is on `Module.rank`, so the argument does not use the finrank value
zero of an infinite-dimensional space.

`exists_scalar_of_rank_endomorphism_le_one` first proves the corresponding
fact for the endomorphism space of any nonzero smooth representation. A
generator exists because its dimension is at most one; its multiple equal to
the nonzero identity has a nonzero scalar coefficient, so every endomorphism
is a scalar identity.

`isIrreducible_of_semisimple_rank_endomorphism_le_one` then applies the published
projection argument: a nonzero reducible semisimple object would have a
nonscalar endomorphism, contradicting that scalar description.

`isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one` transfers the
Jacquet Hom dimension bound to the endomorphism space through the actual
complex-linear first-adjointness equivalence and applies this criterion.
It assumes nonzeroness of induction explicitly.

`isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` instead assumes a
nonzero inducing object and continuity of its actual Levi projection, which
make induction nonzero by the published local-section theorem. Admissibility
and unitarizability of induction, with cofinal compact open subgroups of the
ambient group, give semisimplicity. The same multiplicity-one bound then gives
irreducibility without a finite-length premise.

## Remaining consumer obligations

The bound on `Hom(J(I σ), σ)` is a hypothesis here. It is not derived from
square integrability, regularity, a geometric lemma, or a weak-Jacquet
decomposition. Likewise, this module does not establish unitarizability of
induction, its admissibility, compact-open cofinality or any actual reductive
group's structural hypotheses. These have to be proved or supplied by the
consumer's unchanged statement. This module alone does not prove generic
irreducibility for any family of unramified twists.
