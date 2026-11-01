# A common triangular basis for each actual generalized-weight block

Worker 438 wrote this proof of the unchanged Library proposition
`Langlands.CommutingTupleGeneralizedWeightBlockBasisStatement.{u}`.
The main theorem is
`Langlands.commutingTupleGeneralizedWeightBlockBasis`, whose entire type is
that proposition, with arbitrary carrier universe `u`.

## The actual operators

For a natural rank `d`, a finite-dimensional complex vector space
`V : Type u`, a commuting invertible tuple `A` and unit labels
`c : Fin d → ℂˣ`, the proof uses the unchanged constructions of
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock`.
In the namespace `Langlands.IntegerLattice`, these are

```text
W   = generalizedWeightBlock A c
    = ⋂ t, (A.1 t).maxGenEigenspace (c t : ℂ),
G_t = generalizedWeightBlockGenerator A c t,
N_t = normalizedGeneratorDifference A c t.
```

`G_t` is the actual unit obtained by evaluating the restricted lattice
representation at the standard generator. Its underlying map on `W` acts
in `V` as `A.1 t`. The normalized difference acts in `V` as
`(c t : ℂ)⁻¹ • A.1 t - 1`. No replacement operators, supplied basis or
decomposition are introduced.

## Commutation and nilpotence

The three helper theorems are in `Langlands.IntegerLattice`.

`generalizedWeightBlockGenerator_commute` rewrites both underlying block
generators as values of `generalizedWeightBlockRepresentation A c`.
The standard generators commute in the abelian integer lattice, and
mapping this equality through the restricted representation proves
commutation of the block generators.

`normalizedGeneratorDifference_commute` rewrites the normalized generators
as inverse-label scalar multiples of the block generators.
`Commute.smul_left`, `Commute.smul_right`, `Commute.sub_left` and
`Commute.sub_right`, with commutation of the identity, then prove pairwise
commutation of the actual differences. These two helpers need no
finite-dimensionality.

`normalizedGeneratorDifference_isNilpotent` uses finite dimension.
Fix `t`, set `f = (A.1 t : Module.End ℂ V)` and `μ = (c t : ℂ)`.
The block is invariant under `f`, by the existing invariance theorem at
the standard generator, and under scalar multiplication. It is therefore
invariant under `f - μ • 1`; the proof calls this invariance `hW`.
Membership in the intersection gives
`W ≤ f.maxGenEigenspace μ`.

Mathlib's `Module.End.isNilpotent_restrict_genEigenspace_top` proves that
`f - μ • 1` restricted to the maximal generalized eigenspace is nilpotent.
`Module.End.isNilpotent_restrict_of_le` passes this nilpotence to its
restriction to `W`. The proof next verifies the equality of actual maps

```text
N_t = μ⁻¹ • ((f - μ • 1).restrict hW).
```

It checks this on each block vector after coercion to `V`, using
`normalizedGeneratorDifference_apply_coe` and `μ ≠ 0`, supplied by the unit
label. `IsNilpotent.smul` now gives nilpotence of `N_t`. Thus nilpotence and
commutation are conclusions proved from the tuple and block, rather than
additional hypotheses.

## One basis and all five conclusions

The main theorem applies the published result
`Langlands.CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis`
from `Langlands.LinearAlgebra.CommutingNilpotentStrictUpperBasisProof`
to the family `normalizedGeneratorDifference A c : Fin d → Module.End ℂ W`.
The two preceding helpers discharge its commutation and nilpotence
hypotheses. This gives one basis
`b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W` and

```text
b.repr (N_t (b j)) i = 0  whenever j ≤ i.
```

The existential basis precedes every generator and coordinate quantifier.
The second target clause is the existing intrinsic identity
`generalizedWeightBlockGenerator_eq_smul`:
`G_t = (c t : ℂ) • (1 + N_t)`.
Applying `b.repr` and taking coordinate `i`, linearity and
`Module.Basis.repr_self_apply` give the third clause,

```text
b.repr (G_t (b j)) i =
  (c t : ℂ) * ((if i = j then 1 else 0) + b.repr (N_t (b j)) i).
```

For `j < i`, strict upper triangularity makes the difference coordinate
zero, and `i ≠ j` makes the identity coordinate zero. This proves the
fourth clause. At `j = i`, the difference coordinate is zero and the
identity coordinate is one, giving the fifth clause, the scalar diagonal.
Rows are indexed by `i` and columns by `j`.

## Scope and provenance

The theorem retains every natural rank, all unit label tuples, arbitrary
carrier universe and every finite-dimensional complex space. At rank zero
the family is empty, and the generic theorem still supplies an actual basis
of the block, which is the whole space. For a zero space or zero block,
the finite basis is empty. The proof uses no nonzero-space, positive-rank,
nonzero-block, diagonalizability or unitarity assumption.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix C.III,
printed pp.279–280 / one-based PDF285–286. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both pages were read and PDF286 was visually checked. Its first display
writes the generator of a chosen matrix block as the scalar label times
the identity plus a strictly upper triangular matrix.

This proof supplies the published statement's derived intrinsic
formulation on the actual generalized-weight intersection. Renard chooses
a common matrix basis directly. The implemented route first proves
nilpotence on the actual block from generalized eigenspaces, then applies
the separately published generic common-basis theorem. The internal
restriction and commutation helpers explain that bridge; they are not
additional assertions quoted from the source.

The registered supplementary 2010 errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
are retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
PDF18–19 were read. The C.III correction on PDF19 groups the full
scalar-times-unipotent factor under its integer power. The 2026 display
already has that grouping, and it changes none of the five clauses proved
here.

This result does not assemble a global basis, identify nonzero blocks
with common eigenvalue labels, prove the generalized-weight decomposition
or supply the multivariable product expansion. Those are separate results
or obligations. The generic common-basis proof is imported unchanged;
its independent task ownership is preserved.

## Validation

The complete proof compiled without errors or warnings in approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Lake build and declaration inspection
`480d1799-8725-46e2-8e4a-f00fa2484676` report the single universe parameter
`u` and only `propext`, `Classical.choice` and `Quot.sound`.
This is development evidence; independent semantic review and official
exact-target validation remain required for publication.
