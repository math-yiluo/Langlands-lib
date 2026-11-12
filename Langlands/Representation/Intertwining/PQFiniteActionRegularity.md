# Spectral regularity for finite action algebras

Author: Worker 154. Module
`Langlands.Representation.Intertwining.PQFiniteActionRegularity`, namespace
`Langlands.PQFiniteActionRegularity`.

`actionQuotient ρ` is the commutative group algebra `ℂ[B]` modulo the actual
action kernel. When the action quotients of two representations are finite
over `ℂ`, `sup_kernels_eq_top_iff` proves that their kernels are comaximal
exactly when their generalized-character sets are disjoint. The carriers of
the representations have independent universes and need not be finite over
`ℂ`. Finite action quotients are explicit premises, not consequences of a
finite-length assumption in this module.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VII.3.3, regularity Lemma and proof, printed pp.234–235 /
PDF pp.240–241. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read both pages.

The provenance is derived. The source deduces the converse implication from
finite sets of exponents and annihilator ideals bounded by powers of their
character-kernel intersections. This module implements an alternative finite
commutative-algebra argument. It reuses the published finite-algebra
character and decomposition theorems in `Exponents.CentralDecompositionAlgebra`.
It supplies the spectral comaximality criterion under finite action-algebra
hypotheses, while retaining the application-specific proof that these
hypotheses follow from finite length.

## Implemented argument

`finite_actionQuotient_of_finite_span` identifies a useful sufficient
condition for the finite action-algebra hypothesis. Every group-algebra
operator belongs to the linear span of the actual group-action operators,
by linear induction. The faithful quotient action therefore embeds linearly
into that span. Finiteness of the span implies finiteness of the action
quotient. This condition does not require finiteness of the carrier.

`generalizedCharacter_of_faithful_algebra` takes a finite commutative complex
algebra `R` acting faithfully, a group map `τ : B → R` whose image acts by
the original representation `ρ`, and a scalar algebra character `ψ` of `R`.
The published decomposition theorem supplies elements `hφ`, indexed by the
finitely many scalar characters, whose sum is a unit and which are killed
by a fixed power of the corresponding character kernel. A separating
element for `φ ≠ ψ` shows that `ψ(hφ) = 0`. Since the sum is a unit,
`ψ(hψ) ≠ 0`, hence faithful action makes `hψ` act nontrivially. Choose a
vector with nonzero image under `hψ`. Every group-character defect for `ψ`
lies in its algebra-character kernel, so the fixed power kills that image.
It is a nonzero generalized-character vector. Neither generation of the
algebra by `τ` nor a topology is needed for this assertion.

`generalizedCharacter_of_actionQuotient` specializes the lemma to the actual
quotient action, using the injective algebra map furnished by the first
isomorphism theorem. The group map consists of the classes of the group
algebra basis elements.

For `sup_kernels_eq_top_iff`, the forward implication uses the kernel-to-
character containment lemma from `PQKernelCharacters`. For the converse,
a proper sum of the two action kernels gives a nonzero quotient algebra
`S`. It is finite-dimensional because it is a quotient of either finite
action algebra. A maximal ideal of `S` is the kernel of a scalar complex
character by the published algebra theorem. Pulling this character to both
action algebras gives generalized group characters in both representations;
they agree because they factor through the same `S`. This contradicts
disjointness and proves comaximality.

## Retained application obligations

This is an auxiliary construction for Task 5300. It does not prove
`PQRegularityLemmaStatement` or infer finite action algebras from its
finite-length premise. The exact application must still provide the
geometric support quotient filtration, identify its grades with the
specified intersection pieces with the same action, justify their finite
action algebras in the finite-length case, and relate the algebraic
character predicate to the published compact-open weight predicate.

The imports are `Intertwining.PQKernelCharacters` and
`Exponents.CentralDecompositionAlgebra`. The former helper pair is included
unchanged as a repository dependency because it is a newly staged unit.
The original task statements and their imported closure remain unchanged.
