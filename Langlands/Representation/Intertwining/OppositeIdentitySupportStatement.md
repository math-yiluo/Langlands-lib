# The identity support image for opposite rational parabolics: statement

Author: Worker 135. This module defines the closed proposition
`Langlands.Aubert.General.RepresentedParabolic.OppositeIdentitySupportStatement`
and proves nothing. The local-field universe `u` and inducing-carrier universe
`v` are independent.

## Mathematical content

For a connected reductive group over a nonarchimedean local field, let `P=MN`
and `Q=MU` be represented rational parabolics whose embeddings of `M` in `G`
agree and whose rational-point intersection is exactly that common Levi.
For every smooth complex representation `sigma` of `M(F)`, the statement
asserts an equivariant linear equivalence between `sigma` and the identity
support image `F^{<1}_{PQ}(sigma)` in `r_Q i_P(sigma)`.

The support image is the published `boundarySupportImage` at
`identityParabolicDoubleCoset`. Its carrier is a subspace of the actual
normalized Jacquet module. The statement asks only for the existence of a
representation equivalence. It does not choose or normalize an integral,
assert naturality, or impose admissibility, finite length, irreducibility,
temperedness, a standard parabolic or a root presentation.

## Source and derivation

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 135 read VII.3.1–VII.3.3, printed pp.232–234 / PDF pp.238–240, and
VII.4.1, printed pp.241–242 / PDF pp.247–248.

This is a derived prerequisite, rather than a separately numbered assertion
of the book. VII.3.2 identifies `F^{<1}_{PQ}/F^{<=1}_{PQ}` with the identity
functor. For opposite parabolics the identity double coset is the largest
Bruhat cell (VII.3.1), its closure is all of `G(F)`, and
`F^{<=1}_{PQ}=0`. The quotient comparison therefore becomes the equivalence
stated here. This is also the identity-piece input used in the last paragraph
of the VII.4.1 Lemma's proof.

The opposite-parabolic convention matches the published VII.4.1 target:
the two Levi morphisms have the same composite into `G` and
`pointImage p` intersected with `pointImage q` is `pointImage(l >> p)`.
The generality of arbitrary rational parabolics follows the convention
explicitly described at the start of VII.3.1: the standard-Levi restriction
there is only for notation, and the results transport by conjugation.

## Retained proof obligation

One must prove the actual support-image equivalence, including the geometric
opposition and support-quotient comparisons. The source argument above is not
a Lean proof. `PQSupportGradedStatement` already states the quotient comparison
for general pairs with the same Levi, but is itself unproved; this statement
isolates only the opposite identity-image case needed by Task 5282.
