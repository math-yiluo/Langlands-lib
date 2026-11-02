# Finite étale algebras over a discrete Noetherian spectrum

Author: Worker 122.

This internal helper supplies the algebraic finiteness step in the proposed
finite-orbit proof for nonzero groupoid invariants. It derives its results
from Mathlib and does not assert the existence of an invariant closed subset,
an invariant ideal, a restricted relation, or a nonzero invariant.

`isArtinianRing_of_discrete` applies Mathlib's equivalence between discreteness
of a prime spectrum and finiteness together with Krull dimension at most zero.
The dimension assertion and Noetherianity imply Artinianity by the
Hopkins–Levitzki development. For a reduced ring, `equivPiOfDiscrete` then
uses Mathlib's Artinian decomposition into the quotients by maximal ideals.
These quotients are fields; `finite_maximalSpectrum_of_discrete` records
that the indexing type is finite. These results include the trivial ring,
where the product is empty.

`finite_projective_of_artinian` proves that an étale algebra over an
Artinian ring is finite and projective as a module. Étaleness implies
quasi-finiteness, and Mathlib proves that quasi-finite algebras over
Artinian rings are module-finite. Artinian rings are Noetherian, so a finite
module is finitely presented. Étale algebras are flat; a flat finitely
presented module is projective.

`finite_projective_of_discrete` combines these deductions for a Noetherian
base with discrete spectrum. It does not need the base to be reduced.
`finite_projective_of_etale_hom` states the same result for an arbitrary
étale ring map, using the algebra structure induced by that map.

This is derived internal content. Its mathematical inputs are the named
Mathlib results implemented in the Lean file; it makes no independent
literature claim.
