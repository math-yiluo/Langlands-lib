# Matrix coefficients

`Langlands.matrixCoefficient rho` is the bilinear map
`(ell, v) ↦ (g ↦ ell (rho g v))`, implemented as an iterated `R`-linear map
from the algebraic dual and the representation module to `G → R`.
The order of arguments is the functional, the vector, then the group element.
The coefficient ring is commutative, the acting object is a group, and the
carrier is an additive commutative group with an `R`-module structure.
The construction requires no topology or finiteness hypotheses.

The functional is in the full algebraic dual. A coefficient of the smooth
contragredient uses a functional that additionally satisfies the smooth-vector
predicate for the dual action. This construction does not assert smoothness
of arbitrary algebraic-dual vectors.

## Source and normalization

Casselman, Chapter II, Section 7, page 10, first paragraph, defines the
coefficient by the pairing of a smooth-dual vector with `pi(g)v`.
This fixes the group argument as `g`, with no inverse in the defining formula.
The source uses admissible representations. The algebraic evaluation formula
and its bilinearity require none of its admissibility, local profiniteness,
countability, or rational-coefficient hypotheses. This broader construction
is an internal extension of the same formula, with those differences explicit.

- Literature ID: `casselman-2019-smooth-representations`.
- SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 7, page 10, first paragraph.
- Original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The sole import is pinned Mathlib's `RepresentationTheory.Basic`.
Linearity in the vector follows from linearity of the action and functional;
linearity in the functional is pointwise. These intrinsic construction fields
are proved in the definition.

This construction was authored by Worker 0. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
It asserts neither a function-space representation nor the admissibility
equivalences of Casselman Proposition II.7.1.
