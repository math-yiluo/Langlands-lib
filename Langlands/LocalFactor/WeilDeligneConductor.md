# The Weil–Deligne conductor at a supplied finite inertia quotient

Worker 20 connects the actual finite-Galois ramification sums with the actual
invariant quotient of a Weil–Deligne pair. The pair is the parameter
definition layer's `WeilDeligneRepresentation`, including its actual
representation, monodromy, nilpotence and covariance. A normal subgroup
`I` of the represented group is supplied explicitly.

The further inputs are a finite p-adic field `L`, its supplied topological
realization `T`, a base field `F` with its scalar tower, and a surjective
homomorphism from `I` to `Langlands.Ramification.Padic.inertia T F`.
That target is the kernel of the actual residue-field action. The caller
proves that the homomorphism's kernel acts trivially on the representation.
These inputs are retained in the constructor's telescope. Neither existence
of this quotient for the actual local Weil group nor independence from a
different finite quotient is asserted or assumed globally.

`artinConductorOfInertiaQuotient` is

`a(r; supplied finite quotient) + dim(V^I / (ker N)^I)`.

The first term is the published terminating ramification sum for the
descended representation, using the real lower ramification subgroups and
their cardinalities. The second term is the dimension of the actual
quotient representation constructed in `LocalFactor.WeilDeligne`.
`swanConductorOfInertiaQuotient` is the underlying representation's
finite-quotient Swan sum, with no added monodromy term.

The implementation proves that the corrected Artin expression is also

`dim(V) - dim((ker N)^I) + Swan(r; supplied finite quotient)`.

The proof identifies the fixed space after descent with the original
`I`-fixed subspace, applies the finite-inertia tame-plus-Swan identity, and
uses the proved quotient dimension formula. The bound `dim(V^I) <= dim(V)`
justifies cancellation in natural-number subtraction before passing to
rationals. This proof imposes no additional hypothesis on monodromy.

A genuine pair equivalence restricts to an equivalence of the `I`-actions.
The finite-quotient kernel condition transports along this equivalence.
The corrected Artin and Swan expressions are invariant under it, with
independent source and target carrier universes. When monodromy is zero,
the actual quotient dimension is zero and the corrected Artin expression
reduces to the original finite-quotient Artin expression.

## Sources and boundaries

John Tate, *Number Theoretic Background*, in the Corvallis proceedings,
Part II (1979), section 4.1.6, printed page 21 (retained PDF page 30),
defines the Weil–Deligne conductor by
`a(r,N) = a(r) + dim(V^I) - dim((ker N)^I)`. The original page was read
and visually checked. Source `tate-1979-number-theoretic-background`,
SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
retained at
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

The finite sum is the construction sourced to Serre, *Local Fields* (1979),
Chapter VI, section 2, Proposition 2 and Corollary 1', printed pages 100–101,
retained PDF pages 107–108. Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original pages 99–101 were read for the descent connection. Only the
weighted-codimension expression and its intrinsic dimension identities
are used, not the Artin-character integrality or quotient-independence
theorems.

Lean uses arbitrary coefficient fields and rational finite expressions.
Their interpretation as the usual integral complex Artin/Swan conductors
requires the classical hypotheses and later theorems. No expression is
silently rounded to an integer.

The project imports are `Langlands.LocalFactor.Ramification.Descent`
and `Langlands.LocalFactor.WeilDeligne`. The latter retains the parameter
owner's actual kernel and invariant constructions. The underlying
ramification modules, Descent, and the parameter kernel module and its
Basic and Invariants imports are published in the current Library. The WD
construction pair is included with this conductor pair for independent
review and publication.
No actual local Weil-group constructor, reciprocity map, nonabelian
epsilon system, self-dual measure or functional equation is postulated.
