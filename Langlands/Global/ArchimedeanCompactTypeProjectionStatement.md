# Continuous projections onto actual archimedean compact types

Author: Worker 94.

The proposition `Langlands.Global.ArchimedeanGL.CompactTypeProjectionStatement K n`
uses only the published actual compact subgroup, its action on
`DerivativeSmoothFunctions K n`, and its algebraic compact-type submodules
from `Langlands.Global.ArchimedeanCompactTypes`. It applies to every number
field in arbitrary universe and every natural rank, including zero.

For every actual irreducible continuous compact representation `σ`, it
asserts the existence of one continuous complex linear endomorphism `P`
of the full derivative smooth-function space such that:

- every value of `P` belongs to `compactTypeSubmodule σ`;
- `P` fixes every element of that submodule;
- `P` commutes with every actual compact right translation;
- for every input `f`, `P f` belongs to the topological closure of the
  complex linear span of the actual compact orbit of `f`.

The first two clauses say that the range is exactly the published
algebraic isotypic span and that `P` is a projection. The last clause is
essential for the intended application: it implies preservation of any
closed compact-invariant complex subspace. When the compact orbit of an
input spans a finite-dimensional space, the same clause puts its
projection in that finite-dimensional orbit space. These are
consequences to prove, rather than additional assumptions on the input.
No finite multiplicity, finite dimension of the whole isotypic span,
compact finiteness, center finiteness or analyticity is assumed.

This is an internal specialization and specification of a missing
analytic prerequisite. Its motivating source is Harish-Chandra,
*Discrete series for semisimple Lie groups II*, section 2, printed/PDF
page 8: integration of the conjugate character, multiplied by its degree,
gives a continuous compact-type projection in a complete locally convex
representation. Section 5, printed/PDF page 13, gives the corresponding
right action on smooth functions. The registered source is
`harish-chandra-1966-discrete-series-ii`, retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Discrete series for semisimple Lie groups II- Explicit determination of the characters (1966).pdf`.
The present exact number-field formulation, algebraic range
identification and orbit-closure clause are internally derived; this
module does not transcribe the source's full general theorem.

Only a proposition is defined here. In particular, no integral into the
derivative topology, completeness theorem, Schur orthogonality theorem
or Peter–Weyl decomposition is assumed as a certificate. A proof must
construct the endomorphism and establish all four clauses for the
published actual objects. Admissibility of a generated enveloping
module, extension from a dense algebraic module to its closure,
compact-central convolution preservation and exact reproduction remain
separate obligations. This statement does not prove orbit density or
automorphic differential growth.
