# Preservation obligations for actual automorphic forms

This statement group concerns the published complex-valued automorphic forms
on the actual adelic matrix group over any number field `K : Type u`, for every
natural rank `n`. All four obligations are proposition definitions, not assumed
preservation laws or proved deep theorems. The namespace is
`Langlands.Automorphic`.

## Exact declarations and quantifiers

Write `D(a) = finiteSmoothEnvelopingAction K n a`, with
`a : Langlands.Global.ArchimedeanGL.EnvelopingAlgebra K n`. This is the published
complex enveloping-algebra action on `FiniteSmoothRationalFunctions K n`.
Its slice at any finite adelic matrix `b` is the genuine archimedean
differential of the original slice. On a real Lie generator `X`, it differentiates
in the matrix direction `g * X`, the convention obtained from right translation.
No abstract action or differential-preservation certificate is a parameter.

* `AutomorphicDifferentialInfiniteFiniteStatement K n` states that for every
  `a` and every `f : AutomorphicForms K n`, the continuous function underlying
  `D(a) f.val` satisfies `IsInfiniteFinite` at
  `Langlands.Global.standardInfiniteCompact K n`. Its translates by that
  specific orthogonal/unitary subgroup have finite-dimensional complex span.
* `AutomorphicDifferentialGrowthStatement K n` states that the same output,
  for every `a` and every actual automorphic `f`, satisfies
  `HasPolynomialGrowth`. Explicitly, for each finite adelic matrix `b`, there
  exist a real constant `C ≥ 0` and a natural exponent `d` bounding its absolute
  value at every infinite adelic matrix `g` by
  `C * ArchimedeanGL.matrixHeight K n g ^ d`. These constants may depend on
  `a`, `f`, and `b`. There is no uniform exponent or unchanged growth bound
  asserted. In particular the input retains compact finiteness and simultaneous
  center finiteness; this is not a statement about arbitrary smooth functions
  of polynomial growth.
* `AutomorphicDifferentialPreservationStatement K n` states that for every `a`
  and every `f : FiniteSmoothRationalFunctions K n`, membership of `f` in
  `automorphicSubrepresentation K n` implies membership of `D(a) f` in that
  same subspace. This is precisely the closure obligation for restricting the
  concrete differential to the actual form space.
* `AutomorphicCompactTranslationStatement K n` quantifies over every
  `k : standardInfiniteCompact K n` and every
  `f : SmoothRationalFunctions K n`. If `IsAutomorphicForm K n f`, then
  `IsAutomorphicForm K n
  (smoothRightAction K n (AdelicGL.ofInfinite K n k.val) f)`.
  At an adelic matrix `x`, the translated function has value
  `f(x * AdelicGL.ofInfinite K n k.val)`. The translating element is in the
  specified infinite compact subgroup; arbitrary infinite translation is not
  asserted to preserve the compact-finite form space.

`AutomorphicPreservationStatement K n` is the conjunction of these four
propositions in the order above. Each component can serve as an independent
proof target. Full-telescope examples check that all five declarations have
type `(K : Type u) → [Field K] → [NumberField K] → ℕ → Prop`, including the
arbitrary universe and rank.

The actual space and predicate are those of `Forms`. They impose joint
continuity, rational left invariance, real smoothness at infinity, one compact
open finite level, finiteness under the standard infinite compact subgroup,
simultaneous center finiteness of all slices, and polynomial growth separately
on each finite slice. The published `mem_automorphicSubrepresentation` identifies
the membership and predicate presentations. Center finiteness is equivalent
to one finite-codimensional ideal of the complex enveloping center annihilating
every slice; it is not a collection of unrelated ideals for individual slices.

## Source correspondence and derived content

The original is A. Borel and H. Jacquet, *Automorphic forms and automorphic
representations*, in Corvallis Part I (1979), printed pp. 189–202.
The following original passages were read:

* Section 1.5(1), printed p. 190, one-based PDF page 185, identifies the
  archimedean idempotent condition with right compact finiteness and explains
  preservation of the other automorphic conditions under compact translation.
* Sections 3.2 and 4.1–4.2, printed pp. 194–195, PDF pages 189–190, give the
  right-translation convention, slice smoothness, rational invariance,
  finite Hecke condition, one finite-codimensional center ideal, and growth
  separately for each finite slice. The paragraph following 4.2 permits
  replacement of the finite Hecke element by a compact-open averaging
  idempotent; 3.2 identifies this with finite-level invariance.
* Section 4.3, printed p. 195, PDF page 190, reduces forms at fixed finite
  level to finitely many arithmetic quotients at infinity. This carries the
  archimedean statements to the adelic setting.
* Sections 4.4–4.6, printed pp. 196–197, PDF pages 191–192, discuss cusp forms,
  admissibility of the generated Hecke module, and automorphic representations.
  Section 4.6 explicitly distinguishes this Hecke-module structure from a
  full `G(A)` action. Cuspidality, admissibility, and local components are
  outside the present statements.
* For the differential-preservation provenance, section 2.2, printed p. 193,
  PDF page 188, explicitly says the generated archimedean module consists of
  automorphic forms. Its argument uses compact and center finiteness (2.1)
  and a smoothing convolution to obtain growth of the enveloping
  derivatives. Section 1.10, printed p. 192, PDF page 187, and section 4.8,
  printed p. 198, PDF page 193, also describe the resulting module structures.

The declarations are derived specializations of these assertions to the
Library's actual `GL_n` objects, and a decomposition of the closure assertion
into its remaining conditions. They are not quotations of four separately
numbered source propositions. The compact is the published product of real
orthogonal and complex unitary factors transported to the infinite completions.
The source's complex enveloping algebra of the real infinite Lie group is the
one constructed in `ArchimedeanEnvelopingAction`. The growth convention uses
the published matrix/inverse height, equivalent to the source's Hilbert norm by
`ArchimedeanHilbertGrowthComparison`. Section 1.2, printed pp. 189–190, PDF
pages 184–185, supplies the norm convention. The height is at least one, so
allowing exponent zero yields the same existence condition as a positive
integer exponent. No equivalence with the source's Hecke algebra is newly
formalized here.

There are apparent cross-reference slips in the printed section 2.2:
annihilation by the same central ideal is followed by “whence (d)”, and the
growth sentence refers to “1.2(c)”. We use the actual content of the preceding
definitions and the argument, not those labels: central annihilation is
1.3(c), and slow growth is 1.3(d), defined in 1.2(2). No project errata file for
this registered source was present when these statements were prepared.

The natural-rank quantifier includes `n = 0`. This is an internal extension
under the Library's empty-matrix convention, not a claim that the source
separately discusses `GL_0`: the matrix group is trivial, its Lie algebra is
zero, the enveloping action is scalar, and the growth height is at least one.
The statements use the same definitions at rank zero without a positivity
hypothesis; no separate rank-zero proof is supplied in this unit.

## Implemented elementary implication

`automorphicDifferentialPreservation_iff` proves that the third obligation is
equivalent to the conjunction of the first two. In the forward direction,
apply closure to the underlying finite-smooth function of an automorphic
form, convert membership using `mem_automorphicSubrepresentation`, and project
the compact-finiteness and growth conditions. In the reverse direction, use
the two proposed obligations on the form obtained from the input membership,
and combine them with the already published
`finiteSmoothEnvelopingAction_hasFiniteLevel` and
`isCenterFinite_finiteSmoothEnvelopingAction`. Convert the assembled predicate
back to membership. This is a conditional logical reduction, not a proof of
either remaining differential obligation or of compact-translation preservation.

No finite Hecke integration, full `(g,K)` construction, or automorphic
local-component construction is included.

Registered source: `borel-jacquet-1979-automorphic`.
Original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
