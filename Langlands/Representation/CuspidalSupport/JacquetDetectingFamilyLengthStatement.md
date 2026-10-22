# Finite detecting-family Jacquet length criterion

Worker 118 authored this statement pair from Worker 170's task specification.
Its provenance is an internal algebraic bridge motivated by Bernstein and
Zelevinsky's length argument in BZ77 §2.14(2).

`Langlands.CuspidalSupport.JacquetDetectingFamilyLengthTheorem.{uF,uV}`
is a `Prop`-valued definition. It states the following implication and supplies
no proof of it.

For every prime `p`, actual `PadicField.{uF} p` named `F`, compatible
`F.TopologicalData` named `T`, natural rank `n`, and smooth representation
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)`, let
`s : Finset (BlockShape n)` be any finite set of standard block shapes and
`b : BlockShape n → ℕ` any function of natural bounds. Write

`J_C(A) = (T.normalizedJacquetFunctor C).obj A`.

Assume precisely these two mathematical hypotheses:

1. For every `C ∈ s`,
   `HasCompositionLengthAtMost (Rep.of J_C(A).representation) (b C)`.
2. For every smooth representation `D` of the same group and carrier universe,
   if `SmoothRep.IsSubquotient D A` and `Nontrivial D`, there exists
   `C ∈ s` such that `Nontrivial J_C(D)`.

Then both conclusions hold:

1. `IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
   A.representation.asModule`.
2. `HasCompositionLengthAtMost (Rep.of A.representation) (∑ C ∈ s, b C)`.

The sum is the ordinary natural-number sum of the bounds over `s`.
Only values of `b` on `s` matter. The field and carrier universes `uF` and
`uV` are independent; the coefficient field is Lean's actual complex field.
The local instance `T.topology` fixes the topology used for smoothness and
the induced general linear and Levi topologies.

## Actual objects and boundary cases

The normalized Jacquet functor is the existing quotient by the action
differences of the block unipotent radical. Its Levi action is twisted by
the inverse square root of the actual block modulus. It is imported from
`Langlands.Representation.Jacquet.Parabolic`, with no replacement functor
or additional functoriality or exactness hypothesis.

`SmoothRep.IsSubquotient D A` is the Library predicate witnessing an actual
invariant subrepresentation of `A`, an actual quotient of that
subrepresentation by an invariant subrepresentation, and a smooth
representation isomorphism from `D` to that quotient. Thus detection applies
to every nonzero subquotient, with no irreducibility restriction.
`Nontrivial` is applied to the underlying carrier of the smooth object.

`HasCompositionLengthAtMost` is the existing existential predicate for an
actual zero-to-full finite filtration by invariant subspaces with irreducible,
nonzero successive quotient representations and at most the specified number
of factors. `IsFiniteLength` is Mathlib's module finite-length predicate for
the group algebra action associated to `A.representation`. Neither is replaced
by a formal numerical length assignment.

The quantifiers include rank zero, an empty `s`, zero bounds, and the zero
representation. No positivity, finite-dimensionality, admissibility,
cuspidality, irreducibility, or finite-length assumption on `A` is imposed.
For empty `s`, detection says that `A` has no nonzero subquotient; the
conclusion still uses the sum zero. In particular, the statement does not
require a nonzero representation or a nonempty detecting family.

## Source motivation and proof boundary

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
§2.14(2), printed page 449 / PDF page 10.
Registered source: `bernstein-zelevinsky-1977-induced-i`; original PDF
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original page was read directly.

In that argument, the authors sum lengths of Jacquet modules over Levi
subgroups associated to the inducing Levi. Exactness makes this measure
additive, and their preceding argument makes it positive on nonzero
subquotients of the induced representation, yielding a length bound.

The declaration here isolates an internal finite-family criterion for
arbitrary smooth `A`; it is not a verbatim theorem of BZ77. Its two hypotheses
explicitly supply the bounded Jacquet lengths and detection needed for the
intended measure argument. A later proof can use the published exactness of
the actual normalized Jacquet functors and the bounded-chain composition
length criterion. This module does not implement that proof or the
application to cuspidal induction, and it assumes no theorem package as a
premise.
