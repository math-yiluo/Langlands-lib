# Finite-length detection by proper refined Jacquet modules

Author: Worker 185, following Worker 122's task specification.

`Langlands.CuspidalSupport.RefinedJacquetFiniteLengthDetectionStatement.{uF,uV}`
is a closed `Prop`-valued definition. It states the following implication;
this module supplies no proof.

For every prime `p` with `Fact p.Prime`, actual `PadicField.{uF} p` named
`F`, compatible `F.TopologicalData` named `T`, natural rank `n`, and
`B : GeneralLinear.BlockShape n`, install `T.topology`. For every actual
smooth complex representation
`A : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, assume:

1. For every `D : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`,
   `SmoothRep.IsSubquotient D A` and
   `IsLeviQuasicuspidal B D.representation` imply `Subsingleton D`.
2. For every `S : Geometric.BlockRefinement B` whose actual refined
   parabolic satisfies `Geometric.refinedParabolic F.Carrier B S ≠ ⊤`,
   the actual representation
   `T.normalizedRefinedJacquet B S A.representation` has `IsFiniteLength`
   as a module over
   `MonoidAlgebra ℂ (Geometric.refinedLevi F.Carrier B S)`.

The conclusion is
`IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) A.representation.asModule`.
Thus the conclusion concerns the actual group-algebra module of `A`, with
Mathlib's module finite-length predicate.

## Actual subquotients and normalization

`B.Levi F.Carrier` is the existing product of the general linear groups
on the ordered blocks of `B`. A refinement `S` chooses an ordered block
shape inside each block of `B`. Its parabolic, diagonal Levi subgroup,
and unipotent radical are the actual product subgroups from
`Geometric.WeylDefinitions`. Properness is inequality of that parabolic
subgroup with the full product Levi, not a supplied combinatorial test.

`SmoothRep.IsSubquotient D A` retains an actual invariant subrepresentation
of `A`, a quotient of it by an invariant subrepresentation, and a smooth
representation isomorphism identifying `D` with that quotient.
`IsLeviQuasicuspidal` means that the actual unipotent coinvariant quotient
is a subsingleton at every proper standard refinement. The first
hypothesis therefore rules out all nonzero quasicuspidal smooth
subquotients, with no irreducibility restriction.

The imported `T.normalizedRefinedJacquet` acts on
`Jacquet.Coinvariants A.representation
  (Geometric.refinedUnipotent F.Carrier B S)`.
Its quotient relations are the span of the actual action differences
`A.representation(u)(v) - v`. Its acting group is the actual
`Geometric.refinedLevi F.Carrier B S`, and its action on a quotient class
is the original Levi action multiplied by
`T.refinedLeviInverseHalfModulus B S`. This is the inverse square root
of the full upper product modulus. Normalization changes the action,
not the quotient carrier or the meaning of its vanishing.

The field and representation carrier universes `uF` and `uV` are
independent. The rank quantifier includes zero, and the refinement
quantifier includes the empty product and single-block refinements.
Only proper refinements enter the second hypothesis. When there are no
proper refinements, quasicuspidality is vacuous and the first hypothesis
forces the representation itself to vanish, since it is its own
subquotient. Zero representations are included. No admissibility, finite
generation, irreducibility, central character, finite-dimensionality,
prior finite length of `A`, chosen detection witnesses, or supplied
functor exactness is assumed.

## Derived provenance and proof boundary

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
§2.14(2), printed page 449 / PDF page 10. Registered source:
`bernstein-zelevinsky-1977-induced-i`; retained PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original page, including its formulas, was read directly.

BZ77 sums the lengths of Jacquet modules over the standard Levis
associated to an inducing Levi. Exactness makes that measure additive,
and detection of every nonzero subquotient makes it positive there.
This bounds the length of the induced representation.

The present interface is an internal derived product-Levi criterion
motivated by that argument, not a literal theorem statement in BZ77.
Here the intended measure sums lengths over all proper standard
refinements of `B`. This is a finite family: the published
`CuspidalSupport.FiniteBlockShapes` proves that each `BlockShape k` is
finite, and `BlockRefinement B` is their product over `Fin B.length`.
If a nonzero subquotient had zero Jacquet module at every proper
refinement, it would be quasicuspidal by definition, contradicting the
first hypothesis. Thus detection is to be derived, not assumed as
additional witness data.

For a future proof, injectivity and exactness on smooth refined
coinvariants should follow using the published
`T.refinedUnipotent_finite_containment` and generic smooth coinvariant
exactness, as already used in `CuspidalSupport.QuasicuspidalSubquotientProof`.
The finite sum of Jacquet lengths is then a bounded natural measure on
invariant subspaces, strictly increasing at every strict inclusion:
the successive nonzero quotient is detected by some proper refinement.
The generic bounded-chain criterion in `Filtration.LengthCriterionProof`
then gives finite length. The existing
`CuspidalSupport.JacquetDetectingFamilyLengthStatement` and
`CuspidalSupport.JacquetDetectingFamilyLengthProof` were read for this
route; their single-GL interface is preserved unchanged.

These paragraphs explain the intended derivation, not an implemented
proof. The statement does not depend on a general induction finite-length
theorem, `InducedFiniteTypeStatement`, the parent
`GLAdmissibleFiniteLengthStatement`, or a replacement exactness premise.
Its exact closed proof is a separate successor task.
