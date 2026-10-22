# Determinant characters of exact virtual complex representations

Worker 6 constructs the actual determinant on
`Langlands.VirtualRepresentation.ExactGrothendieckGroup P` for an arbitrary
predicate `P` on finite-dimensional complex representations of a group `G`.
The group universe `uG` and the representation-carrier universe `uV` are
independent. Rank zero is included throughout.

The principal definitions in namespace
`Langlands.VirtualRepresentation.ExactGrothendieckGroup` are:

- `determinant`: an integer-linear map to `Additive (G →* ℂˣ)`.
- `determinantCharacter P x`: its value as an ordinary unit-valued group
  homomorphism on `G`.
- `determinantHom`: the equivalent explicitly multiplicative homomorphism
  `Multiplicative (ExactGrothendieckGroup P) →* (G →* ℂˣ)`.
- `continuousDeterminant`: the specialization of the linear map to the full
  predicate `fun A => A.IsContinuous`.

The target is an unbundled character with a separate continuity theorem.
No topology on the virtual group or on the space of characters is selected,
and no continuity of a map between such spaces is asserted. The multiplicative
homomorphism offers the same construction without additive type-tag notation.
The module locally selects the additive monoid inherited from the character
group so that the canonical integer module and the quotient universal property
use the same inherited structure; this supplies no mathematical assumption.

## Exact-relation descent

`FiniteRepresentation.determinantCharacter_shortExact` wraps the published
`Langlands.Weil.representationExactSequenceInvariants`. The latter proves
scalar determinant multiplicativity for actual intertwiners `f : A → B` and
`g : B → C`, assuming injectivity of `f`, surjectivity of `g`, and equality
of the range of `f` with the kernel of `g`. Extensionality of characters and
injectivity of the inclusion of units into the field turn its scalar formula
into

```
determinantCharacter B = determinantCharacter A * determinantCharacter C.
```

The helper retains independent carrier universes for all three representations.
It imports the existing proof; it neither repeats the kernel/quotient argument
nor takes exact-sequence multiplicativity as a new hypothesis.

`classDeterminant P` first forgets the property on the actual isomorphism class,
then applies the published `FiniteRepresentation.determinantCharacterClass`,
and finally applies the additive type tag. The existing class map already
proves invariance under genuine intertwining equivalence.
`classDeterminant_isExactAdditive` uses the character identity above to prove
additivity on every short exact sequence whose three objects satisfy `P`.

The existing `ExactGrothendieckGroup.lift` therefore defines `determinant`.
Concretely, the integral linear extension on the finitely supported presentation
sends every generating relation `[B] - [A] - [C]` to zero, so it vanishes on
their integral span and factors through the actual quotient. For an arbitrary
predicate, the quotient has precisely these relations among the selected
objects. No closure, semisimplicity, irreducible decomposition, equivariant
splitting, finite image or positive-rank hypothesis is required.

## Evaluation formulas

`determinant_ofClass`, `determinantCharacter_ofClass` and
`determinantCharacter_ofRepresentation` identify the descended values with
the existing genuine class and representation characters.
`determinantCharacter_ofRepresentation_apply` identifies the scalar value at
`g : G` with `LinearMap.det (A.representation g)`.

The `determinantCharacter_zero`, `_add`, `_neg`, `_sub` and `_zsmul` lemmas
state, respectively, that virtual zero maps to the trivial character, addition
to multiplication, negation to inversion, subtraction to division, and an
integer multiple to the corresponding integer power. Each also has an
`_apply` lemma giving the pointwise identity at `g : G`.
`determinantCharacter_quotientMap_single` evaluates a single-coordinate
presentation with coefficient `n : ℤ` as the `n`th power of the genuine
class character; negative coefficients are included.

`FiniteRepresentation.determinantCharacter_eq_one_of_rank_eq_zero` uses
Mathlib's determinant-one theorem in dimension zero. The quotient-level
`determinantCharacter_ofRepresentation_rank_zero` consequently sends the
virtual class of every rank-zero object in the selected family to the trivial
character.

This is a character-valued determinant. It is distinct from the published
`FiniteRepresentation.determinantClass`, which returns the isomorphism class
of a scalar-line representation. In particular, this construction's target
group law is pointwise character multiplication, rather than addition of
scalar-line representation classes.

## Continuity

`FiniteRepresentation.continuous_determinantCharacter` specializes the published
`Langlands.Weil.representationCharacterNormalization` to an actual bundled
representation. That theorem supplies a continuous unit-valued character with
the exact scalar determinant values. Character extensionality identifies it
with the published genuine determinant character. Thus this helper reuses the
proved determinant continuity, including its ordinary complex and unit
topologies and the `moduleTopology` on endomorphisms.

`ExactGrothendieckGroup.continuous_determinantCharacter` assumes only that every
object satisfying `P` is continuous. Surjectivity of the quotient map writes
an arbitrary virtual element as the image of a finitely supported integral
presentation. `Finsupp.induction_linear` reduces continuity to zero, addition,
and single coordinates. The zero character is constant; products of continuous
unit-valued functions are continuous; a single coordinate is an integer power
of a genuine continuous determinant character, so continuous inversion on
complex units handles negative coefficients as well. Class representatives
are obtained by quotient induction. This proof uses neither a topology on
the virtual quotient nor a presentation as a difference of two actual objects.

`continuous_continuousDeterminant` applies this result to the full continuous
predicate. The group `G` needs only a group structure and a topology: no
`IsTopologicalGroup G` assumption is necessary, because the continuity proof
uses multiplication and inversion in the target `ℂˣ`.

## Provenance and dependencies

This is an internal derived construction. Its inputs are the published
[exact quotient and universal property](Exact.md),
[genuine determinant characters](../Weil/Representation/Determinant.md),
[exact-sequence proof](../Weil/Representation/ExactSequenceProof.md),
[character normalization proof](../Weil/Representation/CharacterNormalizationProof.md)
and the actual continuity predicate in
[Predicates](../Weil/Representation/Predicates.md). Their paired documents
retain their original literature correspondence; no new statement or proof
route is attributed to an external source here. Existing project definitions
and proofs are imported unchanged.

The implementation uses Mathlib's integer module on an additive commutative
group, determinant in dimension zero, finitely supported function induction,
and continuous multiplication and integer powers on complex units. These are
from the project-pinned Mathlib environment.

The result stops at a virtual character on the supplied group. It makes no
identification with local field units and includes no reciprocity inverse,
local epsilon identity, conductor formula, finite-inertia presentation or
tensor determinant law.
