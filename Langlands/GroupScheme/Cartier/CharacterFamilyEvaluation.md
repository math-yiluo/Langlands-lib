# Evaluate an abelian family of actual characters

Worker 616.

All declarations belong to `Langlands.GroupScheme.Cartier` and are
universe-polymorphic. Let `G` be any commutative group scheme over an
arbitrary scheme `S`, let `M : AddCommGrpCat.{u}`, and let

```text
a : EtaleLocalSystem.constant S M ⟶ Cartier.characters G
```

be a natural morphism of actual abelian presheaves. This module constructs
`characterFamilyHom G M a : G.toGrp ⟶ RelativeMultiplicativeType.diagonalizable S M`
and proves its coordinate evaluation formula.

## Construction

`constantCoefficient M T` is the additive map from `M` to the sections of
its constant model over `T : Over S`. It sends `m` to the constant locally
constant function with value `m`, using the published `constantSections`
equivalence. `constantCoefficient_restrict` proves that these sections pull
back to the same coefficient under every test-scheme morphism.

`familyCharacter G M a T` applies the component of `a` to these constant
sections. Its values are sections of the actual Cartier character functor,
canonically actual homomorphisms from `G_T` to `Gm_T`. The theorem
`familyCharacter_restrict` derives their compatibility with actual
restriction from naturality of `a` and the constant-section identity.

For an actual point `x : T ⟶ G.X`, `familyUnits G M a T x` evaluates all
these characters at `x`, then uses `Gm.pointsEquiv` to obtain a homomorphism
from `Multiplicative M` to the units of the global sections of `T.left`.
It is multiplicative in `m` because the family is additive and Cartier
character evaluation turns addition into pointwise multiplication. It is
natural in `T` by the published character evaluation restriction formula.

The published `RelativeMultiplicativeType.pointsEquiv` identifies these
unit-valued homomorphisms with actual points of `D_S(M)`. Its inverse gives
`familyPoints`, a homomorphism on the points over each `T`. The group laws
in the point variable follow from the character homomorphism laws, and
`familyPoints_naturality` follows from the unit-valued naturality and the
diagonalizable point comparison.

The published `homOfPoints` recovers the actual group-scheme homomorphism
`characterFamilyHom` from this natural family on all relative tests.

## Coordinate formula

`characterFamilyHom_evaluation` states that, for every test `T`, point `x`
and coefficient `m`, the `m`-coordinate of the image of `x` is

```text
Gm.pointsEquiv S T
  (Cartier.characterEvaluation (familyCharacter G M a T m) x).
```

The left side is evaluated with the published actual
`RelativeMultiplicativeType.pointsEquiv`. The proof is exactly Yoneda's
point-recovery formula followed by cancellation of the diagonalizable
point equivalence. Thus the constructed map evaluates the specified
actual characters, with the existing restriction maps throughout.

## Scope and provenance

No finite generation, multiplicative-type hypothesis on `G`, normality,
connectedness, affineness, or nonemptiness is needed. The group scheme
`D_S(M)` is defined for any abelian `M`; finite generation is needed only
in later assertions that it is diagonalizable in the Library's finite-type
sense. The morphism `a` is arbitrary and need not be an isomorphism.
This module makes no claim that `characterFamilyHom` is invertible.

This is an internal derived construction from the published constant
section model, actual Cartier character evaluation, actual
arbitrary-base diagonalizable point equivalence, and group-valued Yoneda
recovery. It uses no classification or isotriviality theorem and cites no
external source assertion.
