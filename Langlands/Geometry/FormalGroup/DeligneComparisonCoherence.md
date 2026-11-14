# Identity and composition of the ordinary-to-structural comparison

This module proves identity and composition compatibility for the actual
adjunction-defined map

`f^(-1)(underlying_O M) -> underlying_O(f^* M)`.

It supplies derived infrastructure for Drinfeld, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed p.109 (PDF p.3), final paragraph defining
the four objects `eta,T,u,r`, continuing on printed p.110 (PDF p.4). The map
is needed to transport the actual structural-sheaf-valued map `u`. These
categorical coherence lemmas are derived from the existing adjunctions, rather
than separately stated in Drinfeld. The special-formal-module comparison in
Proposition 2.4, Section 2 B, printed p.110 (PDF p.4), remains a separate result.

## Objects and hypotheses

All declarations are in `Langlands.DeligneFormalSpace`. The coefficient ring
`O` is any commutative ring, and all schemes and coefficient modules are in
one universe. The schemes and scheme morphisms are arbitrary. No valuation,
nilpotence, flatness or finite-rank hypothesis is needed for this comparison.

For `f : S' -> S` and `phi : O -> Gamma(S,top)`, the existing
`structuralOSheafFunctor S phi` forgets structural-module scalars to the actual
`O`-module sheaf. On `S'` the scalar map is `pulledGlobalScalar f phi`.
`structuralPullbackSquare` regards the existing
`structuralPullbackComparison f phi` as the square between these two
scalar-forgetting functors, structural-module pullback and ordinary sheaf
inverse image. This square is an actual natural transformation.

The comparison is a map. The module does not assert that it is invertible.
All identity and composition comparisons appearing below are the canonical
ones already constructed for the corresponding pullback functors.

## The mate characterization

`structuralPullbackComparison_eq_mate` identifies this exact comparison with
the inverse mate of `structuralPushforwardIso f phi`. The structural
pullback/pushforward adjunction is on one side and the ordinary sheaf
inverse-image/direct-image adjunction is on the other.

The proof evaluates at each structural module, applies injectivity of the
ordinary adjunction's Hom equivalence, and reduces the actual comparison to
its defining transposed unit. The general mate-unit formula then gives
the equality. Thus the square's right mate is the actual sectionwise
pushforward coefficient comparison, whose underlying section maps are
identities.

## Identity compatibility

`structuralPullbackComparison_id` states that comparison along the identity,
followed by forgetting the canonical structural pullback identity
isomorphism, equals the ordinary inverse-image identity isomorphism
whiskered by the original scalar-forgetting functor.

The proof applies the injective mates equivalence after whiskering the
square by the structural identity comparison. Compatibility of mates with
these whiskerings reduces the equation to the structural and ordinary
identity comparisons' conjugate mates. The structural mate is provided
by the existing structural-module identity lemma. The ordinary comparison
is constructed by uniqueness of left adjoints, so its conjugate mate is
the identity. The mate of the identity square for identity adjunctions is
the identity square. The remaining pushforward square is checked on
actual sheaf sections, where both maps are identities.

## Composition compatibility

For `f : S' -> S` and `g : S'' -> S'`,
`structuralPullbackComparison_comp` equates the following paths, both
starting with iterated ordinary inverse image of the original underlying
module sheaf:

- apply the ordinary composite comparison and then the comparison for `g ≫ f`;
- inverse-image the comparison for `f`, apply the comparison for `g` to
  `f^* M`, and then forget the structural composite comparison.

The scalar maps for iterated and composite pullback agree by the actual
composition formula for global sections; no extra scalar-identification
data is assumed.

The proof first compares the two squares after inverse structural and
ordinary composite comparisons. Applying the mates equivalence reduces
vertical pasting and these whiskerings to pasting the actual pushforward
coefficient squares. The structural composition comparison's conjugate
mate is the canonical structural pushforward comparison. The ordinary
composition comparison's conjugate mate is the identity, again by
uniqueness of left adjoints. Evaluating the resulting equation on each
section proves it by reflexivity. Finally, evaluation at a module and
cancellation of the actual structural and ordinary comparison
isomorphisms give the displayed forward equation.

## Scope

The module establishes these laws for the existing canonical comparison,
without taking a mate equation or a coherence equation as input.
Compatibility of the full four-data object with identity and composition,
admissibility transport, the admissible functor on `Nilp`, integral
determinant comparison, the normalized projective-linear action,
comparison with special formal modules and representability remain
later work.
