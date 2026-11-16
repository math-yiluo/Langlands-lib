# Full-order formal comparison for commuting coefficient squares

This is an internal construction from `AtlasBaseChangeAlongSquare` and
`AtlasOrderRationalBaseChangeAlongComposition`. It lifts the actual formal
comparison between two coefficient-extension routes to the full acting order.
No additional original-literature assertion is made.

## Scope and inputs

Let `O` be a commutative ring, let `R`, `S`, `S'` and `T` be commutative
`O`-algebras in one universe, and let `D` be a ring with a central `O`-algebra
structure. The name “order” describes the intended application; the construction
does not require that `D` be a maximal order or finite over `O`.
Let `E : OrderAction D X` be an action on a formal `O`-module atlas over `R`.
Its coordinate type is finite, while its principal cover need not be finite.
Tests have the coefficient-ring universe.

For naturality, a second atlas `Y` may have a different finite coordinate type,
but the original covers are equal, `h : X.opens = Y.opens`. Integral maps
commute with every element of `D` as formal atlas maps. For rational naturality,
`F` is any field with an `O`-algebra structure, and `RationalHom F E E' h`
is the full chartwise `D`-centralizer inside the global tensor
`F tensor_O BasicAtlas.Hom X Y h`. It is not replaced by the tensor of integral
order-linear maps. Only the quasi-isogeny section adds `IsDomain O` and
`IsFractionRing O F`.

## Equality transport and the actual square isomorphism

For equal coefficient maps `e : f = g`, `baseAlongEqIso` transports the
actual full-order identity isomorphism. Equality elimination reduces its
construction to `Iso.refl`. The two lemmas ending in `_hom_val` and `_inv_val`
identify both underlying formal maps with the corresponding ambient equality
comparison maps.

`baseAlongEqPointEquiv` is a `D`-linear equivalence between complete compatible
families on the two restricted tests. It likewise reduces to the identity by
equality elimination. `baseAlongEqPointEquiv_eq` identifies its underlying
function with the ambient family transport, and `baseAlongEq_onPoints`
shows that the actual formal equality isomorphism realizes this entire-family
comparison. Its proof reduces to the identity formal-map action.

Take supplied maps

```text
f : R -> S,    g : S -> T,
p : R -> S',   q : S' -> T,
e : g.comp f = q.comp p.
```

`baseAlongSquareIso E f g p q e` is the composite

```text
(E extended by f) extended by g
    -> E extended by g.comp f
    -> E extended by q.comp p
    -> (E extended by p) extended by q.
```

The first map is the actual composition isomorphism, the second is the equality
transport, and the third is the inverse actual composition isomorphism.
The target cover equality is the ambient `baseAlongSquareOpens_eq`.
All three factors commute with the full `D`-action; composing them constructs
both actual formal maps and their two inverse equations.
`baseAlongSquareIso_hom_val` and `baseAlongSquareIso_inv_val` prove that
forgetting the action recovers exactly both ambient square maps. Their proofs
expand the composite and use the three factors' forgetful identities.
The specified chart choices of the composition comparisons are retained.

## Complete-family and integral naturality laws

For every `T`-test `A`, `baseAlongSquare_onPoints` starts with a whole
compatible family for `E` on `A` restricted along `g.comp f`. Extending this
family successively along `f` and `g`, then applying the square isomorphism,
equals first transporting the original family along `e` and then extending
successively along `p` and `q`. This is an equality of entire families, with
`D`-linear comparison maps throughout. The proof expands formal composition
on points, applies the left composition-family law and the equality-family
law, and finishes with the right inverse composition-family law.
`baseAlongSquare_inv_onPoints` proves the reverse equation for the inverse
of that same `D`-linear equivalence using `LinearEquiv.symm_apply_eq`.

For every integral full-order formal map `a : Hom E E' h`,
`Hom.baseAlongSquare_natural` states that its left-route extension followed
by the target square comparison equals the source square comparison followed
by its right-route extension. `Hom.baseAlongSquare_inv_natural` states the
reverse square using the actual inverse comparisons. Both are equalities of
formal maps, rather than only equalities after evaluation. Their proofs use
subtype extensionality, identify both successive extensions and both comparison
maps with the ambient maps, and invoke the corresponding ambient naturality
equation. The successive extensions retain the supplied coefficient structures
and the induced cover equalities.

## Rational centralizers and whole quasi-isogenies

`RationalHom.baseAlongSquare_natural` and
`RationalHom.baseAlongSquare_inv_natural` give the same two squares for every
element of the full rational centralizer. Each comparison factor is the
rationalization of the actual integral square map, and each route uses both
supplied-target rational extension maps. Extensionality reduces these equations
to the ambient global-tensor naturality laws, using the forgetful identities
for rational composition, rationalization, scalar extension and both actual
comparison maps. No integral-generation, local rational-gluing or
evaluation-injectivity premise is used.

`baseAlongSquareQuasiIsogeny` applies `QuasiIsogeny.ofIso` to the constructed
full-order isomorphism, retaining both rationalized maps and both inverse
equations. Its `_hom` and `_inv` lemmas expose those maps.
`baseAlongSquareQuasiIsogeny_toAtlas` identifies the entire forgotten
quasi-isogeny with the ambient square quasi-isogeny. The proof uses
forward-map extensionality, the actual formal-map forgetful law and uniqueness
of a two-sided inverse.

Finally, `QuasiIsogeny.baseAlongSquare_natural` and
`QuasiIsogeny.baseAlongSquare_inv_natural` prove the forward and reverse
squares as equalities of whole full-order quasi-isogenies. They apply
forward-map extensionality to the corresponding rational-centralizer equations;
thus the conclusions include their inverse maps as well.

This pair does not specialize the square to varying `Nilp` quotients or assert
arbitrary-refinement invariance, further coherence, specialness, height,
framing, levels, rigidity or representability.
