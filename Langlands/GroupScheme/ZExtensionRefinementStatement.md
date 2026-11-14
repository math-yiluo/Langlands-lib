# Compatible common refinements of z-extensions

`Langlands.GroupScheme.ZExtensionMorphismDominationStatement` asserts the
following over every field `k`. Given connected reductive group schemes
`G` and `H`, actual z-extensions `z : ZExtension G` and
`t : ZExtension H`, and any group-scheme homomorphism `f : G ⟶ H`,
there exist an actual z-extension `w : ZExtension G` and group-scheme maps
`r : w.H ⟶ z.H` and `s : w.H ⟶ t.H` satisfying

```text
r ≫ z.p = w.p
s ≫ t.p = w.p ≫ f.
```

Composition `a ≫ b` means first `a`, then `b`. Both `w` and the maps with
these equalities are conclusions. The only hypotheses are the field
structure, the connected reductive groups, the supplied z-extensions, and
the homomorphism. In particular, `f` has no injectivity or surjectivity
requirement.

`Langlands.GroupScheme.ZExtensionCommonDominationStatement` asserts that
for every field and connected reductive group scheme `G`, any two supplied
z-extensions `z` and `t` of `G` admit an actual z-extension `w` of `G` and
maps to their sources with

```text
r ≫ z.p = w.p
s ≫ t.p = w.p.
```

This is the identity-map specialization of the morphism statement:
take `H = G` and `f = 𝟙 G`, and simplify `w.p ≫ 𝟙 G = w.p`.
It provides the common domination used in the independence-of-choice
argument for the Kottwitz homomorphism in KP Lemma 11.5.1.

The source is Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New
Approach* (Cambridge University Press, 2023), §11.4, Fact 11.4.2 and
Lemma 11.4.3, printed pp. 428–429 / PDF pp. 459–460, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The retained original is
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023.pdf`.
The authors' corrections of 1 November 2024, source
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
have no entries for §§11.4–11.5.

The morphism statement records the existence and commutation consequences
of the source's actual fiber product

```text
P = z.H ×_H t.H,
```

formed along `z.p ≫ f : z.H ⟶ H` and `t.p : t.H ⟶ H`.
Let `r : P ⟶ z.H` and `s : P ⟶ t.H` be its projections, and let the
map from `P` to `G` be `r ≫ z.p`. The fiber-product identity gives
`s ≫ t.p = r ≫ z.p ≫ f`, which yields the second displayed equality
after packaging `P` as `w.H`.

KP checks that this map to `G` is a z-extension. The projection to `z.H`
is the base change of `t.p`, and its composite to `G` is surjective.
The full scheme-theoretic kernel of the composite is the product of the
two induced torus kernels, hence is an induced torus. The resulting torus
extension of `G` is connected reductive. Its derived subgroup is simply
connected by the projection to `z.H`, whose kernel is a torus, and the
simple connectedness of the derived subgroup of `z.H`. In the common-target
case this construction is `z.H ×_G t.H`, the z-extension of Fact 11.4.2.
The Lean propositions retain the resulting actual extension and commuting
maps; they do not specify a chosen fiber product or its universal property.

The existing `ZExtension` and `IsZExtension` definitions are used unchanged.
Thus every conclusion includes an induced central torus kernel, the
represented fppf quotient with the full kernel on all test schemes,
connected reductive source and target, and simply connected derived group.
The explicit connected-reductive hypotheses repeat properties already
carried by the supplied extensions. The assertions range over arbitrary
fields, with no perfectness, characteristic, splitting, quasi-splitting,
valuation or local-field assumption; the source's fiber-product argument
uses none of those additional conditions.

Both declarations are proposition definitions. This module supplies their
statements; their unconditional Lean proofs, including the geometric
properties of the fiber product, remain separate proof obligations.
