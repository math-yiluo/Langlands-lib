# Actual abelian schemes with rational algebra action

This module constructs the category of actual abelian schemes over a scheme
`S` with a unital rational algebra action `D →ₐ[ℚ] End0 A`. It constructs
pullback along arbitrary base morphisms and the natural identity and binary
composition comparisons. Bases lie in a common universe; the algebra has an
independent universe.

## Provenance

This is derived infrastructure for the PEL moduli problem in Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties* (2001),
Section III.1, printed pp.90–91 / PDF pp.98–99. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
That problem uses an algebra action in the rational endomorphism algebra
and equivalence through an isogeny intertwining the actions. Printed
p.18 / PDF p.26 defines an isogeny as an invertible actual rational
homomorphism. The category here isolates this part of the data; its
construction is internal to the published rationalization and actual
base-change functors.

The algebra `D` is any unital rational algebra. No faithfulness condition is
imposed on its action. The additional faithful action, polarization, Hodge
compatibility, dimension and adelic level conditions of the source problem
are subsequent restrictions and constructions.

## Objects, morphisms and isomorphisms

`RationalAlgebraActionData` contains an actual `AbelianScheme S` and the
displayed algebra homomorphism into its actual `End0`. In particular,
preservation of addition and rational scalars is part of the bundled action.
Its `toAction` retains the multiplicative monoid action on the same object
in the published `RationalCategory S`.

`RationalAlgebraAction S D` takes the category induced from Mathlib's
`Action (RationalCategory S) D` along this construction. Thus its morphisms
are precisely rational homomorphisms satisfying

```text
i_X(d) ≫ f = f ≫ i_Y(d)     for every d : D.
```

`of` bundles the data. `hom0` exposes the actual rational homomorphism,
`intertwines` supplies the equation, and `homMk` constructs a morphism from
exactly that equation. `hom_ext` states that the underlying rational map
determines the equivariant map. Identities and composition are those of
the rationalized category, as the two `hom0` formulas show. Their
equivariance and category laws are inherited from the action category
and induced category. `forget` is faithful and forgets just the action.

`underlyingIso` forgets an equivariant isomorphism. Conversely `isoMk`
uses an actual rational isomorphism and equivariance of its forward map.
Mathlib's `Action.mkIso` derives equivariance of the actual inverse from
the forward equation and the two inverse identities. The component
formulas show that both actual rational maps are retained. This construction
does not claim invertibility of an arbitrary integral homomorphism.

## Actual pullback

For `b : S' ⟶ S`, `pullbackObj b` takes the actual abelian-scheme pullback
and composes its `rationalBaseChangeEnd` algebra map with the original
action. `pullbackMap b` constructs the corresponding equivariant rational
map. `pullback b` assembles them into the functor. The object action
formula and `hom0_pullback_map` state

```text
i_{b*X}(d) = b*(i_X(d)),    hom0(b*f) = b*(hom0 f).
```

Applying the rational pullback map to the original intertwining equation,
and using preservation of composition, proves equivariance of the
pulled-back morphism. Its identity and composition laws follow from
those of the existing rational pullback. `pullbackForgetIso` is the
identity comparison with pullback in the rationalized category.

## Identity and binary composition comparisons

`pullbackIdIso X` and `pullbackCompIso b c X` use exactly the actual
rational identity and composition comparison isomorphisms of the
underlying abelian scheme. The published `rationalBaseChangeHom_id`
and `rationalBaseChangeHom_base_comp` applied to `X.action d` establish
their equivariance. The two `underlyingIso` formulas identify them with
the original geometric comparisons, including their inverse maps.

`pullbackIdNatIso` and `pullbackCompNatIso b c` assemble these components
into natural isomorphisms. Their naturality is the same published
rational Hom transport equation applied to the underlying rational map
of an equivariant morphism; faithfulness reduces equality to that map.

These are natural identity and binary composition comparisons. Separate
triangle and pentagon identities and a bundled pseudofunctor are not
asserted here. No local freeness, finite étaleness, geometric point,
polarization or representability assumption is needed for these
constructions. They provide an actual action category and actual
pullback, rather than a complete PEL moduli functor or a scheme level.
