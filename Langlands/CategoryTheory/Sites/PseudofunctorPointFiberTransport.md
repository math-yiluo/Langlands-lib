# Actual point fibres under fully faithful strong transformations

This is an internal construction from Mathlib's actual `Pseudofunctor.StrongTrans`
and `Functor.FullyFaithful` data and the published actual
`PseudofunctorPointFiber` construction. Its base category, base morphisms, fibre
objects and fibre morphisms retain four independent universe parameters. No
geometric existence or stack-algebraicity result is used.

Let `α` be a strong transformation from a contravariant category-valued
pseudofunctor `F` to `G` on the same category `C`. `component α X` is the actual
functor on the fibre at `X`. For `f : Y → X`, `comparison α f ξ` is the component
of the strong naturality isomorphism

```
component α Y (F(f) ξ) ≅ G(f) (component α X ξ).
```

`comparison_comp` retains the transformation's composition coherence. Its proof
evaluates Mathlib's strong-transformation composition equation at `ξ`, expands
the category-of-categories whiskerings, and removes the identity associators.
The resulting equation compares the pullback by a composite with the two
successive pullbacks using the actual composition comparisons of `F` and `G`.

For actual objects `ξ` over `U` and `η` over `T`, `transportIso` sends an
actual isomorphism `e : F(a) ξ ≅ F(p) η` to

```
(comparison α a ξ).symm ≪≫ (component α Z).mapIso e ≪≫ comparison α p η.
```

Accordingly, `mapPoints` retains the base map `a : Z → U` and transports its
actual isomorphism by this formula. It never replaces isomorphisms by their
existence or by isomorphism classes.

`transportIso_pullIso` proves compatibility with coherent pullback of these
isomorphisms. The proof substitutes the prescribed composite maps, expands
`comparison_comp` and `pullIso`, cancels the adjacent images of inverse
composition comparisons, and applies the ordinary naturality equation of the
strong-transformation comparison at the restriction morphism. This proves
`mapPoints_restrict` for every morphism of the entire slice `Over T`.
`presheafMap` is the resulting natural transformation on the full actual
point-fibre presheaves. No full-faithfulness hypothesis is needed for this map.

If every `component α Z` is fully faithful, `pointsEquiv` is an equivalence of
actual point types. For each fixed base map `a`, it combines the fully faithful
functor's equivalence on actual isomorphisms with conjugation by the two
comparison isomorphisms. The inverse conjugates in the reverse directions and
uses the fully faithful functor's inverse on isomorphisms. It retains the same
`a`. `pointsEquiv_apply` records that the forward map is exactly `mapPoints`.

`presheafIso` then assembles these equivalences using `mapPoints_restrict`:

```
PseudofunctorPointFiber.presheaf F ξ η
  ≅ PseudofunctorPointFiber.presheaf G (component α U ξ) (component α T η).
```

This statement compares the whole presheaves and all their restriction maps.
When the base category is schemes over a base, every scheme test and every slice
morphism is included, without any empty, reduced, nonreduced, affine or
quasi-compact restriction. Full faithfulness is required in every fibre, not
just on field-valued points. No essential-surjectivity assumption is made:
the comparison concerns objects in the actual image of the transformation.

The construction can therefore transport point-fibre representations along a
fully faithful inclusion of families. It supplies no fully faithful inclusion
by itself, no open-substack criterion, no represented fibre and no atlas
existence theorem. Those geometric constructions remain separate obligations
for the Picard-stack proof.
