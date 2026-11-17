# Restricting the smooth Hecke equivalence and comparing corner induction

This internal construction supplies the categorical assembly for Renard 2026
VI.10.6, Proposition (ii), printed p.214 / PDF p.220. It applies to any Hausdorff
locally compact nonarchimedean group and compact open subgroup, once closure
of fixed-vector generation under subobjects is supplied. It does not prove
that closure assertion for arbitrary compact open subgroups.

First, generation by an idempotent is invariant under isomorphisms of actual
nondegenerate modules: the forward map is surjective, using its inverse, and
the published surjective descent theorem preserves generation. The published
III.1.4 equivalence, restricted by the generation bridge, therefore gives
`fixedVectorGenerationEquivalence`. Its forward functor followed by inclusion
is definitionally the original smooth Hecke functor on the generated objects.

To transfer subobject closure, apply the inverse of the III.1.4 equivalence
to a monomorphism of nondegenerate modules. An equivalence preserves
monomorphisms. The counit and the generation bridge turn generatedness of
the target into fixed-vector generation of its recovered representation;
the supplied closure gives the source property. The bridge and counit then
return generatedness of the original source module.

Under this explicit closure assumption, `fixedVectorCornerEquivalence`
composes the restricted equivalence with the published I.3.2 corner
equivalence. Its forward functor is definitionally the original smooth
Hecke functor followed by the idempotent-fixed-part functor.
`fixedVectorCornerEquivalence_inverseIso` is the counit of the restricted
equivalence, whiskered by the actual generated induction functor and the
inclusion. Forgetting generatedness recovers the original tensor induction
functor by definitional equality. Carrier universes are `max u v`, as needed
to contain the actual induction tensor product.

The construction uses the proved III.1.4 theorem (printed p.60 / PDF p.66)
and I.3.2 theorem (printed p.22 / PDF p.28) of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`.
These categorical restrictions and transports are internal derived content.
The VI.9.4 generation theorem is not assumed as an unproved Lean constant.
