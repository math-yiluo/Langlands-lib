# Nondegenerate Hom functor interface and boundary checks

These internal checks cover the constructions in `NondegenerateHomFunctor` and
`RenardHomFunctors`. They introduce no replacement Hom, action or part.
Their mathematical source and scope are those pairs' Renard I.2.3 citations.

The checks assign complete unapplied constants to explicitly written types:
the ambient functor, named source action, unbundled induced map and its
composition law, nondegenerate composite, restriction, both natural inclusions,
part map, pseudo-F, I, the source nondegenerate-bimodule adapters and the
specialized inclusions. Each type is checked with independent symbolic
universes and with complementary unequal 0/1 assignments. The Hom and part
carrier universes are the exact maxima. The unbundled composition check keeps
the source, intermediate and target carrier universes independent.

The competing-structure tests retain the selected ring, group, source actions
and named Hom action despite alternatives on the same types. A separate
coincident-carrier test sets both rings and both carriers to one type.
The specialized tests explicitly select the ring-induced additive group and
the left or right regular action even in the presence of other structures.
Subsingleton tests cover trivial source and target carriers and their parts.

The integer zero-action model uses two copies of the nonzero additive group
of integers with zero original S-action and zero residual right R-action,
with S = R = integers. The original identity Hom is nonzero, as evaluation at
1 proves. The published zero-action lemma shows the induced action is zero.
Consequently membership in the actual part is equivalent to being the zero
Hom. The part is subsingleton and excludes the identity. Subtype, canonical
natural inclusion and restricted-map formulas are checked on that part.
This demonstrates why the part cannot be identified with the whole Hom.

The regular integer model instead selects the published left and right
regular actions. It checks the multiplication side in both specialized
actions and in I's inherited subtype action, as well as the pseudo-F carrier
and induction inclusion. These are checks of the direct additive constructions;
they assert no coefficient recovery, equality of the two parts, comparison
with scalar restriction, adjunction, exactness or full coverage of I.2.3.
