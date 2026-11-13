# Compact sections with independent universes

Worker 1222. Module and namespace
`Langlands.Sheaf.CompactSupport.IndependentUniverses`.

This is an internal extension of the published
[compact-support construction](../CompactSupport.md). The coefficient ring
`R : Type v` and topological space `X : TopCat.{u}` have independent universes;
the module carriers have the same universe `u` as the space. Closedness and
the compact-section constructions take an explicit typeclass assumption
that forgetting modules to types preserves filtered colimits. The supplied
local instances establish this whenever the carrier universe is `max w v`.
In particular, they support the actual field `ℂ` and spaces in any universe.

`support F s` is the set of points where the actual colimit-stalk germ of the
global section `s` is nonzero. `isClosed_support` proves closedness by finding
an open neighborhood where a section with zero germ vanishes.
`support_zero`, `support_add_subset` and `support_smul_subset` give the support
properties needed for a submodule. `support_map_subset` uses naturality of
germs to prove that a presheaf morphism cannot enlarge support.

`submodule F` is the submodule of global sections whose support is compact.
Its closure under addition and scalar multiplication follows because the
resulting supports are closed subsets of compact sets. `map` restricts the
actual map on global sections to these submodules, by the same argument.
There is no assumption that the space is Hausdorff, locally compact or
totally disconnected, and no change to the compactness condition.

The local instances `forget₂_preservesFilteredColimits` and
`forget_preservesFilteredColimits` supply the elementwise germ-equality
criterion. The first reuses Mathlib's explicit filtered-colimit cocones for
modules and abelian groups at carrier universe `max u v`. The second composes
it with the forgetful functor from abelian groups to types. These instances
are local to this file. A consumer can activate them locally with
`attribute [local instance]` on these two declarations, so unrelated imports
retain their existing typeclass inference.

`support_eq` and `submodule_eq` prove that at a common coefficient and space
universe, these constructions agree with the published `CompactSupport`
definitions. The original module and its categorical functors are unchanged.

This extension is required for Renard II.2.5 distributions on complex vector
sheaves with arbitrary space universe. It asserts no additional theorem from
Renard. Its mathematical construction and proof route are the published
compact-support construction, with independent coefficient and carrier sizes
and explicit local filtered-colimit preservation. The environment is Lean
4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
