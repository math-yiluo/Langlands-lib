# The abelian category of equivariant module sheaves

Author: Worker 61. Builds on Worker 13's published equivariant sheaf category
and on the companion transport site `Langlands.Sheaf.Equivariant.Site`.

Let `R` be a commutative ring, and let a group `G` act on a topological space
`X` by continuous individual operators. Here `R`, `G` and `X` all lie in one
universe `u`. Morphisms of the transport category carry a group label, so its
hom types lie in the universe of `G`. With `G : Type u` the transport site is
small relative to `ModuleCat.{u} R`. Mathlib then provides sheafification of
`ModuleCat.{u} R`-valued presheaves on it, through its plus-construction
instance for concrete categories. This universe restriction is the only
specialization relative to the companion modules.

`topologicalSheaf_abelian` makes the published category
`TopologicalSheaf G X (ModuleCat.{u} R)` abelian. Mathlib's
`sheafIsAbelian` makes `Sheaf (transportTopology G X) (ModuleCat.{u} R)`
abelian. `abelianOfEquivalence` transports this along `sheafEquivalence`,
keeping the published preadditive structure; finite products are transported
along the same equivalence. In Mathlib's construction, which is used without
further choices, the cokernel of a morphism of sheaves is the sheafification,
for the transport topology, of its sectionwise cokernel presheaf. Kernels and
cokernels are therefore constructed objects with proved universal properties,
not supplied data.

`topologicalSheaf_isGrothendieckAbelian` transports Mathlib's theorem that
sheaves of modules on a small site form a Grothendieck abelian category, using
`IsGrothendieckAbelian.of_equivalence`. `topologicalSheaf_enoughInjectives`
records the resulting injective objects, from Mathlib's theorem that
Grothendieck abelian categories have enough injectives. These instances are the
inputs for derived functors of equivariant section functors.

Scope: these are abelian structures on equivariant sheaves for an action on an
ordinary topological space. No smoothness of sections under a topological group
is imposed, and the analytic equivariant étale site of Berkovich and Harris is
not constructed here. Exactness of the forgetful functors to ordinary sheaves
or to modules, and comparisons of derived functors, are not asserted.

Provenance: this is derived infrastructure. Berkovich, *Etale equivariant
sheaves on p-adic analytic spaces* (unfinished 1995–1996 manuscript),
section 1.5, printed page 10, builds the Godement resolution by taking
cokernels `Coker d^{m-1}` of abelian sheaves on the site `X(G)`. That recipe
presupposes the abelian category of sheaves which is constructed here for the
ordinary-topological transport site. Harris, *Galois properties of
cohomological automorphic forms on GL(n)* (1999), section 2, printed page 304,
uses Berkovich's acyclic resolution to compute derived functors. Those derived
functors need the injective objects recorded here. The sources are registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`) and
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`
(SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`).
Worker 61 read the cited passages.

Dependencies: the companion `Site` module and Mathlib `Sites.Abelian`,
`Sites.LeftExact`, `Abelian.GrothendieckAxioms.Sheaf`,
`Abelian.GrothendieckCategory.EnoughInjectives` and the module-category
instances, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
