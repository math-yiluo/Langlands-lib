# Discrete sections for specified local actions on a site

Author: Worker 13. Built on the published smooth vectors
`Langlands.IsSmoothVector` and smooth representations `Langlands.IsSmooth` of
`Langlands.Representation.Smooth.Definitions`, and on Mathlib's sieves,
Grothendieck topologies and sheaves.

Let `T` be a category and `G` a group with a topology. No compatibility between
the group structure and the topology is assumed. For an object `U` and an open
subgroup `H` of `G`, a local action of `H` on `U` is a monoid homomorphism
`a : H →* (End U)ᵐᵒᵖ`. An element `h` then acts on the sections of a presheaf
`F : Tᵒᵖ ⥤ A` over `U` by `F.map (a h).unop.op`. The opposite monoid makes
this a left action on sections. The coefficient category `A` is concrete, so
sections are elements of `ToType (F.obj (op U))`.

## Definitions

`LocalActionSystem T G` is a structure with a single field `IsAdmissible`. For
each object `U`, open subgroup `H` and local action `a` of `H` on `U`, the
proposition `IsAdmissible U H a` says that `a` is one of the admissible local
actions. The system is data supplied by the user. Nothing in this module
constructs it.

`IsDiscreteSection F a s` says that some open subgroup `K ≤ H` of `G` fixes the
section `s` of `F` over `U` under the local action `a`.

For a local action system `L`:

- `L.IsDiscrete F` says that every section of `F` over every object `U` is
  discrete for every admissible local action on `U`.
- `L.admissibleSieve U` is the sieve of arrows `W ⟶ U` that factor through an
  object `V` carrying an admissible local action.
- `L.Covers J` says that `L.admissibleSieve U` covers `U` for the Grothendieck
  topology `J`, for every object `U`.
- `L.discreteSieve F s`, for a section `s` over `U`, is the sieve of arrows
  `W ⟶ U` that factor as `W ⟶ V` followed by `f : V ⟶ U`. Here `V` carries an
  admissible local action for which the restriction `F.map f.op s` is a
  discrete section.
- `L.IsLocallyDiscrete J F` says that `L.discreteSieve F s` covers `U` for `J`,
  for every object `U` and every section `s` over `U`.

For sheaves, `L.discreteSheafProperty A J` and `L.smoothSheafProperty A J` are
`IsDiscrete` and `IsLocallyDiscrete J` of the underlying presheaf, as object
properties of `Sheaf J A`. `L.SmoothSheaf A J` is the full subcategory of
sheaves with locally discrete sections, and `L.smoothSheafInclusion A J` is its
inclusion into `Sheaf J A`.

For a presheaf `F` of `R`-modules over a commutative ring `R`,
`localRepresentation F a` is the representation of `H` on the sections over `U`
given by `h ↦ F.map (a h).unop.op`. `localRepresentation_apply` records this
formula.

## Results

- `IsDiscreteSection.map`: a morphism of presheaves sends discrete sections to
  discrete sections. The same subgroup fixes the image, by naturality.
- `IsDiscreteSection.of_injective`: conversely, a section is discrete if its
  image under a morphism that is injective over `U` is discrete.
- `IsDiscreteSection.of_agree`: let `N` be an open subgroup contained in both
  `H` and `H'`, and let local actions `a` of `H` and `a'` of `H'` on the same
  object agree on `N`. Then every section discrete for `a` is discrete for
  `a'`. The intersection of the fixing subgroup with `N` fixes it for `a'`.
- `isDiscreteSection_of_discreteTopology`: if `G` is discrete, every section is
  discrete for every local action. The trivial subgroup is then open.
- `discreteSieve_le_admissibleSieve` holds for every presheaf.
  `IsDiscrete.discreteSieve_eq` proves that the discrete sieve of every
  section of a discrete presheaf is the admissible sieve.
  `IsDiscrete.isLocallyDiscrete` concludes that discrete presheaves are locally
  discrete when `L.Covers J` holds.
- `discreteSieve_le_pullback`: the discrete sieve of the restriction of `s`
  along `g : V ⟶ U` is contained in the pullback along `g` of the discrete
  sieve of `s`. `discreteSieve_mem_of_covering` deduces the following from
  transitivity of `J`. Suppose that on a covering sieve of `U` the restriction
  of `s` along each arrow has a covering discrete sieve. Then the discrete
  sieve of `s` covers `U`.
- `discreteSieve_le_map` shows that a morphism of presheaves can only enlarge
  discrete sieves. `discreteSieve_map_of_injective` shows that discrete sieves
  are unchanged under a morphism that is injective on all sections.
  `IsDiscrete.of_injective` and `IsLocallyDiscrete.of_injective` give that the
  source of such a morphism into a discrete, respectively locally discrete,
  presheaf is again discrete, respectively locally discrete.
- `isDiscrete_of_discreteTopology` and `isLocallyDiscrete_of_discreteTopology`
  prove that for discrete `G` every presheaf is discrete, and every presheaf is
  locally discrete when `L.Covers J` holds.
- `discreteSheafProperty_le_smoothSheafProperty` proves the inclusion of the
  two sheaf properties when `L.Covers J` holds.
- `isDiscreteSection_iff_isSmoothVector`: for module-valued presheaves, a
  section is discrete exactly when it is a smooth vector of
  `localRepresentation F a`. Here the open subgroup `H` carries the subspace
  topology. One direction pulls `K ≤ H` back to `H`. The other direction pushes
  an open subgroup of `H` forward to `G`, which stays open because `H` is open.
  `LocalActionSystem.isDiscrete_iff_isSmooth` concludes that `L.IsDiscrete F`
  holds exactly when every admissible local representation is smooth.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.4, printed pp.7–8, which are PDF pages 7–8.
Worker 13 read these passages in the original. The Key Lemma gives every
quasi-étale `U → X` with compact `U` a canonical continuous action of an open
subgroup `G_U ⊂ G` on `U`. The text before the definition notes that, through
it, `G_U` acts canonically on `F(U)` for an equivariant étale sheaf `F`.
Distinguished étale morphisms carry similar actions of
open subgroups. Two choices of such an extension agree on a smaller open
subgroup `N`. Definition 1.4.1 calls a `G_d`-sheaf a `G`-sheaf when, for every
quasi-étale `U → X` with compact `U`, the action of `G_U` on `F(U)` is
discrete. The remark after the definition states an equivalent condition: for
every étale `U → X` and every `f ∈ F(U)`, each point of `U` has a distinguished
open neighbourhood `U'` such that the stabilizer of `f|U'` is open in
`G_{U'}`.

This module is derived infrastructure that abstracts these two conditions to an
arbitrary site. The objects with their canonical actions of open subgroups are
replaced by the admissible family of the supplied `LocalActionSystem`. Group
elements act on an object through endomorphisms of the site, so the site must
contain arrows that realize the group action. The published transport category
`ActionOpens` is such a site. `IsDiscrete` has the shape of Definition 1.4.1.
`IsLocallyDiscrete` has the shape of the remark, with covering sieves in place
of neighbourhoods of points. `IsDiscreteSection.of_agree` corresponds to the
agreement of the two extensions on `N`: discreteness of a section does not
depend on that choice. "Discrete" follows Berkovich; "smooth" in
`smoothSheafProperty` follows Harris, *Galois properties of cohomological
automorphic forms on GL(n)* (1999), section 2, printed p.304, which uses such
sheaves of smooth modules.

The module does not construct Berkovich's quasi-étale or étale sites, the Key
Lemma, the canonical actions `G_U`, compactness or distinguished
neighbourhoods. It does not prove the equivalence of Definition 1.4.1 with the
remark or Theorem 1.4.2. In the generic setting the two conditions differ.
`IsDiscrete` implies `IsLocallyDiscrete` only when `Covers` holds, and the
converse is not proved. If the system has no admissible local actions, every
presheaf is discrete, but every discrete sieve is empty. A presheaf is then
locally discrete only if the empty sieve covers every object over which it has
a section. Nothing is asserted about
cohomology of such sheaves. The comparison with the published smooth
equivariant sheaves on the transport category is in
`Langlands.Sheaf.Equivariant.ActionOpensLocalAction`.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules are present in Library commit
`ddb0a9c0d562246b405e8f1149220107e7407d1d`.
