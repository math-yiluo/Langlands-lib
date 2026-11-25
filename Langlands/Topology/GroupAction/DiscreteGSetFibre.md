# The fibre of a presheaf on `P(G)` as a smooth representation

Builds on the following modules:

- `Langlands.Topology.GroupAction.DiscreteGSetSite` (imported): Berkovich's
  category `DiscreteGSet G = P(G)`. Its objects are the `G`-sets (objects of
  `Action (Type z) G`) all of whose stabilizers are open, and its morphisms are the `G`-maps.
  The module also provides the forgetful functor `DiscreteGSet.forget`, the discrete `G`-set
  `DiscreteGSet.quotient G N hN` of `G ⧸ N` for an open subgroup `N`, the lemma
  `isOpen_stabilizer_quotient`, the `MulAction` instance on underlying sets, and
  `Action.gMap`, the `G`-map underlying a morphism.
- `Langlands.Representation.Category.Basic` (imported): `SmoothRep R G`, with
  `SmoothRep.of`, `SmoothRep.ofHom` and `SmoothRep.hom`.
- `Langlands.Representation.Smooth.SmoothPart.Definitions` and
  `Langlands.Representation.Smooth.Definitions` (through the imports): `fixedVectors ρ H`,
  `smoothVectors ρ` (the submodule of vectors fixed by some open subgroup) and `IsSmooth ρ`.
- Mathlib: `Functor.Elements`, `InducedCategory`, `colimit.desc`, `colimMap`,
  `Functor.final_of_exists_of_isFiltered`, `Functor.Final.colimitIso`,
  `MulAction.stabilizer_quotient`, `MulAction.exists_smul_eq`, and
  `ModuleCat.hasColimitsOfShape`.

All declarations are in the namespace `Langlands.DiscreteGSet`.

## Purpose

Let `G` be a topological group and `P` a presheaf of `R`-modules on `P(G)`. This module
defines the fibre of `P`, a smooth representation of `G` that is functorial in `P`. It is
the colimit of the modules `P(G ⧸ N)`, one for each open subgroup `N` and point
`a ∈ G ⧸ N`. An element `g ∈ G` sends the copy of `P(G ⧸ N)` at `a` to the copy at `g • a`.
The module also proves that the fibre is the colimit of the `P(G ⧸ N)` over the open
subgroups `N` alone (`colimitOpenSubgroupIsoFibre`). This is the colimit Berkovich writes
`lim→_N`.

Applied to `Σ ↦ F(X_Σ(G))`, the fibre is Berkovich's `Γ_{X{G}}(F)`; see
`AnalyticSetInducedSections`.

## Setting

`G : Type z` is a group with a topology and `[IsTopologicalGroup G]`. In the sections on the
fibre, `C` is any category with colimits over `(PointedOrbit G)ᵒᵖ`. In the sections on
modules, `R : Type uR` is a commutative ring and modules live in `ModuleCat.{w} R`.

## Orbits and pointed orbits

- `orbit G N`: the discrete `G`-set `G ⧸ N` of an open subgroup `N`.
- `OrbitCategory G`: the orbit category. Its objects are the open subgroups `N` and its
  morphisms `N ⟶ N'` are the `G`-maps `G ⧸ N → G ⧸ N'`. It is the `InducedCategory` of
  `P(G)` along `orbit G`, and `orbitFunctor G` is its inclusion in `P(G)`.
- `orbitPoints G`: the functor `N ↦ G ⧸ N` to sets.
- `PointedOrbit G`: the category of elements of `orbitPoints G`. Its objects are pairs
  `(N, a)` of an open subgroup `N` and a point `a ∈ G ⧸ N`, written `PointedOrbit.mk N a`.
  The point is `PointedOrbit.pt`. A morphism `(N, a) ⟶ (N', a')` is a `G`-map
  `G ⧸ N → G ⧸ N'` sending `a` to `a'`.
- `PointedOrbit.stabilizer x`: the stabilizer of the point of `x`, as an open subgroup (open
  by `isOpen_stabilizer_quotient`).
- `orbitMap f`: the map of sets of a morphism `f` of the orbit category. `orbitMap_smul`:
  it commutes with the action of `G`. `orbitCategory_hom_ext`: a morphism of the orbit
  category is determined by its map of sets.
- `PointedOrbit.hom_ext`: any two morphisms between the same pointed orbits are equal.
  Proof: every element of `G ⧸ N` is `g • a` for the point `a`
  (`MulAction.exists_smul_eq`), and both maps send `g • a` to `g • a'`.
- `quotientGMap s h`: for a `G`-set `S`, a point `s` and `h : N ≤ stabilizer s`, the `G`-map
  `G ⧸ N → S`, `gN ↦ g • s`. `quotientGMap_mk` states its value on `gN`.
  `orbitHom a h`: the corresponding morphism `N ⟶ N'` of the orbit category, for
  `a ∈ G ⧸ N'`. `orbitMap_orbitHom` states that its map of sets is `quotientGMap a h`.
- `translate g`: the functor `(N, a) ↦ (N, g • a)` on pointed orbits. It is the identity on
  the underlying morphisms of the orbit category.

## Base points

- `basePoint G : OpenSubgroup G ⥤ PointedOrbit G`: `N ↦ (N, [1])`, where `[1]` is the class
  of `1` in `G ⧸ N`. For `N ≤ N'` the morphism is the projection `G ⧸ N → G ⧸ N'`, which is
  `orbitHom [1] h` with `h` from `MulAction.stabilizer_quotient`. Functoriality holds by
  `PointedOrbit.hom_ext`.
- `basePointHom x`: for `x = (N, a)`, the morphism `(G_a, [1]) ⟶ (N, a)`, `g G_a ↦ g • a`,
  where `G_a = x.stabilizer`.
- Instance `final_basePoint_op`: `(basePoint G).op` is final. Proof:
  `Functor.final_of_exists_of_isFiltered`. The category `(OpenSubgroup G)ᵒᵖ` is filtered,
  because `OpenSubgroup G` is a nonempty meet-semilattice. Every pointed orbit `x` receives
  the morphism `basePointHom x` from a base point. Two morphisms from a base point to `x`
  are equal by `PointedOrbit.hom_ext`.

## The fibre and its `G`-action

Let `P : (DiscreteGSet G)ᵒᵖ ⥤ C`.

- `fibreDiagram P`: the diagram `(N, a) ↦ P(G ⧸ N)` on `(PointedOrbit G)ᵒᵖ`. It is the
  composite of `P` with the opposite of the projection to the orbit category and of
  `orbitFunctor G`.
- `fibre P`: the colimit of `fibreDiagram P`.
- `colimitOpenSubgroupIsoFibre P`: **Berkovich's formula**. It is an isomorphism from the
  colimit of `(basePoint G).op ⋙ fibreDiagram P` to `fibre P`. That diagram sends `N` to
  `P(G ⧸ N)` and, for `N ≤ N'`, has the restriction `P(G ⧸ N') → P(G ⧸ N)` along the
  projection. So the colimit runs over the open subgroups `N`, ordered by reverse
  inclusion. The isomorphism is `Functor.Final.colimitIso` for the final functor
  `(basePoint G).op`, and `ι_colimitOpenSubgroupIsoFibre_hom` describes it on colimit
  injections.
- `ι_congr`: the colimit injection at `PointedOrbit.mk N a` depends only on `N` and `a`.
- `fibreAct P g`: the endomorphism of `fibre P` sending the injection at `x` to the
  injection at `(translate g).obj x` (`ι_fibreAct`), defined by `colimit.desc`.
  `fibreAct_one`: `fibreAct P 1 = 𝟙`. `fibreAct_mul`:
  `fibreAct P (g * h) = fibreAct P h ≫ fibreAct P g`.
- `fibreMap α`: the morphism of fibres induced by a morphism of presheaves `α : P ⟶ Q`
  (`colimMap` of the whiskered transformation), with `fibreMap_id` and `fibreMap_comp`.
  `fibreAct_fibreMap`: `fibreAct P g ≫ fibreMap α = fibreMap α ≫ fibreAct Q g`.

## The fibre of a presheaf of modules

Let `P : (DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R`, with colimits over `(PointedOrbit G)ᵒᵖ` in
`ModuleCat.{w} R`.

- `fibreRepresentation P`: the representation `g ↦ (fibreAct P g).hom` of `G` on the module
  `fibre P`. `fibreRepresentation_apply` unfolds it, and `fibreRepresentation_ι_apply`
  states that `g` sends the image of `y ∈ P(G ⧸ N)` under the injection at `x` to its image
  under the injection at `(translate g).obj x`.
- `ι_apply_mem_fixedVectors`: the image of `P(G ⧸ N)` under the injection at `x = (N, a)` is
  fixed by `x.stabilizer`. Proof: `(N, k • a) = (N, a)` for `k` in the stabilizer, by
  `ι_congr`.
- `isSmooth_fibreRepresentation`: **the fibre is smooth**. Proof: by
  `ι_apply_mem_fixedVectors`, the submodule `S = smoothVectors (fibreRepresentation P)`
  contains the images of all colimit injections. So the quotient map `fibre P → fibre P ⧸ S`
  vanishes on every injection and is zero by `colimit.hom_ext`. Hence `S` is everything.
- `fibreRep P`: the fibre as an object of `SmoothRep.{uR, z, w} R G`.
- `fibreIntertwiningMap α`: `fibreMap α` as an intertwining map.
- `fibreFunctor G R`: **the fibre functor**
  `((DiscreteGSet G)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤ SmoothRep.{uR, z, w} R G`, `P ↦ fibreRep P`. The
  lemmas `fibreFunctor_obj` and `fibreFunctor_map_hom` unfold it.
- `hasColimitsOfShape_pointedOrbit G R`: colimits over `(PointedOrbit G)ᵒᵖ` exist in
  `ModuleCat.{max z w} R`. This is a theorem rather than an instance, since its universe
  levels are not determined by its conclusion; callers use it with `haveI`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers. §1.2, printed p.4:

> We also denote by Γ_{X{G}} the functor from X(G)~_qét (resp. X(G)~_ét) to the category of
> (discrete) G-sets by Γ_{X{G}}(F) = lim→_N F(X_{G/N}(G)), where N runs through open
> subgroups of G. The simplest way to see that Γ_{X{G}}(F) is really a G-set is as follows.
> Let P(G) denote the category of G-sets endowed with the Grothendieck topology generated by
> the pretopology for which the sets of coverings consist of surjective families of G-maps.
> It is well known that any sheaf F ∈ P(G)~ is representable by the G-set ∪_N F(G/N), where
> N runs through open subgroups of G.

## Provenance

Derived. Berkovich takes the colimit `lim→_N` over the open subgroups and obtains the action
of `G` from the representability of sheaves on `P(G)`. Here the fibre is defined as a
colimit over the pointed orbits `(N, a)` instead, so that `g ∈ G` acts by moving the point,
`(N, a) ↦ (N, g • a)`, with no choice of coset representatives. The comparison with
Berkovich's colimit over the open subgroups is proved: `colimitOpenSubgroupIsoFibre`.

The fibre is a colimit over the category of elements of the underlying-set functor on the
orbits. Informally, this is the stalk of `P` at the point of the topos `P(G)~` given by the
forgetful functor, and `G` acts through the automorphisms `s ↦ g • s` of that functor. For
the presheaf `Hom(-, S)` of a discrete `G`-set `S`, sending `(N, a, f)` to `f(a)` identifies
the fibre with `S`, compatibly with the actions of `G`. This remark is not formalized.

The construction is made for presheaves of modules, so it gives smooth representations
rather than `G`-sets. The sheaf condition is not used.

## Not claimed

- The representability of sheaves on `P(G)` and the equivalence `P(G) ≃ P(G)~`.
- `fibre(P)^N ≅ P(G ⧸ N)` for sheaves `P`, and any exactness of the fibre functor.
