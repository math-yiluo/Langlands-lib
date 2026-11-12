# Derived sections of discrete sheaves as representations

Author: Worker 26. Builds on `Langlands.Sheaf.Equivariant.LocalAction`
(Worker 13: local action systems, discreteness, `localRepresentation`),
`Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (Worker 26: the abelian
category `L.DiscreteSheaf (ModuleCat R) J` of discrete module sheaves, its exact
inclusion and enough injectives) and `Langlands.Representation.Category.Abelian`
(the abelian category `SmoothRep R G` of smooth representations). Uses Mathlib's
`Rep`, sheaf limits and right derived functors.

Throughout, `T : Type u` is a category with `Category.{v} T`, `R : Type uR` is a
commutative ring, and module presheaves take values in `ModuleCat.{w} R`.

## Sections as representations

Let `K : Type uK` be a monoid, `U : T` and `a : K →* (End U)ᵐᵒᵖ` an action of `K`
on `U` by endomorphisms.

- `actionRepresentation F a`, for `F : Tᵒᵖ ⥤ ModuleCat R`: the representation
  of `K` on `F(U)` in which `k` acts by `F.map (a k).unop.op`
  (`actionRepresentation_apply`). The unit and product laws follow from
  functoriality of `F`; the opposite monoid makes the action a left action.
  `actionRepresentation_eq_localRepresentation`: for an open subgroup `H` of a
  topological group, this is the published `localRepresentation` (by `rfl`).
- `actionIntertwiningMap φ a`: a morphism of presheaves `φ : F ⟶ F'` gives an
  intertwiner `F(U) ⟶ F'(U)`, by naturality of `φ` along `(a k).unop`
  (`actionIntertwiningMap_apply`).
- `sectionsRep R a : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R K`: sections over `U`
  as a representation of `K`, functorially (`sectionsRep_obj_ρ`,
  `sectionsRep_map_hom_apply`). It is additive (`sectionsRep_additive`).
  `sectionsRepForgetIso a`: composed with the forgetful functor to modules it is
  evaluation at `U`.
- For a Grothendieck topology `J`, `sheafSectionsRep R J a` is the composite
  with `sheafToPresheaf`. It is additive and preserves finite limits
  (`sheafSectionsRep_preservesFiniteLimits`): its composite with the forgetful
  functor `Rep R K ⥤ ModuleCat R` is evaluation of sheaves at `U`, which
  preserves finite limits, and that forgetful functor reflects them.

## Discrete sheaves

Let `G : Type uG` be a group with a topology and `L : LocalActionSystem T G`.
`R` is an explicit argument of the following declarations.

Representation-valued, for any monoid action `a : K →* (End U)ᵐᵒᵖ`:

- `discreteSectionsRep R L J a : L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ Rep.{w} R K`
  is the inclusion of discrete sheaves followed by `sheafSectionsRep R J a`;
  additive. Under `[HasSheafify J (ModuleCat.{w} R)]` and
  `[L.HasFiniteEquivariantRefinements J]` it preserves finite limits, since
  both factors do.
- With moreover `[EnoughInjectives (Sheaf J (ModuleCat.{w} R))]`, so that
  discrete sheaves have injective resolutions:
  `discreteDerivedRep R L J a q` is the `q`-th right derived functor (Mathlib's
  `Functor.rightDerived`) of `discreteSectionsRep R L J a`. It is the
  cohomology over `U`, computed with injective resolutions among discrete
  sheaves, as a representation of `K`. `discreteDerivedRepZeroIso`: degree
  zero is the sections functor. `discreteDerivedRepIso`: for an injective
  resolution `I` of `F` among discrete sheaves, the value at `F` is the
  homology of the sections of `I`. `isZero_discreteDerivedRep_succ_of_injective`:
  it vanishes in positive degrees on injective discrete sheaves.

Smooth, for an admissible local action `ha : L.IsAdmissible U H a` of an open
subgroup `H`, with the subspace topology on `H`:

- `isSmooth_actionRepresentation R L J ha F`: for a discrete module sheaf `F`,
  the representation of `H` on `F(U)` is smooth. This is
  `LocalActionSystem.isDiscrete_iff_isSmooth`.
- `discreteSectionsSmooth R L J ha : L.DiscreteSheaf (ModuleCat.{w} R) J ⥤
  SmoothRep.{uR, uG, w} R H` lifts `discreteSectionsRep R L J a` to smooth
  representations. `discreteSectionsSmoothToRepIso`: followed by the inclusion
  `SmoothRep.toRep` it is `discreteSectionsRep R L J a`. It is additive, and
  under the two hypotheses above it preserves finite limits: its composite with
  the fully faithful `SmoothRep.toRep` does.
- With `[EnoughInjectives (Sheaf J (ModuleCat.{w} R))]`:
  `discreteDerived R L J ha q` is its `q`-th right derived functor, the
  cohomology over `U` with coefficients in a discrete sheaf as a smooth
  representation of `H`. `discreteDerivedZeroIso`, `discreteDerivedIso` and
  `isZero_discreteDerived_succ_of_injective` are the degree-zero
  identification, the computation by an injective resolution among discrete
  sheaves, and the vanishing on injective discrete sheaves.

`discreteSheaf_enoughInjectives_of_small` (in `LocalActionDiscretePart`)
supplies the enough-injectives hypothesis for a small site `T : Type w` and a
ring `R : Type w`, where Mathlib also provides sheafification.

## Provenance and scope

Derived infrastructure. Sources, read in the original by Worker 26:

- Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
  1995–1996 manuscript), §1.4, printed p.7 = PDF p.7: for a `G`-sheaf and
  `U(H) → X(G)`, "the set `F(U)` is endowed with a canonical action of the
  group `H`"; Definition 1.4.1 (pp.7–8) requires the action of `G_U` on `F(U)`
  to be discrete for compact `U`. §1.5, printed p.11 = PDF p.11: cohomology
  groups are defined as "the values of the high direct images" of section
  functors, and Corollary 1.5.2 speaks of the canonical action of `G` on them.
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), §2, printed p.304 = PDF p.6: étale sheaves in smooth
  `Z/ℓ^m Z[S(ẽ)]`-modules over `U(ẽ)` (Berkovich's discrete sheaves), whose
  compactly supported cohomology `H^q_c(U(ẽ), ·)` Harris uses; compact
  supports are not treated in this module.

Correspondence and differences. `discreteSectionsSmooth` is the section functor
over an object with an admissible local action, on the category of discrete
sheaves, with values in smooth representations; `discreteDerived` is its right
derived functor. In Berkovich's setting the discrete sheaves are the category
`T_G(X_ét)`, which Theorem 1.4.2 identifies with sheaves on `X(G)_ét`; his
cohomology groups are derived functors on that category. The present module
works on an arbitrary site with a local action system, derives within the
category of discrete sheaves, and does not compare these derived functors with
derived functors computed among all sheaves; such a comparison is a theorem,
not proved or assumed here. Compact supports, Godement resolutions and the
analytic specialization are not treated here.

Universes: `T : Type u` with `Category.{v} T`, `G : Type uG`, `K : Type uK`,
`R : Type uR`, modules and representations with carriers in `Type w`.

Source registrations: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, file
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
