# The locally discrete part of a sheaf for a local action system

Author: Worker 26. Built on the published local action systems of
`Langlands.Sheaf.Equivariant.LocalAction` (Worker 13). Also uses the published
`Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (Worker 26), Mathlib's
sheaves of modules, its abelian structure on sheaf categories, its abelian full
subcategories (`Mathlib.CategoryTheory.Abelian.Subcategory`) and its Grothendieck
abelian categories.

Let `T` be a category, `J` a Grothendieck topology on `T`, `G` a group with a
topology, and `L : LocalActionSystem T G` a local action system. A local action
of an open subgroup `H` on an object `U` is a monoid homomorphism
`H →* (End U)ᵐᵒᵖ`. Recall from `LocalAction` the following. The discrete sieve
`L.discreteSieve F s` of a section `s` over `U` consists of the arrows `W ⟶ U`
that factor as `k ≫ f` with `f : V ⟶ U`, where `V` carries an admissible local
action for which `F.map f.op s` is discrete. A presheaf is locally discrete,
`L.IsLocallyDiscrete J F`, when every discrete sieve covers.
`L.smoothSheafProperty A J` is this property for sheaves, `L.SmoothSheaf A J`
the full subcategory and `L.smoothSheafInclusion A J` its inclusion functor.

The module answers the following question. Under a refinement hypothesis on the
site, do locally discrete sheaves of modules form an abelian category with
enough injectives, in which kernels and cokernels are those of all sheaves? It
mirrors `LocalActionDiscretePart` for the locally discrete condition. It does
not construct any site or local action system.

## Restriction of discreteness

`IsRestrictionEquivariant a b p`: here `a` is a local action of `H` on `U`, `b`
a local action of `H'` on `V`, and `p : V ⟶ U` an arrow. The proposition says
the following. For every open subgroup `K ≤ H` there is an open subgroup
`M ≤ H'` such that every `h ∈ H'` with `h ∈ M` has some `k ∈ H` with `k ∈ K` and
`(b h).unop ≫ p = p ≫ (a k).unop`. This is the dual of `IsLocallyEquivariant`
of `LocalActionDiscretePart`: the roles of the two actions are exchanged, so it
moves discreteness from `U` to `V` instead of from `V` to `U`.

- `isRestrictionEquivariant_of_intertwines`: an arrow intertwining the two
  actions on a common open subgroup `N ≤ H ⊓ H'` satisfies the condition, with
  `M = N ⊓ K` and `k = h`. Berkovich's "N-morphisms" are of this kind.
- `map_op_comp_apply`: restricting a section along `x ≫ y` is restricting along
  `y` and then along `x`. The coefficient category is any concrete category.
- `IsDiscreteSection.restrict`: if `p` restricts discreteness from `a` to `b`
  and `s` is discrete for `a`, then `F.map p.op s` is discrete for `b`. If `K`
  fixes `s`, the subgroup `M` given by the hypothesis fixes the restriction.

## The refinement hypothesis

`L.fiberRefinementSieve f₁ f₂ k₁ k₂` is defined for a cospan
`f₁ : V₁ ⟶ U`, `f₂ : V₂ ⟶ U` and arrows `k₁ : W ⟶ V₁`, `k₂ : W ⟶ V₂`. It is the
sieve of arrows `e : W' ⟶ W` with the following property. There are an object
`V` with an admissible local action, an arrow `k : W' ⟶ V` and arrows
`p₁ : V ⟶ V₁`, `p₂ : V ⟶ V₂` with `p₁ ≫ f₁ = p₂ ≫ f₂`, `k ≫ p₁ = e ≫ k₁` and
`k ≫ p₂ = e ≫ k₂`.

`LocalActionSystem.HasAdmissibleRefinements L J` is a class with two fields.

- `isRestrictionEquivariant`: every arrow `p : V' ⟶ V` between objects with
  admissible local actions `a'` and `a` satisfies
  `IsRestrictionEquivariant a a' p`.
- `fiberRefinementSieve_mem`: for every cospan `f₁, f₂` and every cone
  `k₁, k₂` over it (`k₁ ≫ f₁ = k₂ ≫ f₂`), the sieve
  `L.fiberRefinementSieve f₁ f₂ k₁ k₂` covers `W`.

`HasAdmissibleRefinements.covers` derives `L.Covers J` from the second field,
applied to the cospan and cone of identities of `U`.

The class is an explicit hypothesis. No instance is constructed here. The
intended analytic reading is as follows; this module does not prove it. Take
as admissible objects the compact quasi-étale or distinguished
étale objects with their canonical actions of open subgroups. Then the first
field is the Key Lemma statement that a morphism between such objects is an
`N`-morphism for a small open subgroup `N`. The second field says that each
fibre product `V₁ ×_U V₂` is covered by distinguished étale objects.

Why these fields: the locally discrete sections must be shown to form a
submodule which is stable under restriction.

- Zero: the zero section is discrete for every action, so its discrete sieve
  contains the sieve of arrows factoring through admissible objects. This
  covers by `covers`.
- Sums: let `s` and `t` be locally discrete over `U`. An arrow `g : W ⟶ U` in
  both discrete sieves factors as `k₁ ≫ f₁`, with `s` discrete on `V₁` for an
  action `a₁`, and as `k₂ ≫ f₂`, with `t` discrete on `V₂` for an action `a₂`.
  The two objects and actions are unrelated. The second field refines `W` by
  admissible `V` mapping to `V₁` and `V₂` over `U`. The first field moves both
  discreteness statements to the action on `V`, where the sum is discrete.
- Restriction along `g : U' ⟶ U`: an arrow `h : W ⟶ U'` in the pullback of the
  discrete sieve of `s` satisfies `h ≫ g = k₁ ≫ f₁` with `s` discrete on `V₁`.
  To lie in the discrete sieve of `F.map g.op s`, an arrow must factor through
  an admissible `V` by an arrow `V ⟶ U'`. In general `f₁` does not factor
  through `g`, so `V₁` does not map to `U'`. A fibre product of `f₁` and `g`
  would map to both, but the site need not have one, and it need not carry an
  admissible local action. The second field, for the cospan `f₁, g` and the
  cone `k₁, h`, provides admissible `V` with arrows to `V₁` and `U'`. The first
  field moves discreteness from `V₁` to `V`.

The two theorems that implement this, for presheaves with values in any
concrete category, are:

- `LocalActionSystem.discreteSieve_map_mem`: if the discrete sieve of `s` covers
  `U`, the discrete sieve of `F.map g.op s` covers `U'`.
- `LocalActionSystem.discreteSieve_mem_of_pair`: let `s₁`, `s₂` and `t` be
  sections of three presheaves over `U`, the first two with covering discrete
  sieves. Suppose that, on every object `V` with admissible `b` and every
  `f : V ⟶ U`, discreteness of the restrictions of `s₁` and `s₂` for `b`
  implies discreteness of the restriction of `t`. Then the discrete sieve of
  `t` covers `U`.

`LocalActionSystem.smoothSheafInclusion_full` and
`LocalActionSystem.smoothSheafInclusion_faithful` record that the inclusion
functor `smoothSheafInclusion`, a `def` in `LocalAction`, is fully faithful.

## Modules: the locally discrete part

From here on, `R` is a commutative ring with `R : Type uR`, coefficients are in
`ModuleCat.{w} R`, and `F : Tᵒᵖ ⥤ ModuleCat.{w} R`.

`isDiscreteSection_of_pair` (no refinement hypothesis): for a binary product
`limit D` of module sheaves, a section is discrete for `b` when its two
projections are. Two fixing open subgroups have an intersection fixing both
projections, and `sheaf_limit_sections_ext` of `LocalActionDiscretePart`
finishes.

The remaining declarations are in the namespace `LocalActionSystem`. They
assume `[L.HasAdmissibleRefinements J]`, because the submodule itself uses
it. The names avoid the published `smoothSubmodule`, `smoothCoreflector`, ...
for topological `G`-sheaves in `Langlands.Sheaf.Equivariant.SmoothPart`.

- `LocalActionSystem.smoothSubmodule L J F U` is the submodule of sections `s`
  over `U` whose discrete sieve covers `U`. Zero, sums and scalar multiples are
  handled as described above; for scalar multiples the discrete sieve of `s` is
  contained in that of `r • s`. `mem_smoothSubmodule_iff` unfolds membership.
- `map_mem_smoothSubmodule`: restriction preserves the locally discrete
  submodules, by `discreteSieve_map_mem`. `map_mem_smoothSubmodule_of_hom`: so
  does every morphism of presheaves, since the discrete sieve can only grow.
- `isLocallyDiscrete_iff_forall_mem`: `L.IsLocallyDiscrete J F` holds exactly
  when every section lies in the locally discrete submodule.
- `mem_smoothSubmodule_of_covering`: membership is local. If the restrictions
  of `s` along the arrows of a covering sieve lie in the locally discrete
  submodules, so does `s` (`discreteSieve_mem_of_covering` of `LocalAction`).
  No compactness is needed, unlike `mem_discreteSubmodule_of_covering`.
- `smoothPresheaf L J F` is the presheaf `U ↦ smoothSubmodule L J F U`, with the
  restricted restriction maps. `smoothPresheafι L J F` is its inclusion into
  `F`, injective on sections by `smoothPresheafι_app_injective`.
  `smoothPresheafMap L J φ` is the restriction of a morphism `φ`, and
  `smoothPresheafFunctor L J` is the resulting endofunctor of presheaves.
- `isLocallyDiscrete_smoothPresheaf`: the locally discrete part is locally
  discrete. Along the injective inclusion discrete sieves do not change
  (`discreteSieve_map_of_injective`).
- `smoothPresheaf_isSheaf`: the locally discrete part of a sheaf is a sheaf.
  The proof checks the sheaf condition for each test module `E` and covering
  sieve. Separatedness: compose with the injective inclusion and use uniqueness
  of gluing in `F`. Existence: glue the family composed with the inclusion in
  `F`. Every value of the gluing has restrictions in the locally discrete parts
  along the sieve, so it lies in the locally discrete part by
  `mem_smoothSubmodule_of_covering`. Then restrict the codomain.
- `smoothSubsheafFunctor L J` is the endofunctor of `Sheaf J (ModuleCat R)`
  taking a sheaf to its locally discrete part. `smoothSubsheafι L J` is the
  natural inclusion into the identity. `isLocallyDiscrete_smoothSubsheaf` says
  the image is locally discrete. `smoothCoreflector L J` is the corestricted
  functor `Sheaf J (ModuleCat R) ⥤ L.SmoothSheaf (ModuleCat R) J`.
- `smoothLift hS f`: a morphism `f : S ⟶ F` from a locally discrete sheaf
  factors through the locally discrete subsheaf of `F`. `smoothLift_comp_ι`
  records the factorization.
- `smoothAdjunction L J`: `L.smoothSheafInclusion (ModuleCat R) J` is left
  adjoint to `smoothCoreflector L J`. The hom bijection sends `f` to
  `smoothLift _ f`, and its inverse composes with the inclusion.

## Abelian structure

This section also assumes `[HasSheafify J (ModuleCat.{w} R)]`, so that
`Sheaf J (ModuleCat R)` is abelian in Mathlib.

- `mono_smoothSubsheafι_app`: the inclusion of the locally discrete part is a
  monomorphism.
- `smoothSheafProperty_isClosedUnderSubobjects`: a subsheaf of a locally
  discrete sheaf is locally discrete. A monomorphism is injective on sections
  (`injective_app_of_mono`), and `IsLocallyDiscrete.of_injective` applies.
- `smoothSheafProperty_of_isIso`: a sheaf is locally discrete if the inclusion
  of its locally discrete part is an isomorphism.
  `smoothSheafProperty_isClosedUnderQuotients`: a quotient of a locally
  discrete sheaf is locally discrete. An epimorphism from a locally discrete
  sheaf factors through the locally discrete subsheaf of the target. So that
  inclusion is an epimorphism and a monomorphism, hence an isomorphism.
- `smoothSheafProperty_containsZero`: the zero sheaf is locally discrete, being
  a subobject of its own locally discrete part.
- `smoothSheafProperty_isClosedUnderBinaryProducts`: apply
  `discreteSieve_mem_of_pair` to the two projections of a section, with
  `isDiscreteSection_of_pair`. `smoothSheafProperty_isClosedUnderFiniteProducts`
  follows.
- `smoothSheaf_abelian`: `L.SmoothSheaf (ModuleCat R) J` is abelian. This is
  Mathlib's instance for full subcategories closed under kernels, cokernels and
  finite products, and containing zero.
- `smoothSheafInclusion_preservesMonomorphisms`,
  `smoothSheafInclusion_preservesEpimorphisms`,
  `smoothSheafInclusion_preservesFiniteLimits`,
  `smoothSheafInclusion_preservesFiniteColimits`: the inclusion into all module
  sheaves preserves monomorphisms, epimorphisms, finite limits and finite
  colimits, so it is exact. Kernels and cokernels are computed among all
  sheaves (Mathlib's `preservesKernels_ι`, `preservesCokernels_ι`).
- `injective_smoothCoreflector_obj`: the locally discrete part of an injective
  module sheaf is injective among locally discrete sheaves. A right adjoint of
  a functor preserving monomorphisms preserves injectives.
- `smoothSheaf_enoughInjectives`: if `Sheaf J (ModuleCat R)` has enough
  injectives, so do locally discrete module sheaves (Mathlib's
  `EnoughInjectives.of_adjunction`, with the fully faithful inclusion).

`LocalActionSystem.smoothSheaf_enoughInjectives_of_small` instantiates this for
a small site `T : Type w` (a `SmallCategory`) and a ring `R : Type w`. Mathlib
then supplies sheafification and shows that `Sheaf J (ModuleCat.{w} R)` is a
Grothendieck abelian category with enough injectives. So under
`[L.HasAdmissibleRefinements J]` the locally discrete module sheaves have
enough injectives, and right derived functors on them are available.

## Provenance and scope

Derived infrastructure. Source, read in the original by Worker 26: Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), §1.4, printed pp.7–8 = PDF pp.7–8.

- Printed p.7: an étale morphism `𝒰 → X` is distinguished if it factors as
  `𝒰 ↪ U → X` with `U` compact, `U → X` quasi-étale and `𝒰` a distinguished
  open subset of `U`. The action of `G` on `X` then extends canonically to a
  continuous action of an open subgroup `G_𝒰` on `𝒰`. "If there is another
  representation of the morphism `𝒰 → X` as a composition `𝒰 ↪ U' → X` and,
  therefore, an extension of the action of `G` on `X` to a continuous action of
  an open subgroup `G'_𝒰 ⊂ G` on `𝒰`, then one can find an open subgroup
  `N ⊂ G_𝒰 ∩ G'_𝒰` such that the two actions of `N` on `𝒰` coincide. (For this
  it suffices to apply the Key Lemma to the quasi-étale morphism
  `U ×_X U' → X`.)"
- Printed p.8, the remark after Definition 1.4.1: "It is easy to see that an
  étale `G^d`-sheaf `F` is a `G`-sheaf if and only if for any étale morphism
  `U → X` and any element `f ∈ F(U)` each point of `U` has a distinguished open
  neighborhood `𝒰` such that the stabilizer of `f|_𝒰` is open in `G_𝒰`."
- Printed p.8, step A.2 of the proof of Theorem 1.4.2: for a finite
  quasi-étale covering `{U_i → U}` by compact spaces, "the Key Lemma implies
  that for a sufficiently small open subgroup `N` ... the morphisms `U_i → U`
  and `U_i ×_U U_j → U_i` are in fact `N`-morphisms". Theorem 1.4.2 identifies
  the category of étale `G`-sheaves with the category of sheaves on the site
  `X(G)_ét`, from which its abelian structure and enough injectives follow.
  That theorem is neither formalized nor used here.

Correspondence and differences. `IsLocallyDiscrete` (from `LocalAction`) has
the shape of the remark, with covering sieves in place of distinguished
neighbourhoods of points. The first field of `HasAdmissibleRefinements`
abstracts the `N`-morphism statements of p.7 and step A.2. The second field
abstracts covering fibre products by distinguished étale objects. Both fields,
the name `fiberRefinementSieve` and the dual condition
`IsRestrictionEquivariant` are choices made for this formalization; they are
the properties the proof needs. The present module does not build Berkovich's
sites, the Key Lemma actions or the `G^d`-sheaf structure. It does not prove
that `HasAdmissibleRefinements` holds for an analytic étale site; this belongs
to the analytic specialization. The abelian structure and enough injectives are
proved directly through the locally discrete part, not via Theorem 1.4.2.
"Smooth" in the names follows `smoothSheafProperty` of `LocalAction`.

Universes: `T : Type u` with `Category.{v}`, `G : Type uG`, `R : Type uR`,
modules in `ModuleCat.{w} R`. The final small-site theorem takes `T : Type w`,
`SmallCategory T` and `R : Type w`.

Source registration: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
