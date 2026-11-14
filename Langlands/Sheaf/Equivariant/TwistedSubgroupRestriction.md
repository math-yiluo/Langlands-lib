# Restriction of twisted sheaves to a subgroup

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedOver` (through the imports): the twisted category
  `TwistedOver P ρ` of a `G`-object `X`, its morphisms (`homMk`, `hom_ext`, the twist
  `Hom.twist`, the underlying arrow `Hom.left` and the compatibility `Hom.w`), the inclusion
  `ι P ρ` of `P.Over ⊤ X`, the translation functors `translate P ρ g`, the relabelling arrows
  `relabel ρ g U : (ι P ρ).obj U ⟶ (ι P ρ).obj ((translate P ρ g).obj U)` (twist `g`,
  identity underlying arrow, an isomorphism), translation-invariant topologies `IsTranslationInvariant`, the
  twisted topology `twistedTopology ρ J`, `isSheaf_of_isSheaf_comp`, and the restriction
  `restriction ρ J A` of sheaves on the twisted site to sheaves over `X`.
- `Langlands.Sheaf.Equivariant.TwistedLeftInduction` (through the imports): the template for
  the coset argument below. There the translates of `V` by all of `G` are final among the
  costructured arrows of `V` for `(ι P ρ).op`; here the translates by representatives of the
  cosets `H\G` are final for the subgroup inclusion.
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections`: `sheafGlobalSectionsRep J R`, the
  global sections of module sheaves on the twisted site as representations of `G` (`g` acts
  by restriction along the endomorphism `g⁻¹` of the base object).
- `Langlands.Sheaf.Equivariant.TwistedCompactSupport`: `PointEquivariance ρ Φ` (natural
  isomorphisms `fiberIso g i : translate P ρ g ⋙ (Φ (g • i)).fiber ≅ (Φ i).fiber` of fibre
  functors) and `sheafCompactSectionsRep J R E`, the compactly supported global sections as
  representations of `G`.
- `Langlands.Sheaf.Equivariant.TwistedRepCohomology` (imported): the right derived functors
  `sheafGlobalRepDerived J R q` and `sheafCompactRepDerived J R E q` of these two
  representation-valued functors.
- `Langlands.Cohomology.ExactBaseChange` and `Langlands.Cohomology.ExactBaseChange.ResolutionProof`
  (through the imports): the base change transformation `baseChangeNatTrans τ q` of a
  transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂` along exact functors `α`, `β`,
  `quasiIso_mapResolutionAugmentation`, and the criterion
  `isIso_baseChangeNatTrans_app_of_acyclic`; `Langlands.Cohomology.AcyclicResolution`:
  `mapResolutionAugmentation`.
- Mathlib: `Rep.resFunctor` (restriction of representations along a group homomorphism),
  `Functor.sheafPushforwardContinuous`, `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafAdjunctionCocontinuous`, `Functor.sheafPullbackConstruction`,
  `Functor.Final.hasColimitsOfShape_of_final`, `hasExactColimitsOfShape_of_final` and
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

Let `G` act on `X` and let `H` be a subgroup of `G`. A sheaf on the twisted site of `G` is a
sheaf over `X` with an action of `G`. This module restricts the action to `H`, as a functor
from sheaves on the twisted site of `G` to sheaves on the twisted site of `H`. It constructs
the two adjoints of this functor and shows that restriction to `H` sends injective module
sheaves to injective module sheaves. Consequently, restricting to `H` the `G`-representations
`H^q(X, b^*F)` and `H^q_c(X, b^*F)` of `TwistedRepCohomology` gives the `H`-representations
computed directly on the twisted site of `H`.

This is used to restrict the action of a group on cohomology to a subgroup, as for Harris's
groups `GJ^0 ⊂ GJ` acting on the compactly supported cohomology of the Drinfeld tower (Harris
1997 (A.8), recorded in the Library's coverage note
`notes/henniart/harris-cohomology-coverage.md`). This module does not construct those groups
or spaces.

## Setting

`C : Type u` is a category with `Category.{v} C`, `P` a morphism property of `C`, `X : C`,
`G : Type uG` a group, `ρ : G →* Aut X`, and `H : Subgroup G`. The restricted action is
`ρ.comp H.subtype : H →* Aut X`. Each section below lists its further hypotheses.

## The subgroup inclusion

- `subgroupInclusion ρ H : TwistedOver P (ρ.comp H.subtype) ⥤ TwistedOver P ρ`: the identity
  on objects (both categories have the objects of `P.Over ⊤ X`), and a twisted morphism with
  twist `h ∈ H` goes to the twisted morphism with twist `(h : G)` and the same underlying
  arrow.
- `subgroupInclusion_obj_obj`, `subgroupInclusion_map_twist`, `subgroupInclusion_map_left`
  (simp lemmas, by `rfl`), and the instance that `subgroupInclusion ρ H` is faithful.
- `ι_comp_subgroupInclusion`: `ι P (ρ.comp H.subtype) ⋙ subgroupInclusion ρ H = ι P ρ`
  (by `rfl`).

## Topologies and restriction of sheaves

Assume `[P.RespectsIso]` and let `J` be a Grothendieck topology on `P.Over ⊤ X` with
`[IsTranslationInvariant (ρ := ρ) J]`.

- `translate_comp_subtype`: translation by `h` for the restricted action is translation by
  `(h : G)` (by `rfl`).
- `isTranslationInvariant_comp_subtype` (instance): `J` is invariant for the restricted
  action.
- `subgroupInclusion_isCocontinuous` (instance): the subgroup inclusion is cocontinuous from
  `twistedTopology (ρ.comp H.subtype) J` to `twistedTopology ρ J`. In both twisted topologies
  a sieve covers when its arrows from objects of `P.Over ⊤ X` cover for `J`, and these arrows
  are the same for a sieve and its pullback along the inclusion.
- `subgroupInclusion_isContinuous` (instance): the subgroup inclusion is continuous. A type
  sheaf on the twisted site of `G` restricts along `ι P ρ` to a sheaf over `X`. By
  `ι_comp_subgroupInclusion`, this is the restriction along `ι P (ρ.comp H.subtype)` of its
  pullback to the twisted site of `H`, so `isSheaf_of_isSheaf_comp` applies.

For a category `A`:

- `subgroupRestriction ρ H J A : Sheaf (twistedTopology ρ J) A ⥤ Sheaf (twistedTopology (ρ.comp H.subtype) J) A`
  (abbreviation): Mathlib's `sheafPushforwardContinuous` along the subgroup inclusion,
  that is, precomposition with its opposite.
- `subgroupRestrictionCompRestrictionIso`: restricting to `H` and then to `P.Over ⊤ X` is
  restricting to `P.Over ⊤ X` (`Iso.refl`).
- `subgroupRestriction_faithful` (instance), from the previous isomorphism and faithfulness of
  `restriction ρ J A`.

Given pointwise right Kan extensions along `(subgroupInclusion ρ H).op` of all presheaves on
the twisted category of `H` with values in `A`:

- `subgroupCoinduction ρ H J A` (abbreviation): Mathlib's `sheafPushforwardCocontinuous`, the
  right Kan extension along the subgroup inclusion.
- `subgroupRestrictionAdjunction ρ H J A : subgroupRestriction ρ H J A ⊣ subgroupCoinduction ρ H J A`:
  Mathlib's `sheafAdjunctionCocontinuous`.

## Module sheaves

Let `R : Type w` be a commutative ring.

- `subgroupInclusion_hasPointwiseRightKanExtension_moduleCat`: when the coefficients are
  modules in the universe `max u v uG`, the right Kan extensions above exist (Mathlib's
  instance for limits of the size of the twisted category).
- `subgroupRestriction_additive` and `subgroupRestriction_preservesFiniteLimits` (instances):
  restriction to `H` of module sheaves is additive and preserves finite limits; the latter
  because `sheafToPresheaf` reflects and preserves finite limits and the composite with it is
  precomposition of presheaves.
- `subgroupRestriction_preservesFiniteColimits` (instance, given the right Kan extensions):
  restriction to `H` is a left adjoint.

## Coset translates are final

Assume `[P.RespectsIso]`. Fix `V : TwistedOver P ρ`. An object of
`CostructuredArrow (subgroupInclusion ρ H).op (op V)` is an object `U'` of the twisted
category of `H` with a twisted arrow `V ⟶ U'` of the twisted category of `G`. The right cosets
`H\G` are `Quotient (QuotientGroup.rightRel H)`, whose classes are the sets `Hg`; `q.out` is
the chosen representative of the class `q`.

- `subgroupUntwist g f hf`: for a twisted arrow `f : U ⟶ U'` whose twist `t` satisfies
  `t * g⁻¹ ∈ H`, the arrow `gU ⟶ U'` of the twisted category of `H` with twist `t * g⁻¹` and
  the same underlying arrow as `f`.
- `relabel_comp_subgroupInclusion_map_subgroupUntwist`: `f` is the relabelling arrow
  `U ⟶ gU` followed by the inclusion of `subgroupUntwist g f hf`.
- `cosetTranslateArrows ρ H V : Discrete (Quotient (QuotientGroup.rightRel H)) ⥤ CostructuredArrow (subgroupInclusion ρ H).op (op V)`:
  the class `q` goes to the translate `q.out V` with the relabelling arrow
  `relabel ρ q.out V.obj`.
- `coset_eq_of_hom_cosetTranslateArrows`: a morphism from a costructured arrow `d` to the
  translate indexed by `j` forces `j` to be the coset of the twist of the arrow of `d`. The
  twist of the arrow of `d` equals `h * j.out` with `h ∈ H`, the twist of the factor.
- `cosetTranslateArrows_hom_subsingleton` (instance): such morphisms are unique, because the
  relabelling arrow is an epimorphism and the subgroup inclusion is faithful.
- `mul_inv_out_mem`: `g * (Quotient.out ⟦g⟧)⁻¹ ∈ H`.
- `toCosetTranslate ρ H V d`: every costructured arrow `d` factors through the translate by
  the representative of the coset of its twist, via `subgroupUntwist`.
- `cosetTranslateArrows_final` (instance): `cosetTranslateArrows ρ H V` is final. For each `d`
  the category of factorizations through coset translates is nonempty (`toCosetTranslate`)
  and any two of its objects are joined by a morphism (both have the same index, and
  morphisms are unique).

For `H = ⊥` this recovers the shape of `translateArrows` of `TwistedLeftInduction`, with
cosets in place of group elements; the module does not prove this.

## Exactness of left Kan extension

- `lanEvaluationIsoColimitOf F V`: for any functor `F : C ⥤ D` and categories `E` in which the
  colimits over all `CostructuredArrow F V` exist, the value at `V` of the left Kan extension
  functor `F.lan` is the colimit over the costructured arrows of `V`. This is Mathlib's
  `lanEvaluationIsoColim` without its smallness assumptions, with the same proof. (The
  published `lanEvaluationIsoColimit` of `TwistedLeftInduction` is the special case
  `F = (ι P ρ).op` with module coefficients.)

Let `R : Type w` be a commutative ring and assume
`[HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat R)]`
(coproducts of modules indexed by `H\G`).

- `subgroupCostructuredArrow_hasColimitsOfShape` (instance): colimits of modules over the
  costructured arrows of every object exist, by finality of `cosetTranslateArrows`.
- `subgroupInclusion_hasPointwiseLeftKanExtension` and `subgroupInclusion_hasLeftKanExtension`
  (instances): every module presheaf on the twisted category of `H` has a pointwise left Kan
  extension along the subgroup inclusion.

With also `[HasExactColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H))) (ModuleCat R)]`:

- `subgroupCostructuredArrow_hasExactColimitsOfShape` (instance): these colimits are exact,
  by Mathlib's `hasExactColimitsOfShape_of_final`.
- `subgroupLan_preservesFiniteLimits` (instance): `(subgroupInclusion ρ H).op.lan` preserves
  finite limits, checked objectwise through `lanEvaluationIsoColimitOf`.

The colimit over the costructured arrows of `V` is, mathematically, the direct sum over `H\G`
of the values on the coset translates. The module uses only finality and does not construct
this isomorphism. The two coproduct hypotheses are not discharged here.

## Induction and injectivity

With `R`, the coproduct hypothesis, a translation-invariant `J`, and
`[HasSheafify (twistedTopology ρ J) (ModuleCat R)]`:

- `subgroupInduction ρ H R J`: Mathlib's `Functor.sheafPullbackConstruction.sheafPullback`
  along the subgroup inclusion, that is, left Kan extension along its opposite followed by
  sheafification for the twisted topology of `G`.
- `subgroupInductionAdjunction ρ H R J : subgroupInduction ρ H R J ⊣ subgroupRestriction ρ H J (ModuleCat R)`:
  Mathlib's `sheafAdjunctionContinuous`.

With also exact coproducts indexed by `H\G`:

- `subgroupInduction_preservesFiniteLimits` (instance): induction is the composite of
  `sheafToPresheaf`, `(subgroupInclusion ρ H).op.lan` and sheafification, each of which
  preserves finite limits.
- `subgroupRestriction_preservesInjectiveObjects` (instance): restriction to `H` sends
  injective module sheaves on the twisted site of `G` to injective module sheaves on the
  twisted site of `H`, by Mathlib's
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`.

## Global sections

Assume `[P.RespectsIso]`, `[P.ContainsIdentities]`, a translation-invariant `J` and a
commutative ring `R : Type w`.

- `subgroupRestrictionGlobalSectionsIso ρ H J R`:
  `sheafGlobalSectionsRep J R (ρ := ρ) ⋙ Rep.resFunctor H.subtype ≅ subgroupRestriction ρ H J (ModuleCat R) ⋙ sheafGlobalSectionsRep J R (ρ := ρ.comp H.subtype)`,
  with identity components: both sides are the sections at the base object, on which `h ∈ H`
  acts by restriction along the endomorphism `h⁻¹` of the base object.

Assume also `HasSheafify` and `EnoughInjectives` for module sheaves on the twisted sites of
`G` and of `H`, and the pointwise right Kan extensions along `(subgroupInclusion ρ H).op`.

- `subgroupRestrictionGlobalComparison ρ H J R q`: from
  `sheafGlobalRepDerived J R (ρ := ρ) q ⋙ Rep.resFunctor H.subtype` to
  `subgroupRestriction ρ H J (ModuleCat R) ⋙ sheafGlobalRepDerived J R (ρ := ρ.comp H.subtype) q`,
  the `baseChangeNatTrans` of `(subgroupRestrictionGlobalSectionsIso ρ H J R).hom` along the
  exact functors restriction to `H` and `Rep.resFunctor H.subtype`.

With also coproducts of modules indexed by `H\G` that exist and are exact:

- `isIso_subgroupRestrictionGlobalComparison_app`: each component is an isomorphism. The
  proof applies `isIso_baseChangeNatTrans_app_of_acyclic` to the injective resolution
  `injectiveResolution F` and to its restriction to `H` (a resolution by
  `quasiIso_mapResolutionAugmentation`), with `ψ = 𝟙`. The comparison of complexes is the
  componentwise application of the isomorphism `subgroupRestrictionGlobalSectionsIso`. The
  terms of the resolution are injective, and so are their restrictions to `H`
  (`subgroupRestriction_preservesInjectiveObjects`), so both are acyclic.
- `subgroupRestrictionGlobalCohomologyIso ρ H J R q`: the resulting natural isomorphism
  `sheafGlobalRepDerived J R (ρ := ρ) q ⋙ Rep.resFunctor H.subtype ≅ subgroupRestriction ρ H J (ModuleCat R) ⋙ sheafGlobalRepDerived J R (ρ := ρ.comp H.subtype) q`.

## Compactly supported global sections

Let `I : Type uI` carry a `G`-action, a topology and `[ContinuousConstSMul G I]`, and let
`Φ : I → J.Point` be a family of points.

- `subgroup_continuousConstSMul` (instance): `H` acts on `I` by homeomorphisms (Mathlib's
  `IsScalarTower.continuousConstSMul`).
- `PointEquivariance.toSubgroup H E`: a compatibility `E : PointEquivariance ρ Φ` restricts to
  a compatibility for the restricted action, with the same fibre isomorphisms (translation by
  `h` for the restricted action is translation by `(h : G)`).

Assume also `[LocallySmall.{w} (P.Over ⊤ X)]`.

- `subgroupRestrictionCompactSectionsIso ρ H J R E`:
  `sheafCompactSectionsRep J R E ⋙ Rep.resFunctor H.subtype ≅ subgroupRestriction ρ H J (ModuleCat R) ⋙ sheafCompactSectionsRep J R (E.toSubgroup H)`,
  with identity components.

With `[HasSheafify J (ModuleCat R)]` and the hypotheses of the global case:

- `subgroupRestrictionCompactComparison ρ H J R E q`: the `baseChangeNatTrans` of the
  previous isomorphism, from `sheafCompactRepDerived J R E q ⋙ Rep.resFunctor H.subtype` to
  `subgroupRestriction ρ H J (ModuleCat R) ⋙ sheafCompactRepDerived J R (E.toSubgroup H) q`.
- `isIso_subgroupRestrictionCompactComparison_app` (with exact coproducts indexed by `H\G`):
  its components are isomorphisms, by the same argument as in the global case.
- `subgroupRestrictionCompactCohomologyIso ρ H J R E q`: the resulting natural isomorphism.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
Printed page numbers equal PDF page numbers.

- §1.1, printed pp.2–3: "The category of analytic spaces with operators `Anop` is the category
  of pairs `X(G)` where `G` is a topological group and `X` is a `G`-space. A morphism between
  such spaces `ϕ : X′(G′) → X(G)` is a pair consisting of a continuous homomorphism of
  topological groups `ν_ϕ : G′ → G` and a morphism of analytic spaces `ϕ : Y → X` compatible
  with the homomorphism `ν_ϕ`. [...] The category `Anop` is a fibred category over the
  category of topological groups."
- Construction 1.1.2, printed p.2: for an open subgroup `H` of `G` and an `H`-space `X`, the
  `G`-space `X_{G/H}`, a disjoint union of copies of `X` indexed by `G/H`, with its universal
  property.
- Example 1.1.3, printed p.3: for a `G`-space `X`, the morphism `b : X → X(G)` with
  `X = X({1})`.
- §1.2, printed p.3: any morphism `ϕ : X′(G′) → X(G)` gives morphisms of the quasi-étale and
  étale sites and topoi. "For a quasi-étale (resp. étale) sheaf `F′` on `X′(G′)`, the value of
  `ϕ_*F′` on `U(G)` over `X(G)` is `F′((X′ ×_X U)(G′))`", and `ϕ^*F` is the sheaf associated
  with the presheaf `U′(G′) ↦ lim→ F(V(G))`, the limit over the dual of the category
  `C(U′(G′)/X(G))` of morphisms `U′(G′) → V(G)` over `X(G)` with `V` quasi-étale (resp.
  étale) over `X`.
- §1.4, printed p.7: "Consider first the case when the group `G` is discrete. In this case a
  quasi-étale (resp. étale) `G`-sheaf `F` is a quasi-étale (resp. étale) sheaf on `X` endowed
  with an action of `G` on `F`, compatible with the action of `G` on `X`, i.e., endowed with a
  system of isomorphisms `τ(g) : F ⥲ g^*F`, `g ∈ G`, such that `τ(gh) = h^*(τ(g)) ∘ τ(h)`."
  For a subgroup `H` of `G` and `U(H) → X(G)`, the same page defines the action of `H` on
  `F(U)`.
- Theorem 1.4.2, printed p.8: "The inverse image functor for the morphism `b : X → X(G)`
  induces an equivalence of categories `X(G)~_qét ⥲ T_G(X_qét)` (resp. `X(G)~_ét ⥲ T_G(X_ét)`)."

## Provenance and correspondence

Derived. As explained in the Provenance section of `TwistedOver.md`, sheaves on the twisted
site of `G` model Berkovich's `G`-sheaves for discrete `G` (§1.4, p.7): sheaves on `X` with
the bijections `F(U) ≅ F(gU)` and their cocycle law. Correspondence:

- `subgroupRestriction` keeps the bijections for `h ∈ H` and forgets the others; the
  underlying sheaf over `X` is unchanged (`subgroupRestrictionCompRestrictionIso`). Berkovich
  has no separate name for this functor. In his framework of §1.1–1.2, it is expected to
  correspond to the inverse image `ϕ^*` along the morphism `ϕ = (H ↪ G, id_X) : X(H) → X(G)`
  of `Anop`. Indeed `ϕ ∘ b_H = b_G` for the morphisms `b : X → X(H)` and `b : X → X(G)` of
  Example 1.1.3, so, through the equivalences of Theorem 1.4.2, `ϕ^*` does not change the
  underlying sheaf on `X` either. Neither this correspondence nor the agreement of the
  `H`-actions is formalized.
- `subgroupCoinduction` (the right Kan extension along the subgroup inclusion) is the right
  adjoint of restriction, so it corresponds to Berkovich's `ϕ_*` in the same expected sense.
  It is not compared with his formula `ϕ_*F′(U(G)) = F′((X ×_X U)(H))`.
- `subgroupInduction` (the left adjoint of restriction) is our construction; Berkovich's text
  does not define it. Before sheafification its values are colimits over the translates by
  representatives of `H\G`, an analogue for sheaves of the disjoint union over cosets in
  Construction 1.1.2. The module does not relate it to `X_{G/H}`.

Differences from Berkovich: `H` is any subgroup, not necessarily open; groups are discrete;
the coproduct hypotheses indexed by `H\G` are assumptions. The results on derived functors
(`subgroupRestrictionGlobalCohomologyIso`, `subgroupRestrictionCompactCohomologyIso`) are not
stated in Berkovich's text; they are the restriction-to-a-subgroup compatibility of the
actions of `TwistedRepCohomology`. Not formalized here: the analytic specializations (étale
and quasi-étale `G`-sheaves of `AnalyticGSheaves` restricted to `H`, which needs the local
action systems restricted to `H`), smoothness, compact induction from `H` to `G`, and Harris's
groups and spaces.
