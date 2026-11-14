# Restriction of étale and quasi-étale `G`-sheaves to a subgroup

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedSubgroupRestriction` (imported; accepted candidate
  `053e4a98`): the subgroup inclusion
  `subgroupInclusion ρ H : TwistedOver P (ρ.comp H.subtype) ⥤ TwistedOver P ρ` (identity on
  objects, a twist `h ∈ H` goes to the twist `(h : G)`), restriction of sheaves
  `subgroupRestriction ρ H J A` (precomposition with its opposite), and the natural
  isomorphisms `subgroupRestrictionGlobalCohomologyIso ρ H J R q` and
  `subgroupRestrictionCompactCohomologyIso ρ H J R E q`. These identify `Rep.resFunctor H.subtype`
  applied to the `G`-representations `sheafGlobalRepDerived J R q` and
  `sheafCompactRepDerived J R E q` with the corresponding `H`-representations after
  restriction to `H`. They assume pointwise right Kan extensions along the subgroup inclusion,
  and coproducts of modules indexed by the right cosets `H\G` that exist and are exact.
- `Langlands.Sheaf.Equivariant.AnalyticGSheaves` (through the imports): the twisted étale and
  quasi-étale topologies `twistedEtaleTopology ρ` and `twistedQuasiEtaleTopology ρ`, the open
  subgroup `liftOpenSubgroup l` and the local action `liftAction l` of a lift `l` (the element
  `h` acts by the twisted endomorphism with twist `h⁻¹` whose arrow is the action of `h⁻¹`),
  the local action systems `liftSystem P ρ Adm`, `distinguishedLiftSystem ρ` (`Adm` = the
  structure arrow is distinguished étale) and `compactLiftSystem ρ` (`Adm` = the source is
  compact), and the categories `EtaleGSheaf ρ A` (locally discrete sheaves for
  `distinguishedLiftSystem ρ`) and `QuasiEtaleGSheaf ρ A` (discrete sheaves for
  `compactLiftSystem ρ`).
- `Langlands.Geometry.Analytic.LocalActionLifts` (Worker 21, through the imports):
  `ActionLift ρ f`, a lift of the action `ρ` to `f : U ⟶ X`, consisting of an open subgroup
  `l.subgroup` of `G`, a continuous action `l.action` of it on `U`, and the equivariance of
  `f`; `IsDistinguishedEtale` and `IsCompactSpace`.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleRefinements` (imported):
  `IsDistinguishedEtale.comp_iso` (a distinguished étale arrow followed by an isomorphism is
  distinguished étale) and, for `[IsTopologicalGroup G]`, the translate
  `ActionLift.translate l t : ActionLift ρ (f ≫ (ρ t).hom)` of a lift, with subgroup
  `t S t⁻¹` (`S = l.subgroup`) on which `y` acts as `t⁻¹ y t` acts for `l`, together with
  `ActionLift.translateHom`, `ActionLift.mem_translateSubgroup` and
  `ActionLift.coe_translateHom`.
- `Langlands.Sheaf.Equivariant.LocalAction` and `Langlands.Sheaf.Equivariant.LocalActionDiscretePart`
  (through the imports): `LocalActionSystem.IsDiscrete` (every admissible local action has open
  stabilizers on all sections), `LocalActionSystem.IsLocallyDiscrete` (for every section `s`,
  the sieve `discreteSieve F s` of arrows factoring through an object with an admissible local
  action for which the restriction of `s` is discrete is a covering sieve), the full
  subcategories cut out by these properties (`smoothSheafProperty`, `discreteSheafProperty`)
  and their inclusions `smoothSheafInclusion`, `discreteSheafInclusion`.
- `Langlands.Sheaf.Equivariant.TwistedOver` (through the imports): the inclusion `ι P ρ`, the
  translations `translate P ρ t`, the relabelling arrows
  `relabel ρ t V : (ι P ρ).obj V ⟶ (ι P ρ).obj ((translate P ρ t).obj V)` (twist `t`) and
  `relabelInv ρ t V` (twist `t⁻¹`), both with identity underlying arrow, `untwist` with
  `relabel_comp_ι_map_untwist`, `exists_ι_map_of_twist_eq_one`, `comp_twist` and `hom_ext`.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleRepCohomology` and
  `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleRepCohomology` (imported): the
  representations `etaleRestrictionCohomologyRep ρ R q`,
  `etaleRestrictionCompactCohomologyRep L ρ h R q`, `quasiEtaleRestrictionCohomologyRep ρ R q`
  and `quasiEtaleRestrictionCompactCohomologyRep L ρ h R q` of `G` on `H^q(X, b^*F)` and
  `H^q_c(X, b^*F)`. Through the imports: `b^*` (`etaleGSheafRestriction`,
  `quasiEtaleGSheafRestriction`), and the lemmas supplying the instances used below
  (`twistedEtale_hasSheafify`, `twistedEtale_enoughInjectives`,
  `twistedEtale_essentiallySmall_points`, `twistedEtale_locallySmall_points`, their
  quasi-étale analogues, `discrete_hasColimitsOfShape`, `discrete_hasExactColimitsOfShape`,
  `EtaleSite.pointEquivariance`, `QuasiEtaleSite.pointEquivariance`).
- Mathlib: `MonoidHom.subgroupComap`, `Subgroup.map`, `Subgroup.comap`,
  `IsOpen.isOpenMap_subtype_val`, `ObjectProperty.lift`, `hasLimitsOfShape_of_essentiallySmall`,
  `Functor.isoWhiskerLeft` and `Rep.resFunctor`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Let a topological group `G` act on a `K`-analytic space `X`, and let `H` be a subgroup of `G`
with the subspace topology. `TwistedSubgroupRestriction` restricts sheaves on the twisted site
of `G` to sheaves on the twisted site of `H`. This module shows that this restriction preserves
Berkovich's `G`-sheaf conditions:

- étale `G`-sheaves restrict to étale `H`-sheaves for every subgroup `H` (when `G` is a
  topological group);
- quasi-étale `G`-sheaves restrict to quasi-étale `H`-sheaves when `H` is open.

Restriction does not change the underlying sheaf on `X`, so it commutes with `b^*`. The
representations of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)`, restricted to `H`, are the
representations of `H` defined from the restricted sheaf.

The intended use is restriction of the action of Harris's group `GJ` on the cohomology of the
Drinfeld tower to its open subgroup `GJ^0` (Harris 1997 (A.8), recorded in the Library's
coverage note `notes/henniart/harris-cohomology-coverage.md`). This module does not construct
those groups or spaces.

## Setting

`K : Type u` is a complete ultrametric normed field, `X : LocalizedCategory.{u, v, v} (K := K)`,
`G : Type z` a group with a topology, `ρ : G →* Aut X` and `H : Subgroup G`. The restricted
action is `ρ.comp H.subtype : H →* Aut X`, and `H` has Mathlib's subspace topology. `A` is a
concrete category. Each section lists its further hypotheses.

## Subgroups

- `continuous_subtype_subgroupComap H S`: for a subgroup `S` of `G`, the homomorphism
  `H.subtype.subgroupComap S : S.comap H.subtype →* S` (an element of `H ∩ S` seen in `S`) is
  continuous.
- `mem_of_mem_map_subtype` and `mk_mem_of_mem_map_subtype`: for a subgroup `S` of `H`, an
  element `g` of its image `S.map H.subtype` in `G` lies in `H`, and `⟨g, _⟩ ∈ S`.
- `mapSubtypeHom H S : S.map H.subtype →* S`, the identity on underlying elements of `G`, and
  `continuous_mapSubtypeHom H S`.
- `isOpen_map_subtype hH hS`: if `H` is open in `G` and `S` is open in `H`, then the image of
  `S` in `G` is open. Proof: Mathlib's `IsOpen.isOpenMap_subtype_val`.

## Lifts

Let `f : U ⟶ X` be an arrow of `LocalizedCategory`.

- `liftToSubgroup H l : ActionLift (ρ.comp H.subtype) f` for `l : ActionLift ρ f`: the
  subgroup `l.subgroup.comap H.subtype` of `H` (open, as the preimage of an open set under the
  inclusion `H → G`), acting through `H.subtype.subgroupComap l.subgroup` and `l.action`.
  Equivariance is that of `l`.
- `liftOfSubgroup hH l : ActionLift ρ f` for an open subgroup `H` and
  `l : ActionLift (ρ.comp H.subtype) f`: the subgroup `l.subgroup.map H.subtype` of `G` (open by
  `isOpen_map_subtype`), acting through `mapSubtypeHom` and `l.action`.

Assume `[IsTopologicalGroup G]`.

- `conj_mem_of_mem_liftToSubgroup_translate H l t hh`: if `h ∈ H` lies in the subgroup of
  `liftToSubgroup H (l.translate t)`, then `t⁻¹ * h * t ∈ l.subgroup`
  (`ActionLift.mem_translateSubgroup`).

## Lift systems

Let `P` be a morphism property of `LocalizedCategory` and `Adm : P.Over ⊤ X → Prop`. Let `F`
be a presheaf on `TwistedOver P ρ` with values in `A`; its restriction to `H` is
`(subgroupInclusion ρ H).op ⋙ F`.

- `subgroupInclusion_map_liftAction hH l h`: for an open `H`, a lift `l` for `H` on an object
  `U` and `h` in its subgroup, the subgroup inclusion sends the local action of `l` at `h` to
  the local action of `liftOfSubgroup hH l` at `(h : G)`. Both have twist `(h : G)⁻¹` and arrow
  the action of `h⁻¹` (`hom_ext rfl rfl`).
- `isDiscrete_subgroupRestriction hH Adm hF`: for an open `H`, if
  `(liftSystem P ρ Adm).IsDiscrete F`, then
  `(liftSystem P (ρ.comp H.subtype) Adm).IsDiscrete ((subgroupInclusion ρ H).op ⋙ F)`. Proof:
  an admissible action for `H` on `U` comes from a lift `l` for `H` and an open subgroup `S` of
  its subgroup. The image `S'` of `S` in `G` is open and contained in the subgroup of
  `liftOfSubgroup hH l`, so the corresponding action for `G` is admissible. By `hF` a section
  `s` is fixed by an open subgroup `N ≤ S'` for it. Then `N.comap H.subtype` is open in `H`,
  contained in `S`, and fixes `s` for the action of `H` by the previous theorem.

Assume now `[P.RespectsIso]` and `[IsTopologicalGroup G]`.

- `subgroupInclusion_map_liftAction_translate H t l h`: for an object `V` of `P.Over ⊤ X`, a
  lift `l` for `G` on `(ι P ρ).obj V` and `h` in the subgroup of
  `liftToSubgroup H (l.translate t)`, a lift on the translate `tV`, the subgroup inclusion sends
  the local action of the latter at `h` to
  `relabelInv ρ t V ≫ a ≫ relabel ρ t V`, where `a` is the local action of `l` at
  `t⁻¹ * h * t`. Proof by `hom_ext`: the twists agree because
  `h⁻¹ = (t * (t⁻¹ * h * t)⁻¹) * t⁻¹`. The arrows agree because the translated lift acts at
  `h⁻¹` as `l` acts at `t⁻¹ * h⁻¹ * t = (t⁻¹ * h * t)⁻¹`, and the relabelling arrows are
  identities.
- `relabelInv_comp_relabel t V`: `relabelInv ρ t V ≫ relabel ρ t V = 𝟙 _`.
- `map_comp_op_apply` and `map_comp_comp_op_apply`: for a functor `F : Cᵒᵖ ⥤ A`, the value of
  `F.map (a ≫ b).op` (resp. `F.map (a ≫ b ≫ c).op`) at an element is obtained by applying the
  maps one at a time. These helpers avoid rewriting inside dependent types.
- `isLocallyDiscrete_subgroupRestriction H Adm hAdm J hF`: let `H` be any subgroup, `Adm`
  invariant under the translations (`hAdm`), and `J` a translation-invariant topology on
  `P.Over ⊤ X`. If `(liftSystem P ρ Adm).IsLocallyDiscrete (twistedTopology ρ J) F`, then
  `(liftSystem P (ρ.comp H.subtype) Adm).IsLocallyDiscrete (twistedTopology (ρ.comp H.subtype) J)`
  holds for `(subgroupInclusion ρ H).op ⋙ F`.

  Proof. A sieve on `U` covers for a twisted topology when its arrows from objects of
  `P.Over ⊤ X` with trivial twist cover for `J`. So it suffices to show that the arrows
  `φ : W ⟶ U.obj` of `P.Over ⊤ X` whose images under `ι P ρ` lie in the discrete sieve of a
  section `s` for `G` also lie in the discrete sieve of `s` for `H`. Such an arrow factors as
  `k ≫ f` through an object `V` with an admissible action for `G`: a lift `l` on `V`, an open
  `S ≤ l.subgroup`, and an open `N ≤ S` fixing `F.map f.op s`. The twist `t` of `f` need not
  lie in `H`. Write `f = relabel ρ t V ≫ (ι P ρ).map f₀` with `f₀ : tV ⟶ U.obj`
  (`relabel_comp_ι_map_untwist`). Then `k ≫ relabel ρ t V` has trivial twist, so it is
  `(ι P ρ).map k₀` (`exists_ι_map_of_twist_eq_one`), and `φ = k₀ ≫ f₀`. On `tV` take the
  admissible action for `H` given by `liftToSubgroup H (l.translate t)` on its whole subgroup;
  `Adm (tV)` holds by `hAdm`. The open subgroup `{h ∈ H | t⁻¹ * h * t ∈ N}` of `H` fixes
  `F.map f₀.op s`: by `subgroupInclusion_map_liftAction_translate`, the action of `h` on it
  is the composite of `F.map (relabel ρ t V).op`, the action of `t⁻¹ * h * t` (which fixes
  `F.map f.op s`), and `F.map (relabelInv ρ t V).op`, and
  `F.map (relabelInv ρ t V).op ∘ F.map (relabel ρ t V).op = id` by
  `relabelInv_comp_relabel`.

## `G`-sheaves

- `etaleGSheafSubgroupRestriction ρ H A`, for `[IsTopologicalGroup G]` and any `H`:
  `EtaleGSheaf ρ A ⥤ EtaleGSheaf (ρ.comp H.subtype) A`, the lift through the full subcategory
  of `smoothSheafInclusion ⋙ subgroupRestriction ρ H (etaleTopology X) A`. The property holds by
  `isLocallyDiscrete_subgroupRestriction` with `Adm V = IsDistinguishedEtale V.hom`. This `Adm`
  is translation-invariant: the translate by `t` has structure arrow `V.hom ≫ (ρ t).hom`, which
  is distinguished étale by `IsDistinguishedEtale.comp_iso`.
- `etaleGSheafSubgroupRestrictionCompInclusionIso ρ H A`: the restriction followed by the
  inclusion into sheaves is the inclusion followed by `subgroupRestriction` (`Iso.refl`).
- `quasiEtaleGSheafSubgroupRestriction ρ A hH`, for an open `H`:
  `QuasiEtaleGSheaf ρ A ⥤ QuasiEtaleGSheaf (ρ.comp H.subtype) A`, the lift of
  `discreteSheafInclusion ⋙ subgroupRestriction ρ H (quasiEtaleTopology X) A`, by
  `isDiscrete_subgroupRestriction`.
- `quasiEtaleGSheafSubgroupRestrictionCompInclusionIso ρ A hH`: the analogous `Iso.refl`.

Let `R : Type (max u (v + 1) uL)` be a commutative ring.

- `etaleGSheafSubgroupRestrictionCompRestrictionIso ρ H R`:
  `etaleGSheafSubgroupRestriction ρ H (ModuleCat R) ⋙ etaleGSheafRestriction (ρ.comp H.subtype) R ≅ etaleGSheafRestriction ρ R`
  (`Iso.refl`): restricting to `H` and then applying `b^*` is `b^*`.
- `quasiEtaleGSheafSubgroupRestrictionCompRestrictionIso ρ R hH`: the quasi-étale analogue.

## Right Kan extensions

Assume `[Small.{max u (v + 1) uL} G]`; `G` need not have a topology here.

- `etale_subgroupInclusion_hasPointwiseRightKanExtension ρ H R F`: every presheaf of
  `R`-modules on the twisted étale category of `H` has a pointwise right Kan extension along
  `(subgroupInclusion ρ H).op`. The twisted étale category of `H` is essentially small and that
  of `G` is locally small, so the categories of structured arrows are essentially small, and
  `ModuleCat R` has limits over them (`hasLimitsOfShape_of_essentiallySmall`).
- `quasiEtale_subgroupInclusion_hasPointwiseRightKanExtension ρ H R F`: the quasi-étale
  analogue.

## Cohomology

Assume `[Small.{max u (v + 1) uL} G]`. The coproducts of modules indexed by the right cosets
`H\G` required by `TwistedSubgroupRestriction` exist and are exact because `H\G`, a quotient
of `G`, is small (`discrete_hasColimitsOfShape`, `discrete_hasExactColimitsOfShape`).

- `etaleSubgroupRestrictionCohomologyIso ρ H R q`, for `[IsTopologicalGroup G]`:
  `etaleRestrictionCohomologyRep ρ R q ⋙ Rep.resFunctor H.subtype ≅ etaleGSheafSubgroupRestriction ρ H (ModuleCat R) ⋙ etaleRestrictionCohomologyRep (ρ.comp H.subtype) R q`.
  It is `subgroupRestrictionGlobalCohomologyIso ρ H (etaleTopology X) R q`, whiskered on the
  left by the inclusion of étale `G`-sheaves into sheaves.
- `etaleSubgroupRestrictionCompactCohomologyIso ρ H R L h q`, for `L : Type uL` a normed field
  with `[NormedAlgebra K L]` and `h : ∀ x, EtaleSite.PointAxioms L x`:
  `etaleRestrictionCompactCohomologyRep L ρ h R q ⋙ Rep.resFunctor H.subtype ≅ etaleGSheafSubgroupRestriction ρ H (ModuleCat R) ⋙ etaleRestrictionCompactCohomologyRep L (ρ.comp H.subtype) h R q`,
  the whiskering of `subgroupRestrictionCompactCohomologyIso` for the point compatibility
  `EtaleSite.pointEquivariance L ρ h`. Supports are taken in the `L`-valued points.
- `quasiEtaleSubgroupRestrictionCohomologyIso ρ hH R q` and
  `quasiEtaleSubgroupRestrictionCompactCohomologyIso ρ hH R L h q`, for an open `H` (with
  `h : ∀ x, QuasiEtaleSite.PointAxioms L x`): the quasi-étale analogues, with
  `quasiEtaleGSheafSubgroupRestriction ρ (ModuleCat R) hH`.

In each case the underlying modules are `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`) on both
sides, by `etaleGSheafSubgroupRestrictionCompRestrictionIso` and its quasi-étale analogue.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`). Printed page
numbers equal PDF page numbers.

- §1.1, printed pp.2–3: `Anop` is the category of pairs `X(G)` with `G` a topological group
  and `X` a `G`-space; a morphism `ϕ : X′(G′) → X(G)` is a continuous homomorphism
  `ν_ϕ : G′ → G` with a morphism of analytic spaces compatible with `ν_ϕ`. §1.2, printed p.3:
  such a morphism gives an inverse image functor `ϕ^*` on quasi-étale and étale sheaves.
- §1.4, printed p.7, for discrete `G`: "Given a `G`-sheaf `F`, then for any quasi-étale (resp.
  étale) morphism `U(H) → X(G)`, where `H` is a subgroup of `G`, the set `F(U)` is endowed with
  a canonical action of the group `H`."
- §1.4, printed p.7, for a topological group `G`: by the Key Lemma 7.2 of [Ber3], for a
  quasi-étale `U → X` with compact `U` "the action of `G` on `X` extends in a canonical way to
  a continuous action of some open subgroup `G_U ⊂ G` on `U`"; the same holds for distinguished
  étale morphisms, and two such extensions coincide on some open subgroup.
- Definition 1.4.1, printed pp.7–8: "A quasi-étale (resp. étale) `G`-sheaf on `X` is a
  quasi-étale (resp. étale) `G^d`-sheaf `F` such that for any quasi-étale morphism `U → X` with
  compact `U` the action of `G_U` on `F(U)` is discrete."
- Printed p.8, after the definition: "an étale `G^d`-sheaf `F` is a `G`-sheaf if and only if
  for any étale morphism `U → X` and any element `f ∈ F(U)` each point of `U` has a
  distinguished open neighborhood `Ū` such that the stabilizer of `f|Ū` is open in `G_Ū`."
- Theorem 1.4.2, printed p.8: `b^*` induces equivalences `X(G)~_qét ⥲ T_G(X_qét)` and
  `X(G)~_ét ⥲ T_G(X_ét)`.

## Provenance and correspondence

Derived. The étale (resp. quasi-étale) `G`-sheaves of `AnalyticGSheaves` model Berkovich's
`T_G(X_ét)` (resp. `T_G(X_qét)`): the étale case uses the criterion of p.8, the quasi-étale case
Definition 1.4.1, with lifts `ActionLift` in place of the canonical extensions `G_U`.

Berkovich does not state a restriction result for `G`-sheaves of a topological group. The p.7
quotation concerns discrete `G`, where the generic `TwistedSubgroupRestriction` applies. The
results here are ours. In Berkovich's framework, restriction to `H` is expected to be the
inverse image `ϕ^*` along `ϕ = (H ↪ G, id_X) : X(H) → X(G)`, a morphism of `Anop` for the
subspace topology on `H`, composed with the equivalences of Theorem 1.4.2. This
correspondence is not formalized.

Why the two cases differ. Berkovich's extensions `G_U` are canonical: by the Key Lemma any two
agree on an open subgroup. So the canonical action of `H ∩ G_U` on `U` is the restriction of
that of `G_U`, and both of his conditions pass to any subgroup `H`. In the Library, the
`H`-sheaf conditions quantify over arbitrary lifts `ActionLift (ρ.comp H.subtype)`, and no
uniqueness of lifts is available. Hence:

- the quasi-étale condition (`IsDiscrete`) requires discreteness for every lift for `H`. Every
  such lift is a lift for `G` when `H` is open (`liftOfSubgroup`), but this is not known for
  other `H`. Only open `H` are treated;
- the étale condition (`IsLocallyDiscrete`) requires only some lifts on a covering. The
  restrictions to `H` of translated lifts for `G` suffice (`liftToSubgroup`,
  `ActionLift.translate`), so every `H` is treated. The translation is needed because the
  covering arrows on the twisted site of `G` can have twists outside `H`, and
  `ActionLift.translate` needs `[IsTopologicalGroup G]`.

The compatibilities with `b^*` and with `Rep.resFunctor` are those of
`TwistedSubgroupRestriction`, restricted to `G`-sheaves.

Not formalized here: the identification with Berkovich's `ϕ^*`; restriction of quasi-étale
`G`-sheaves to subgroups that are not open; the right and left adjoints of the restriction
functors on `G`-sheaves (the adjoints of `TwistedSubgroupRestriction` are for all sheaves on
the twisted sites); the compatibility of restriction with Berkovich's `H^q(X{G}, F)` and
`H^q_c(X{G}, F)`; smoothness of the restricted actions; compact induction from `H` to `G`;
and Harris's groups and spaces.
