# Essential surjectivity of induction on equivariant quasi-étale sites

This module proves the essential surjectivity part of Berkovich's Example
1.2.1(i), `InducedSpace.QuasiEtaleSiteEquivalenceStatement`, assuming two
Library statements and an isomorphism condition as hypotheses (see below).
Berkovich states the example without proof; the argument here is the evident
one: a quasi-étale `G`-space `π : W → X_{G/H}` is induced from the `H`-space
`π⁻¹(X)` over `X`. The `H`-space `π⁻¹(X)` and its morphism to `X` are
constructed in module `InducedSiteBase`. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

Throughout, `G : Type z` is a group, `H` a subgroup, `X` an `H`-object and `Y`
a `G`-object of `LocalizedCategory`, and `π : Y ⟶ inducedAction H X` a
morphism of `G`-objects. `baseCoset H` is the coset `H` and `baseRep H` its
chosen representative `r ∈ H`.

## Declarations

### Quasi-étaleness of the base morphism

- `map_mem_copyDomain_of_mem_preimageDomain π c`: `π` maps the domain
  `preimageDomain π c` into the domain `copyDomain H X c` of the copy `c`, in
  the form required by `domainRestrict`.
- `baseHomV_eq_domainRestrict π`: the morphism `baseHomV π : π⁻¹(X_H) → X` of
  `InducedSiteBase` is the restriction
  `domainRestrict (preimageDomain π H) (copyDomain H X H) π.hom` of `π` to these
  open domains, followed by
  `domainι (copyDomain H X H) ≫ foldHom H X ≫ X.ρ r`.
- `quasiEtale_baseHomV π hP hR hπ`: if the underlying space of `Y` is
  Hausdorff and `π.hom` is quasi-étale, then `baseHomV π` is quasi-étale. Here
  `hP : OpenPartitionCoproductStatement.{u, v, z}` and
  `hR : QuasiEtaleOpenRestrictionStatement.{u, max z v}` are hypotheses: the
  Library statements that an analytic space partitioned into open subsets is
  their coproduct, and that a quasi-étale morphism with Hausdorff source
  restricts to a quasi-étale morphism over an open subset of the target
  (Berkovich 1994, Lemma 3.1(i)). Neither statement is proved here.

### Essential surjectivity

- `subgroupContinuousHom H : H →ₜ* G`: the inclusion of `H` as a continuous
  homomorphism, with the subspace topology on `H`.

From now on `G` is a topological group, `H` is open (`hH`), and
`hC : ContinuityStatement`, `hQ : MorphismPropertyStatement` are the
hypotheses under which `quasiEtaleSiteInduction hH hC hQ X` is defined (module
`InducedEquivariantSite`). `X` is an `H`-space (`GSpace K H`) and `W` an object
of `Qét(X_{G/H}(G))`, i.e. of `EquivariantQuasiEtaleSite` of the induced
`G`-space.

- `siteHom hH hC W`: the structure morphism `W → X_{G/H}` of `W`, as a morphism
  of `G`-objects (`W.hom.hom`).
- `baseSpace hH hC W`: the `H`-space whose `H`-object is
  `baseAction (siteHom hH hC W)` (lemma `baseSpace_obj`). Its underlying space
  is Hausdorff as a subspace of the Hausdorff space of `W`, and its action is
  continuous because it is the restriction to an invariant domain
  (`IsContinuousAction.invariantDomainAction`) of the restriction of `W` to `H`.
- `baseSpaceHom hH hC W hP : baseSpace hH hC W ⟶ X`: the `H`-morphism
  `baseActionHom` of `InducedSiteBase`.
- `baseObj hH hC W hP hR`: the object `π⁻¹(X_H) → X` of `Qét(X(H))`. It is
  quasi-étale by `quasiEtale_baseHomV`, since `W` is Hausdorff and `W → X_{G/H}`
  is quasi-étale.
- `baseObjIso hH hC hQ W hP hR hI`: given
  `hI : IsIso (lift H (baseInclusion (siteHom hH hC W)))`, an isomorphism in
  `Qét(X_{G/H}(G))` from the induction of `baseObj hH hC W hP hR` to `W`. Its
  underlying isomorphism of `G`-spaces is `lift H (baseInclusion …)`, the
  morphism `Ind(π⁻¹(X_H)) → W` adjoint to the inclusion `π⁻¹(X_H) → W`.
- `essSurj_quasiEtaleSiteInduction_of_isIso hH hC hQ hP hR hI`: the functor
  `quasiEtaleSiteInduction hH hC hQ X` is essentially surjective, given
  `hI : ∀ π : Y ⟶ inducedAction H X.obj, IsIso (lift H (baseInclusion π))`.
  This condition is proved separately from `hP` (`isIso_lift_baseInclusion`, module
  `InducedSiteBaseIso`).

## Proof

`baseHomV_eq_domainRestrict` is `domainRestrict_comp_assoc` read backwards.

`quasiEtale_baseHomV`: by `baseHomV_eq_domainRestrict`, `baseHomV π` is the
restriction of `π` over the open subset `image of copy H` of `X_{G/H}`, followed
by an isomorphism (`isIso_copyDomain_foldHom`, which uses `hP`). The domain
`preimageDomain π H` is by definition the open domain
`π⁻¹(image of copy H)`, so `hR` applied to `π.hom` and this open subset says
the restriction is quasi-étale. Quasi-étale morphisms respect isomorphisms
(`MorphismProperty.RespectsIso.postcomp`).

`baseObjIso`: `MorphismProperty.Over.isoMk` of an isomorphism of `G`-spaces:
`ObjectProperty.isoMk` lifts the isomorphism of `G`-objects
`asIso (lift H (baseInclusion π))` (between the induction of `π⁻¹(X_H)` and the
`G`-object of `W`) to an isomorphism of `G`-spaces. The compatibility
with the structure morphisms is checked on underlying morphisms of
`G`-objects, where it is `lift_baseInclusion_comp` of `InducedSiteBase`:
`lift H (baseInclusion π) ≫ π = (inductionFunctor H).map (baseActionHom π hP)`.

`essSurj_quasiEtaleSiteInduction_of_isIso`: every `W` is isomorphic to the
induction of `baseObj hH hC W hP hR` by `baseObjIso`.
