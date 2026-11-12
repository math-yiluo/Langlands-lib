# Derived comparison for equivariant compactly supported cohomology

Author: Worker 26. Builds on `Langlands.Cohomology.DiscreteSheafDerivedComplex`
(the derived complexes `compactComplex` and `sheafCompactComplex`),
`Langlands.Sheaf.Equivariant.TwistedCompactComparison` (`smoothForget`,
`smoothCompactInclusion`, the exactness instances for restriction of discrete
sheaves, and `compactComparison`), and the published derived-category
infrastructure: `Langlands.Cohomology.DerivedPlus` (`derivedComplex`,
`homologyIso`, `descHom`), `Langlands.Cohomology.AcyclicResolution.DerivedComparison`
(`derivedResolutionFunctor`, `derivedResolutionIso`,
`derivedResolutionHomologyIso` and their lemmas),
`Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison`
(`derivedCompComparison`), `Langlands.Cohomology.DerivedExactPostcomposition`
(`derivedPostcompIso`), `Langlands.Cohomology.ExtendMap`
(`extendMapIso_hom_app`), `Langlands.Cohomology.ExactBaseChange` and
`Langlands.Cohomology.LeftExactHomology`. It also uses
`DerivedSections.isZero_rightDerived_succ_of_preservesHomology` from
`Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction`.

## Maps of derived complexes induced by natural transformations

Let `C` and `D` be abelian categories with derived categories chosen by
`[HasDerivedCategory.{w₁} C]` and `[HasDerivedCategory.{w₂} D]`, `C` with enough
injectives, and `τ : G ⟶ H` a natural transformation of additive functors
`C ⥤ D`. The published `derivedComplexCongr` (in `DerivedExactComposition`)
treats natural isomorphisms; this section does the same for an arbitrary
natural transformation, by the same method.

- `resolutionNatTrans τ : derivedResolutionFunctor G ⟶ derivedResolutionFunctor H`:
  on a natural-indexed complex `K`, the localization of
  `NatTrans.mapHomologicalComplex τ` at the integer extension of `K`.
- `derivedComplexMapOfResolution τ I`, for an injective resolution `I` of `X`:
  the composite `derivedResolutionIso G I ≫ (resolutionNatTrans τ).app I ≫
  (derivedResolutionIso H I)⁻¹`, a map from `(derivedComplex G ⋙ ι).obj X` to
  `(derivedComplex H ⋙ ι).obj X`, where `ι = DerivedCategory.Plus.ι`.
- `derivedComplexMapOfResolution_naturality`: it commutes with
  `(derivedComplex G ⋙ ι).map f` and `(derivedComplex H ⋙ ι).map f` for every
  morphism of injective resolutions over `f : X ⟶ Y` (naturality of
  `derivedResolutionIso` and of `resolutionNatTrans`).
  `derivedComplexMapOfResolution_eq`: it does not depend on the resolution
  (apply naturality to `descHom (𝟙 X)`).
- `derivedComplexMap τ : derivedComplex G ⋙ ι ⟶ derivedComplex H ⋙ ι`: the
  natural transformation with components computed by Mathlib's chosen injective
  resolutions; `derivedComplexMap_app` computes it with any resolution.
- `derivedResolutionHomologyIso_hom_natTrans`: on cohomology in degree `n`,
  `(resolutionNatTrans τ).app K` corresponds, under
  `derivedResolutionHomologyIso`, to the map induced by
  `NatTrans.mapHomologicalComplex τ` on the degree `n` homology of the images of
  `K`. The proof combines naturality of `DerivedCategory.homologyFunctorFactors`,
  the published `extendMapIso_hom_app` and Mathlib's
  `extendHomologyIso_hom_naturality`.
- `derivedComplexMapOfResolution_homology` and `derivedComplexMap_homology`:
  under `DerivedPlus.homologyIso`, the degree `n` cohomology of the map is
  Mathlib's `(NatTrans.rightDerived τ n).app X` (via
  `derivedResolutionIso_homology` and `InjectiveResolution.rightDerived_app_eq`).

## The derived comparison on a twisted site

Setting of `TwistedCompactComparison`: a twisted site `twistedTopology ρ J`
built from `C : Type u` with `Category.{v} C`, a morphism property `P`
(`[P.RespectsIso]`, `[P.ContainsIdentities]`), an object `X`, a topological group
`G : Type uG` with `ρ : G →* Aut X`, a translation-invariant topology `J` on
`P.Over ⊤ X` with `[LocallySmall.{w} (P.Over ⊤ X)]`; a commutative ring
`R : Type w`; `L : LocalActionSystem (TwistedOver P ρ) G`; points
`Φ : I → J.Point.{w}` indexed by a topological space `I`; sheafification for `J`
and for the twisted topology; `[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`;
enough injectives in both sheaf categories; and the hypothesis of
`TwistedGodement` that module presheaves on `P.Over ⊤ X` have pointwise right
Kan extensions along `(ι P ρ).op`. Derived categories: `w₁` for discrete
sheaves on the twisted site, `w₂` for `Sheaf J (ModuleCat R)`, `w₃` for
`SmoothRep R G`, `w₄` for `ModuleCat R`. Write `X₀ = (base P ρ).obj` (`X` over
itself).

- `discreteRestriction J R L`: the inclusion of discrete sheaves followed by
  restriction to the site over `X`, the role of `b^*`. It is exact (instances
  from `TwistedCompactComparison`), so its positive right derived functors
  vanish: `isZero_discreteRestriction_rightDerived`.
- `restrictionCompactComparison J R L Φ`: the natural transformation from
  `derivedComplex (discreteRestriction ⋙ sheafCompactSections J Φ R X₀) ⋙ ι` to
  `discreteRestriction ⋙ (sheafCompactComplex J Φ R X₀ ⋙ ι)` with components the
  published `derivedCompComparison` for the identity of
  `discreteRestriction ⋙ sheafCompactSections`; every object is acyclic for the
  exact functor. Naturality is `derivedCompComparison_naturality`.
- `compactComplexComparison J R L E`, for `E : PointEquivariance ρ Φ`: the
  natural transformation

  ```text
  (compactComplex J R L E ⋙ ι) ⋙ (smoothForget R G).mapDerivedCategory
    ⟶ discreteRestriction J R L ⋙ (sheafCompactComplex J Φ R X₀ ⋙ ι),
  ```

  the composite of `(derivedPostcompIso (discreteCompactSections J R L E)
  (smoothForget R G)).hom`, `derivedComplexMap (smoothCompactInclusion J R L E)`
  and `restrictionCompactComparison J R L Φ`. The source is the derived complex
  of smooth compactly supported global sections of a discrete sheaf, with the
  action of `G` forgotten by the exact functor `smoothForget`; the target is the
  derived complex of compactly supported sections over `X₀` of its restriction.
- `inclusionRestrictionComparison_homology`: in degree `n`, the last two
  factors induce, under the identifications `DerivedPlus.homologyIso`, the map
  `(LeftExactHomology.derivedNatTrans (smoothForget R G)
  (discreteCompactSections J R L E) n).app F ≫ (compactComparison J R L E n).app F`.
  Since `compactComparison` is defined as the inverse of that `derivedNatTrans`
  followed by `NatTrans.rightDerived τ n` and `compComparisonNatTrans`, the
  proof uses `derivedComplexMap_homology`, the published
  `derivedCompComparison_homology` and cancellation of the inverse.

Not proved: the cohomology of the first factor, `derivedPostcompIso`, is not
compared with `LeftExactHomology.derivedNatTrans`; so the module does not state
that the degree `n` cohomology of `compactComplexComparison` is
`compactComparison J R L E n`, although the remaining two factors are
identified exactly as above. Nor is it proved that `compactComplexComparison` is
an isomorphism.

## Provenance and scope

Derived infrastructure. Source, read in the original by Worker 26: Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), §1.5, Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any
étale abelian sheaf `F` on `X(G)` there are canonical isomorphisms
`H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0` [sic, for `q ≥ 0`]." Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999), §2,
printed p.304 = PDF p.6, uses compactly supported cohomology `RΓ_c` of étale
sheaves in smooth modules over `U(ẽ)`.

Correspondence. As recorded in `TwistedCompactComparison`, the published
`compactComparison J R L E q` has the shape of Berkovich's maps in degree `q`,
`compactComplex` has the shape of `RΓ_c(X{G}, F)`, and the restriction plays the
role of `b^*`. `compactComplexComparison` is a single map of complexes in the
derived category of `R`-modules from `RΓ_c(X{G}, F)` (with the action
forgotten) to `RΓ_c(X, b^*F)`; Berkovich states the comparison only on
cohomology groups, so the derived-category form is our construction. Its
relation to the degree-wise maps is the content of
`inclusionRestrictionComparison_homology` described above.

Differences and omissions: as in `TwistedCompactComparison`, an arbitrary site
with a group action and points replaces the analytic étale site, and derived
functors are taken among discrete sheaves. Not constructed or proved here: that
the comparison is an isomorphism (Berkovich's corollary), the full degree-wise
identification noted above, the spectral sequence of Corollary 1.5.2(i), and any
analytic instance.

Universes: `C : Type u` with `Category.{v} C`, `G : Type uG`, `I : Type uI`,
ring and modules in universe `w`; derived categories in `w₁`, `w₂`, `w₃`, `w₄`;
in the general section, `C : Type uC` with `Category.{vC}`, `D : Type uD` with
`Category.{vD}`.

Source registrations: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, file
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
