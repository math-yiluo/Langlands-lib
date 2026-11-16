# Open and closed immersions of analytic spaces

This unit defines open and closed immersions in the Library's localized category
of analytic spaces, `SaturatedAtlasPresentation.LocalizedCategory`, as two
morphism properties `openImmersion` and `closedImmersion`. It also defines the
underlying chart-level notion of closed immersion for strong maps between
constructed saturations. It proves the following basic facts.
- Closed immersions are finite in the Library's sense.
- Both properties are stable under isomorphisms and contain all isomorphisms,
  in particular all identities.
- Open immersions are open embeddings of the underlying topological spaces.

It also proves that an admissible epimorphism of normed algebras is a finite
Banach algebra map.

The unit makes no further claim. It does not prove that either class is stable
under composition, base change or extension of the ground field. It does not
prove that a closed immersion is a homeomorphism onto a closed subset, or a
monomorphism. It does not prove that the localized notion of closed immersion
can be tested on any chosen presentation. No comparison with algebraic open or
closed immersions is stated here; that is the subject of later statements.

## Provenance

The main source is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. The second
source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The motivating source is Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The pages below were read in the registered files.

- Berkovich 1993, Definition 1.3.1 and the paragraph after it, printed p.23
  (PDF p.20). A subset of an analytic space `X` is an analytic domain if the
  affinoid domains contained in it form a net on it. An analytic domain `Y`
  carries an atlas of the affinoid domains inside it and a canonical morphism
  `ν : Y → X`. Every morphism `φ : Z → X` with `φ(Z) ⊆ Y` factors uniquely as
  `φ = ν ∘ ψ`. The paragraph ends: "A morphism φ : Y → X that induces an
  isomorphism of Y with an open Φ-analytic domain in X is said to be an open
  immersion. If the class Φ is dense, then all open subsets of X are
  Φ-analytic domains."
- Berkovich 1993, Lemma 1.3.7 and the definition after its proof, printed
  pp.27–28 (PDF pp.24–25). For a morphism `φ : Y → X` the lemma shows that
  two conditions are equivalent. Condition (a) is pointwise: every point `x`
  of `X` lies in finitely many affinoid domains `Vᵢ` for which each
  `φ⁻¹(Vᵢ) → Vᵢ` is a closed immersion of affinoid spaces. Condition (b)
  asks that `φ⁻¹(V) → V` be a closed immersion of affinoid spaces for every
  affinoid domain `V ⊆ X`. A morphism with these properties is called a
  closed immersion. The text then notes that a closed immersion induces a
  homeomorphism of `|Y|` with its image in `|X|`.
- Berkovich 1990, Corollary 2.3.2(ii) and the definition after its proof,
  printed p.33 (PDF p.47). For a morphism of affinoid spaces
  `M(ℬ) → M(𝒜)`, the direct image of the structure sheaf is coherent with
  surjective structure map if and only if `𝒜 → ℬ` is an admissible
  epimorphism. Such a morphism is called a closed immersion.
- Berkovich 1990, §3.1, printed p.49 (PDF p.63), defines open immersions as
  isomorphisms onto open subsets with the induced structure, and closed
  immersions as homeomorphisms onto closed subsets with coherent direct image
  and surjective structure map. Proposition 3.1.4(i) shows that preimages of
  affinoid domains under closed immersions are affinoid domains. This page is
  background for the comparison with the 1993 definitions; it is not
  formalized here.
- Conrad, printed p.19, in the proof of Proposition 5.11(3), uses that the
  analytification of separated algebraic spaces locally of finite type is
  compatible with open and closed immersions. That is why this unit is needed.

## Derived formulation

**Open immersions.** The definition is Berkovich's literal one. The Library
already has open analytic domains in `InvariantAnalyticDomains`. For an object
`Y` of the localized category, `presentationOf Y` is the saturated presentation
underlying `Y`; it is `localizedObjectEquiv.symm Y`, not a choice. For an open
subset `U` of its space, `openDomain U hU` is the analytic domain with carrier
`U`. It exists because saturated presentations have all local domains, the
Library's form of Berkovich's remark that all open subsets are analytic domains
when the class is dense. `domainObj Y D` is the analytic space of the domain
`D`, and `domainι Y D` is Berkovich's canonical morphism `ν`. A morphism
`φ : X ⟶ Y` "induces an isomorphism of `X` with the open domain `U`" when it
equals `e.hom ≫ domainι Y (openDomain U hU)` for an isomorphism
`e : X ≅ domainObj Y (openDomain U hU)`. By the unique factorization through
`ν`, this is the same as saying that `φ` lands in `U` and its factorization
through `U` is an isomorphism.

**Closed immersions.** The Library has no closed analytic subspaces and no
coherent sheaves of ideals, so the definition uses condition (b) of
Lemma 1.3.7, with Corollary 2.3.2(ii) of the 1990 book for closed immersions
of affinoid spaces. The chart-level predicate
`AffinoidAtlasPresentation.StrongHom.IsClosedImmersion g` applies to a strong
map `g` between the saturated presentations of two atlas presentations. It
replaces "every affinoid domain" by "every recognized affinoid subset of the
target". These are the Library's constructed affinoid domains in the full
recognition of the saturated atlas, defined in `RecognizedAffinoidCategory`.
They contain every original local domain and may be empty. The Library has not
proved that they are all affinoid domains in Berkovich's sense. The predicate
then asks for the following.
1. The preimage of the target subset `W` is again a recognized subset `V`,
   given as `V.locus = g.baseMap ⁻¹' W.locus`.
2. The bounded map from the algebra of `W` to that of `V`, constructed by the
   Library's `fullRecognitionPairs` extension of `g`, is an admissible
   epimorphism.

This follows the pattern of the published `StrongHom.IsFinite` of
`FullRecognitionFiniteMorphisms`, which formalizes the "finite" half of the
same lemma.

The localized property `closedImmersion` follows the pattern of the published
`SaturatedAtlasPresentation.etale` of `EtaleSite`. A morphism is a closed
immersion when its arrow is isomorphic, in the arrow category, to the image
under `localizationFunctor` of a chart-level closed immersion between
constructed saturations `ofSaturation A ⟶ ofSaturation B`. Berkovich's notion
is invariant under isomorphisms of source and target, so the closure under arrow
isomorphisms adds nothing on his side. On the Lean side, it makes the property
independent of how the objects are presented. Because `ofSaturation` produces
presentations in universes `{u, v, v}`, the property is defined on
`LocalizedCategory.{u, v, v}`, as `etale` is. Open immersions are defined on
`LocalizedCategory.{u, v, w}` for all three universes.

## Hypotheses

Everything lies in `Langlands.Analytic`. In the first section `K : Type u` is a
normed field and `R : Type v`, `S : Type w` are normed commutative
`K`-algebras. From the second section on, `K` is a normed field that is
ultrametric and complete, with no nontriviality assumption.

## Declarations

`BoundedAlgHom.IsAdmissibleEpi.isFiniteBanach` says that an admissible
epimorphism `f : BoundedAlgHom K R S` is a finite Banach algebra map
(`IsFiniteBanach`), with one generator `1`. The proof takes the norm-controlled
lifts from `isAdmissibleEpi_iff_normControlledLifts`: every `y` has a preimage
`a` with `‖a‖ ≤ C‖y‖`. The coefficient vector with single entry `a` maps to
`f a * 1 = y`, and its maximum norm is `‖a‖`.

`AffinoidAtlasPresentation.StrongHom.IsClosedImmersion g`, for
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`, says: for every
recognized affinoid subset `W` of `B` there are a recognized affinoid subset
`V` of `A` and a proof `h` that `g` maps the range of `V` into the range of
`W`, such that `V.locus = g.baseMap ⁻¹' W.locus` and
`(g.fullRecognitionPairs.pullback V W h).IsAdmissibleEpi`.

`SaturatedAtlasPresentation.closedImmersion` is the morphism property of
`LocalizedCategory.{u, v, v}` that holds for `φ` when there are atlas
presentations `A`, `B`, a morphism `g : ofSaturation A ⟶ ofSaturation B` with
`StrongHom.IsClosedImmersion g`, and an isomorphism of arrows
`Arrow.mk (localizationFunctor.map g) ≅ Arrow.mk φ`.

`SaturatedAtlasPresentation.openImmersion` is the morphism property of
`LocalizedCategory.{u, v, w}` that holds for `φ : X ⟶ Y` when there are an open
subset `U` of the space of `presentationOf Y` and an isomorphism
`e : X ≅ domainObj Y (openDomain U hU)` with
`e.hom ≫ domainι Y (openDomain U hU) = φ`.

`SaturatedAtlasPresentation.openDomainIso ψ U hU`, for an isomorphism
`ψ : Y ≅ Z` and an open subset `U` of `Y`, is the isomorphism from the open
domain `U` of `Y` to the open domain of `Z` given by the preimage of `U` under
the point map of `ψ.inv`. Its two directions are the restrictions
`domainRestrict` of `ψ.hom` and `ψ.inv`. The inverse laws follow from
`domainRestrict_comp`, the inverse laws of `ψ` and cancellation of the
monomorphism `domainι`.

## Lemmas

- `StrongHom.IsClosedImmersion.isFinite`: a closed immersion is finite
  (`StrongHom.IsFinite`). The same `V` works, since `V.locus` equals
  `univ ∩ g.baseMap ⁻¹' W.locus`, and the admissible epimorphism is finite
  Banach by the first declaration.
- `StrongHom.isClosedImmersion_id`: the identity is a closed immersion. Take
  `V = W`; the Library's `fullRecognitionPairs_id_pullback_self` identifies the
  bounded map with the identity, which is an admissible epimorphism.
- `closedImmersion_localizationFunctor_map`: the image of a chart-level closed
  immersion is in `closedImmersion`, with the identity arrow isomorphism.
- `closedImmersion` respects isomorphisms, by composing arrow isomorphisms.
- `closedImmersion_of_isIso`: every isomorphism is a closed immersion. The
  source is isomorphic to a constructed saturation `ofSaturation A`
  (`exists_iso_localizationFunctor_obj_ofSaturation`), and the identity of
  `ofSaturation A` gives the arrow isomorphism. Hence `closedImmersion`
  contains identities.
- `openImmersion_domainι`: the canonical morphism of an open domain is an open
  immersion.
- `isOpenEmbedding_domainι`: its point map is the inclusion of the open subset
  `U` (`domainι_apply`), so it is an open embedding.
- `openImmersion.isOpenEmbedding`: the point map of an open immersion is an
  open embedding, as the composite of the homeomorphism given by `e` and the
  open embedding of `domainι`.
- `map_inv_map_hom_apply`: the point map of `ψ.inv` undoes that of `ψ.hom`.
- `openDomainIso_hom_domainι`: `openDomainIso ψ U hU` followed by the canonical
  morphism into `Z` equals the canonical morphism into `Y` followed by
  `ψ.hom`.
- `openImmersion` respects isomorphisms. Precomposing with an isomorphism
  changes `e`. Postcomposing with `ψ : Y ≅ Z` replaces `U` by its image under
  `ψ`, through `openDomainIso`.
- `openImmersion_id`: the identity of `X` is an open immersion onto the open
  domain `univ`. The isomorphism has the lift `domainLift` of the identity as
  its forward map and `domainι` as its inverse. Hence `openImmersion` contains
  identities.
- `openImmersion_of_isIso`: every isomorphism is an open immersion, by
  postcomposing the identity with it.
