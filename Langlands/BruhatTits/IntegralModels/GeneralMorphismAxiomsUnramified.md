# The general morphism clauses of KP Axiom 4.1.22 from the unramified kernel statement

This module derives `M.SatisfiesGeneralMorphismAxioms`, the preamble and
part (1) of KP Axiom 4.1.22, for a model family `M` over `↥𝒪[F]`. It assumes
the statement `UnramifiedModelKernelStatement` (KP
Proposition 8.4.15 over the integers of the maximal unramified extension).
The construction in `ModelAxiomsUnramified` provides the required integral
point description of the neutral models over the maximal unramified integers.

Throughout, `fixedFieldIntegers F` are the integers of the maximal unramified
extension `inertiaFixedField F`. `C` is a building datum for the base change
of `G` to that field, and `E` is an unramified zero datum. The module installs
the coefficient algebra `↥𝒪[F] → fixedFieldIntegers F`, its scalar tower and
its local-homomorphism instance from Mathlib's `Valuation.HasExtension`
instances. These are the instances that define
`IntegralModel.baseChangeUnramified`.

## Declarations

- `RelativeComponentModelHom.hasSmoothConnectedUnipotentKernel_of_unramified`
  (one ordered pair). Take `φ : RelativeComponentModelHom source target` over
  `↥𝒪[F]`, a rational point `g` of the base-changed group, and subsets
  `Ωa`, `Ωa'` of the apartment of `C`. Assume that `Ωa` is nonempty, that
  `Ωa'` is bounded (every real affine functional is bounded above on it), and
  that `Ωa` lies in the closure of `Ωa'` for the affine topology. Assume also
  that the base changes to `fixedFieldIntegers F` of the target and source
  neutral models have the integral points
  `E.zeroPoints ⊓ C.pointwiseFixer (g • A(Ωa))` and
  `E.zeroPoints ⊓ C.pointwiseFixer (g • A(Ωa'))`. Then, given
  `UnramifiedModelKernelStatement`, `φ.HasSmoothConnectedUnipotentKernel`
  holds.
- Transfer lemmas for a real affine map `a` from the apartment of `B` to the
  apartment of `C`:
  - `continuous_affineApartmentMap`: `a` is continuous for the two affine
    topologies.
  - `image_subset_closure_image`: if `Ωa ⊆ apartmentClosure B Ωa'`, then
    `a '' Ωa` lies in the affine-topology closure of `a '' Ωa'`.
  - `bddAbove_image_image`: `a` carries bounded subsets to bounded subsets.
  - `image_translatedApartmentMap`: let `e` be a map of reduced buildings that
    is equivariant along `rationalExtend` and satisfies
    `e (apartmentMap w) = C.apartmentMap (a w)`. Then `e` carries
    `g • A(Ωa)` to `(rationalExtend g) • A(a '' Ωa)`.
- `BuildingModelFamily.exists_chart_of_modelMorphismRequired`: suppose faces
  lie in the closure of the facets containing them. Then every required
  morphism pair `ModelMorphismRequired B Ω Ω'` is an
  `ApartmentSubsetPrecedes B Ω Ω'` pair: both indices are presented in one
  translated chart with `Ωa ⊆ closure Ωa'`.
- `BuildingModelFamily.satisfiesGeneralMorphismAxioms_of_unramified`. Take a
  family `M` over `↥𝒪[F]` and an unramified datum `(C, E, e, a)`, where `e` and `a`
  are as above. Assume three things:
  - `hpoints`: the base change of every neutral model `(M.model Ω).neutral`
    has integral points `E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`.
  - `hbdd`: every apartment presentation `Ω = g • A(Ωa)` of an index has `Ωa`
    bounded.
  - `hface`: faces lie in the closure of the facets containing them.

  Then `UnramifiedModelKernelStatement` implies `M.SatisfiesGeneralMorphismAxioms`.
- `isBoundedSubset_of_buildingModelIndex`: take parahoric building data `P`
  with a realization `R` and a splitting `T` satisfying the seven predicates of
  the target statement. If an index `Ω` of a model family equals `g • A(Ωa)`,
  then `Ωa` is bounded.
- `satisfiesGeneralMorphismAxioms_of_unramified_of_axioms`: the previous family
  theorem for `B = P.toValuationBuildingData` under the seven predicates of the
  target statement. `hbdd` and `hface` are discharged, so only
  `UnramifiedModelKernelStatement`, the datum `(C, E, e, a)` with its two
  compatibilities, and `hpoints` remain as hypotheses.

## Proof

The one-pair theorem first notes that both base-changed neutral models are
smooth (`isSmooth_baseChange` of the smooth neutral models). It applies
`UnramifiedModelKernelStatement` to them, with the explicit models
`target.neutral.baseChangeUnramified` and `source.neutral.baseChangeUnramified`.
This gives the kernel property for every model homomorphism between the
base changes with identity generic fibre.
`Hom.isSmoothConnectedUnipotent_kernel_of_baseChangeUnramified` (module
`SpecialFibreKernelDescent`) then descends the property to
`kernel φ.neutral.specialFibreMap`. Matching the instance arguments of the
base-changed models against the statement needs a heartbeat budget of
1,000,000, set locally on this theorem and on the family theorem.

The transfer lemmas are direct. Composing an affine functional with `a` gives
an affine functional, which is continuous for the affine topology of `B` and
bounded above on bounded sets. The continuous image of a closure lies in the
closure of the image. The image lemma rewrites with the two compatibilities of
`e`.

`exists_chart_of_modelMorphismRequired` splits `ModelMorphismRequired` into
its two cases. An `ApartmentSubsetPrecedes` pair is already the conclusion.
For a facet pair `FacetPrecedes B F F'`, the two facets are presented in one
chart as `Fa`, `Fa'` with `Fa` a face of `Fa'`, and `hface` gives
`Fa ⊆ apartmentClosure B Fa'`.

The family theorem rewrites the general clauses with
`satisfiesGeneralSpecialFibreClauses_iff` (module `GeneralClausesReduction`),
so only the smooth, connected and unipotent kernel remains to be shown. It
obtains a common chart `g`, `Ωa`, `Ωa'` for the pair, and applies the one-pair
theorem with the point `rationalExtend g` and the subsets `a '' Ωa`,
`a '' Ωa'`. The image `a '' Ωa` is nonempty because every index is nonempty
(`BuildingModelIndex.nonempty`). Boundedness comes from `hbdd` and
`bddAbove_image_image`, and the closure order from `image_subset_closure_image`.
The two integral-point equations follow by rewriting `hpoints` with the
presentations and `image_translatedApartmentMap`.

`isBoundedSubset_of_buildingModelIndex` uses that every index has one bounded
presentation. It is either a nonempty bounded subset of a translated apartment
or a translated facet. Facets are bounded under the apartment axioms
(`isBoundedSubset_of_isFacet_of_satisfiesApartmentAxioms`, module
`ApartmentFacetBounds`). Boundedness then transfers to the given presentation
by `isBoundedSubset_of_image_translatedApartmentMap_eq_of_axioms` (same
module), which rests on the Library's KP Proposition 4.2.24
(`apartmentConjugacyFixingIntersection`). In the axioms-level family theorem,
`hface` is `subset_apartmentClosure_of_isFaceOf` from the same module.

## Provenance

KP prove part (1) of Axiom 4.1.22 for their Bruhat–Tits group schemes by
Proposition 8.4.15 over the maximal unramified extension and unramified
descent (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, §8.4, §9.5 and
Axiom 4.1.22, printed p. 163 / PDF p. 194). The implication from the
kernel condition to the torus clause of the preamble is the derived argument
in `GeneralClausesReduction`. The chart bookkeeping (common charts, transfer
along the apartment map `a`, chart independence of boundedness) is internal to
this formalization: KP state the axiom for subsets of the building and do not
fix charts.
