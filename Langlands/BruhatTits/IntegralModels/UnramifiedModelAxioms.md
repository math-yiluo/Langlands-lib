# Helper lemmas for KP Axiom 4.1.20 from the maximal unramified extension

This helper module collects the lemmas that the proof of KP Axiom 4.1.20 in
`ModelAxiomsUnramified` uses. Here KP is Kaletha–Prasad, *Bruhat–Tits theory: a
new approach* (2023). The following lemmas take an unramified statement as a
hypothesis.

- `one_inf_pointwiseFixer_le` takes `UnramifiedOneFixerClosureStatement`.
- `nonempty_hom_of_unramified_le` and `exists_isIso_neutral_of_unramified_eq`
  take `UnramifiedSmoothHomExtensionStatement` (KP Corollary 2.10.10).

Throughout, `K = inertiaFixedField F` is the maximal unramified extension and
`G(K)^1` is `characterValuationKernel (MaximalUnramified.valuation F) G_K`, the
common kernel of the valuations of the rational characters.

## Generic lemmas

- `rationalPoints_map_id_apply`: the identity homomorphism acts trivially on
  rational points.
- `comp_hom_eq_of_generic`: let `φ₁ : M₁ → M₂`, `φ₂ : M₂ → M₄`, `ψ₁ : M₁ → M₃`,
  `ψ₂ : M₃ → M₄` be morphisms of integral models over `R` whose generic fibre is
  the identity of `G`. Then `φ₁ ≫ φ₂ = ψ₁ ≫ ψ₂`. Both composites have the
  identity as generic fibre, and a morphism of integral models over a domain
  is determined by its generic fibre (Library `IntegralModel.hom_eq_of_generic`).
- `isIso_hom_of_hom`: if there are morphisms `M → N` and `N → M` over the
  identity of `G`, then the first one is an isomorphism. The proof uses the
  Library `IntegralModel.Iso.ofHoms` (module `GenericRigidity`).
- `inf_le_inf_of_le_of_inf_le`, `inf_eq_inf_of_le_of_inf_eq`: if `E ≤ G₁` and
  `G₁ ⊓ X ≤ G₁ ⊓ Y` (respectively `=`), then `E ⊓ X ≤ E ⊓ Y` (respectively
  `=`). Elementary subgroup lattice facts.

## Facets

Let `A` be a real affine space and `Ψ` a set of affine functions on `A`.

- `nonneg_iff_of_mem_facet`: if `y` lies in the facet of `x` for `Ψ`, then
  every `ψ ∈ Ψ` has `0 ≤ ψ x ↔ 0 ≤ ψ y`. Points of one facet give every root
  the same sign (Library `AffineRootSystem.mem_facet`).
- `forall_nonneg_iff_of_subset_facet`: two nonempty subsets `Y`, `Y'` of one
  facet have the same nonnegative roots: for `ψ ∈ Ψ`, `ψ ≥ 0` on `Y` exactly
  when `ψ ≥ 0` on `Y'`. Both conditions are equivalent to `0 ≤ ψ x`.

## Presentations of indices

Let `B` be valuation building data for `G` over `F` and `C` building data for
`G_K` over `K`.

- `BuildingModelIndex.exists_eq_translatedApartmentMap`: every index `Ω` of a
  building model family (a bounded subset or a facet) has the form
  `g · apartmentMap '' Ωa`. This is read off from the two constructors of the
  index set.
- `BuildingModelIndex.nonempty_of_eq_translatedApartmentMap`: any such `Ωa` is
  nonempty, because `Ω` is.
- `unramifiedPointwiseFixer_anti`: pointwise fixers in `G(K)` reverse inclusion.

Now let `e : B.ReducedBuilding → C.ReducedBuilding` be equivariant along
`rationalExtend`, and let `a` be a real affine map of apartments with
`e (apartmentMap w) = C.apartmentMap (a w)`. Assume (`hbdd`) that every
apartment presentation `Ωa` of an index is bounded.

- `exists_unramified_presentation`: `e '' Ω` is a translate
  `g_K · C.apartmentMap '' Ya` of a nonempty set `Ya` of the apartment of `C`
  on which every affine function is bounded above. Take `Ya = a '' Ωa`. The
  helpers `image_translatedApartmentMap` and `bddAbove_image_image` of
  `GeneralMorphismAxiomsUnramified` give the image formula and the
  boundedness.
- `one_inf_pointwiseFixer_le`: assume `UnramifiedOneFixerClosureStatement`,
  and (`hface`) that faces lie in the apartment closure of the facets
  containing them. Let `Ω ≺ Ω'` be a pair requiring a model morphism
  (`ModelMorphismRequired`). Then
  `G(K)^1 ∩ Fix(e '' Ω') ≤ G(K)^1 ∩ Fix(e '' Ω)`. The proof:
  1. `BuildingModelFamily.exists_chart_of_modelMorphismRequired`
     gives one chart `g` with presentations `Ωa`, `Ωa'` and
     `Ωa ⊆ closure Ωa'`.
  2. The images in `C` satisfy `a '' Ωa ⊆ closure (a '' Ωa')`, because `a` is
     continuous for the affine topologies (`image_subset_closure_image`).
  3. The closure statement replaces `Fix(e '' Ω')` by the fixer of the image of
     the closure of `a '' Ωa'`, inside `G(K)^1`.
  4. That fixer lies in `Fix(e '' Ω)` by antitonicity.

  The lemma has `set_option maxHeartbeats 1000000`. The image identities are
  stated as explicit `have`s, because inferring them makes `whnf` time out.

## Zero points and morphisms over `𝒪[F]`

- `UnramifiedZeroDatum.zeroPoints_le_unramifiedCharacterValuationKernel`:
  `G(K)^0 ≤ G(K)^1` for every zero datum over `K` (KP Definition 2.6.23(1) and
  Lemma 2.6.24). The valuation `MaximalUnramified.valuation F` is equivalent
  to the one used by the Library lemma `zeroPoints_le_characterValuationKernel`
  (`MaximalUnramified.valuation_isEquiv`), and character-valuation kernels
  depend only on the equivalence class (`characterValuationKernel_eq_of_isEquiv`).
- `nonempty_hom_of_unramified_le`: let `M`, `N` be integral models of `G` over
  `𝒪[F]` with `M` smooth. If the integral points of the unramified base change
  of `M` lie in those of `N`, then there is a model morphism `M → N` over the
  identity of `G`. This is `UnramifiedSmoothHomExtensionStatement` for the
  identity homomorphism.
- `exists_isIso_neutral_of_unramified_eq`: if two relative-component data over
  `𝒪[F]` have neutral models with the same unramified integral points, there
  is a morphism of the neutral models over the identity that is an
  isomorphism. Neutral models are smooth, so the previous lemma gives
  morphisms both ways; then use `isIso_hom_of_hom`.

## Sources

- KP Definition 2.6.23(1) and Lemma 2.6.24, printed pp. 104–105 / PDF
  pp. 135–136: `G(k)^0 ⊂ G(k)^1`.
- KP Corollary 2.10.10, printed p. 124 / PDF p. 155: homomorphisms of smooth
  models are determined by integral points.
- KP Notation 1.3.34, printed p. 26 / PDF p. 57, defines the closure order
  `Ω ≺ Ω'`. The preamble of Axiom 4.1.22, printed p. 163 / PDF p. 194,
  gives the comparison morphisms from the models at `Ω'` to those at `Ω`.

The other lemmas are elementary. The role of KP Corollary 2.10.10 over a
finite residue field is derived: `𝒪[F]`-points alone do not determine a
smooth model there, so the hypothesis compares points after base change to
the maximal unramified integers. The residue field of those integers is
separably closed.
