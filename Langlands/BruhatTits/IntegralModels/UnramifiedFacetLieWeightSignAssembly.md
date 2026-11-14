# Assembly of the unramified Lie-weight sign formula

Module `Langlands.BruhatTits.IntegralModels.UnramifiedFacetLieWeightSignAssembly`.

This module proves the Library statement
`UnramifiedFacetLieWeightSignStatement` (Kaletha–Prasad Theorem 8.4.19(2) for
the apartment of the maximal unramified building data `C`) as the theorem
`unramifiedFacetLieWeightSign`. It puts together results that are already in
the Library: the rootwise images, the negative-root reduction, the
kernel-smoothness theorem and the positive-reduction theorem.

## Setting

`F` is a nonarchimedean local field, `K = inertiaFixedField F` its maximal
unramified extension and `O = fixedFieldIntegers F`, with residue field `k`.
`G` is an affine `K`-group and `C` is KP building data for `G` with maximal
split torus `C.S` included by `C.i`. `E` is an unramified zero datum.
`φ : source ⟶ target` is a morphism of relative-component model data over
`O`, `T` an integral torus of `source` with generic fibre `C.S` and split
torus `T.torus`, and `Q` a reductive quotient of the special fibre of
`target.neutral`. `ψ = φ_s ≫ π` is the composite from the special fibre of
`source.neutral` to `Q.quotient`. Its schematic image is
`φ.reductiveImageInclusion Q`.

## Definition

- `RelativeComponentModelHom.nonnegativeQuotientRoots φ C T hT Q v` is the set
  of characters `χ` of the special-fibre torus `T_s` that are roots of
  `φ.quotientTorusInclusion Q T` (the torus `T_s` in `Q.quotient`) and whose
  generic character `(T.characterSpecialization hT).symm χ` is nonnegative on
  the real cocharacter vector `v`. This is the right side of the sign
  formula in `UnramifiedFacetLieWeightSignStatement`. The lemma
  `mem_nonnegativeQuotientRoots` unfolds it (`Iff.rfl`).

## Main results

- `RelativeComponentModelHom.nonzeroLieImageWeights_eq_of_smooth_kernel`: let
  `Ωf ≺ Ωf'` be incident facets of the apartment of `C`, with `Ω ⊆ Ωf` and
  `Ω' ⊆ Ωf'`. Suppose the neutral models of `source` and `target` have
  integral points `E.zeroPoints ⊓ C.pointwiseFixer(Ω')` and
  `E.zeroPoints ⊓ C.pointwiseFixer(Ω)`. Let `Q` be a reductive quotient and
  let `x ∈ Ω` and `v` satisfy `v +ᵥ x ∈ Ω'`. Assume two further hypotheses:
  `UnramifiedRootPositiveReductionStatement` (`hP`), and smoothness of the
  full kernel of `ψ` (`hK`). Then
  `nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q)`
  equals the set of `χ ∈ relativeRoots (φ.quotientTorusInclusion Q T)` with
  `0 ≤ eval C.S ((T.characterSpecialization hT).symm χ) v`.
- `RelativeComponentModelHom.nonzeroLieImageWeights_eq_nonnegativeQuotientRoots`:
  the same equality, with right side `φ.nonnegativeQuotientRoots C T hT Q v`
  and with no extra hypotheses. `hP` is supplied by the Library proof
  `unramifiedRootPositiveReduction`, and `hK` by the Library theorem
  `reductiveComposite_smooth_kernel_of_incidentFacets`.
- `unramifiedFacetLieWeightSign : UnramifiedFacetLieWeightSignStatement.{u}`.
  The statement's model pair `D, D'` corresponds to `target, source`, and its
  torus `A` to `T`. The statement's smoothness hypotheses on the neutral models
  are not used, because `RelativeComponentModelData` already contains smooth
  neutral models.

## Auxiliary lemmas

- `Lie.residue_weightSpace_inf_range_eq_map_weightSpace`: over the residue
  field of a local ring, let `q : G ⟶ H` be a homomorphism of affine groups of
  locally finite type and `i : T ⟶ G` a split torus. Then
  `Lie(H)_χ ⊓ range dq = dq(Lie(G)_χ)` for the torus `i ≫ q`. One inclusion is
  the Library lemma `exists_weightSpace_preimage`. The other is
  `lieKernelHomLinear_mem_weightSpace`.
- `RelativeRoot.weightSpace_le_semigroupWeightSpan_cyclicTail`: `Lie(G)_χ` lies
  in the sum of the weight spaces of the positive multiples of `χ`. This uses
  `actionWeightSpace_conjugation` and the summand for `1 • χ`.
- `nonzeroLieImageWeights_schematicImage_of_smooth_kernel`: over a residue
  field, let `f : H ⟶ G` with `H` smooth and connected and `kernel f` smooth.
  Then the nonzero Lie weights of a torus on the schematic image of `f` are
  the nonzero `χ` whose weight space meets `range df`. This uses the Library
  lemma `Lie.range_schematicImage_inclusion_of_smooth_kernel`.
- `quotientTorusInclusion_eq_comp`: `φ.quotientTorusInclusion Q T` equals
  `T.specialFibreInclusion ≫ ψ` (associativity).
- `mem_relativeRoots_of_characterSpecialization_mem_source` and
  `mem_relativeRoots_of_characterSpecialization_mem_quotient`: if the
  specialization of `a` is a root of `T_s` in the source special fibre, or in
  the reductive quotient, then `a` is a root of `C.S` in `G`. These use
  `IntegralTorusData.mem_relativeRoots_characterSpecialization_iff`, the
  Library lemma `SpecialFibreQuotientData.relativeRoots_subset_specialFibre`
  and `mapIntegralTorus_specialFibreInclusion`.
- `weightSpace_le_range_rootModelMap`: for `a ≠ 0`, the source weight space of
  the specialization of `a` lies in the differential range of the source
  root-model special fibre. The Library lemma `rootModelMap_specialFibre_lie_range`
  identifies that range with the sum of the positive-multiple weight spaces.
- `weightSpace_quotientTorusInclusion_inf_range`: the residue lemma above,
  applied to `ψ` and `T.specialFibreInclusion`.
- `range_rootTargetReductiveQuotientMap`: the range of the differential of
  `φ.rootTargetReductiveQuotientMap T hT Q a ha` (the root model composed with
  `ψ`) is the image under `dψ` of the range of the root-model differential.
- `map_weightSpace_eq_bot_of_eval_neg`: if `eval a v < 0`, then
  `dψ(Lie_s(source)_{a_s}) = 0`. This combines
  `rootTargetReductiveQuotientMap_lie_range_of_eval_neg` (which uses `hP`) with
  the two preceding lemmas. The boundedness of `Ω` comes from
  `C.isBoundedApartmentSubset_of_isFacet`.
- `weightSpace_le_range_of_nonneg`: if `0 ≤ eval a v`, the quotient weight
  space of `a_s` lies in `range dψ`. This combines
  `rootTargetReductiveQuotientMap_lie_range_of_incidentFacets_of_nonneg` with
  `range_rootTargetReductiveQuotientMap` and `LinearMap.map_le_range`.
- `mem_relativeRoots_and_nonneg_of_inf_range_ne_bot` and
  `inf_range_ne_bot_of_mem_relativeRoots_of_nonneg`: the two inclusions of the
  sign formula, one character at a time.

## Proof of the main theorem

By `nonzeroLieImageWeights_schematicImage_of_smooth_kernel` and `hK`, the left
side is the set of nonzero `χ` with `Lie(Q)_χ ⊓ range dψ ≠ ⊥`. Write
`a = (T.characterSpecialization hT).symm χ`.

- Forward. By `weightSpace_quotientTorusInclusion_inf_range`, the condition
  says `dψ(Lie_s(source)_χ) ≠ 0`. So the source weight space is nonzero, and
  `a` is a root of `C.S` by the source root comparison. The quotient weight
  space is nonzero, so `χ` is a quotient root. If `eval a v < 0`, then
  `map_weightSpace_eq_bot_of_eval_neg` would give `dψ(Lie_s(source)_χ) = 0`, a
  contradiction. Hence `0 ≤ eval a v`.
- Backward. If `χ` is a quotient root, then `a` is a root of `C.S` by the
  quotient root comparison. If also `0 ≤ eval a v`, then
  `weightSpace_le_range_of_nonneg` gives `Lie(Q)_χ ≤ range dψ`, so
  `Lie(Q)_χ ⊓ range dψ = Lie(Q)_χ ≠ ⊥`.

The per-character lemmas rewrite along
`AddEquiv.apply_symm_apply` with `congrArg`. They avoid `subst`, which timed out
on the large concrete terms.

## Implementation notes

The module reuses the Library's affineness instances from `FacetLieWeights`
(`neutralSpecialFibre_affine`, `neutralSpecialFibre_isAffine`,
`quotient_isAffine`) as local instances. It also declares private instances
for smoothness, connectedness and finite type of the neutral special fibres,
and affineness of the root-model special fibres. The Lie-algebra module
instance on a schematic image is given with an explicit additive monoid
structure, because the general instance search times out there.

## Provenance

Internal infrastructure for Task 6320 (proof of
`UnramifiedFacetCommonTorusStatement`, Kaletha–Prasad, *Bruhat–Tits theory: a
new approach*, Axiom 4.1.22(3)). It proves the Library statement
`UnramifiedFacetLieWeightSignStatement` (KP Theorem 8.4.19(2)) from Library
results only. The proof route is internal. It follows the structure of KP's
argument: positive roots reduce to the image, negative roots die, and the
smooth kernel identifies the Lie algebra of the image with the differential
image. The definition `nonnegativeQuotientRoots` only names the right side of
that Library statement.
