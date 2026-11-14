# Zero-group fixers depend only on nonnegative affine roots

`Langlands.Geometry.Building.unramifiedZeroFixerAffineRoot` proves the
unchanged Library proposition
`Langlands.Geometry.Building.UnramifiedZeroFixerAffineRootStatement.{u}`
at arbitrary universe `u`, with no additional premise.

For every nonarchimedean local field `F : Type u`, let
`K = inertiaFixedField F` and `G_K = baseChanged F K G`. The theorem keeps
every affine group scheme `G` over `F`, every supplied
`C : MaximalUnramified.BuildingData F G_K`, every
`E : UnramifiedZeroDatum F G_K`, every `g : rationalPoints G_K`, and both
nonempty apartment subsets on which all real affine functions are bounded
above. When the affine roots nonnegative on the two subsets agree, their
pointwise fixers in `E.zeroPoints`, after translation by `g`, agree.

## Implemented proof

The proof uses the following Library theorems:

- `unramifiedSharpFixerRootGeneration`, from
  `UnramifiedSharpFixerRootGenerationProof`, expresses `C.sharpFixer Ω` as
  the supremum of the full affine root groups indexed by all relative
  roots `a` and `ψ ∈ C.affineRoots` with linear part `rootForm C.i a` and
  nonnegative values on `Ω`. These are the ordinary affine roots `Ψ`, and
  multipliable roots and their doubles remain in the index family.
- `unramifiedZeroFixerSharpComparison`, from
  `UnramifiedZeroFixerSharpComparisonProof`, expresses
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)` for nonempty
  bounded `Ω` as the join of the whole-apartment zero fixer with
  `C.sharpFixer Ω`.
- `normal_of_simplyConnectedImage_le`, from
  `ZeroSubgroupCommutatorNormality`, proves normality of a subgroup
  containing the rational-point image of a simply connected derived cover.

First rewrite both sharp fixers with root generation. Their index families
are identical except for the predicate that `ψ` is nonnegative on the
subset. Repeated `iSup_congr`, followed by `iSup_congr_Prop` applied to the
hypothesis on `ψ`, proves equality of the sharp fixers. Apply the comparison
theorem to each subset, using its nonemptiness and boundedness. The
whole-apartment factor is the same in both joins, so this proves equality
of the two zero-group pointwise fixers in the original apartment.

Next `E.isSimplyConnectedDerivedCover` and
`E.simplyConnectedImage_le_zeroPoints` supply the normality theorem's
hypotheses for `E.zeroPoints`. This normality proof uses the actual cover
in `E`; it adds no independence hypothesis and does not change `E`.

Two private group-action lemmas finish the translation. An element `h`
fixes every point of `g • Y` exactly when `g⁻¹ * h * g` fixes every point of
`Y`. For a normal subgroup `H`, membership in `H` is preserved by this
conjugation. Applying these facts to the equality already proved, with
`H = E.zeroPoints`, transports it to the translated apartment subsets.
The final simplification combines set images and unfolds the two existing
pointwise-fixer abbreviations. A private affine-morphism instance supplies
pullback stability for the actual base change `G_K`.

## Provenance

This is an internal composition of the imported results and elementary
group-action transport. The unchanged statement Markdown gives the source
comparison with Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 7.4.1, Lemma 7.4.4(3), Proposition 7.7.5(1) and Lemma 2.6.24,
read with the authors' 2024 corrections. The implemented proof uses the
whole-apartment zero fixer in the comparison theorem, so it needs no
separate identification of that factor with a centralizer subgroup.

The theorem retains all original quantifiers, uses the existing reduced
building and apartment map, and assumes neither existence of the supplied
data nor a local-field structure on `K`. Every imported mathematical input
is supplied by a proof term, with no unproved proposition passed as a
hypothesis of the final theorem.
