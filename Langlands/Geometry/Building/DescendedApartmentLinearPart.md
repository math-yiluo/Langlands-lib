# The linear part of a descended apartment map

Module `Langlands.Geometry.Building.DescendedApartmentLinearPart`.

## Setting

`F` is a nonarchimedean local field and `K = inertiaFixedField F` is its maximal
unramified extension. `G` is an affine group scheme over `F` and
`B : ValuationBuildingData G` is valuation building data over `F`, with maximal split
torus `S = B.S`, inclusion `B.i : S → G` and centralizer datum `B.centralizer`
(`j : Z → G`, `s : S → Z`, `s ≫ j = i`).
`C : MaximalUnramified.BuildingData F G_K` is building data for `G_K` over `K`
(integer-valued valuation building data for the normalized valuation of `K`), with torus
`C.S` and inclusion `C.i`. `f : S_K → C.S` is a homomorphism of group schemes over `K`
from the base change of `S` to `C.S`.

These are the objects of the Library statement
`Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement`. The
factorization `f` with `f ≫ C.i = (B.i)_K` is what the Library statement
`Langlands.Geometry.Building.UnramifiedDescendedApartmentTorusStatement` provides.

`V T = ℝ ⊗[ℤ] X_*(T)` is the real cocharacter space and `TranslationSpace i` is its
quotient by the common kernel `rootAnnihilator i` of the relative roots.

## Content

Scalar extension of points (general fields `F → K`):

- `Gm.affinePointsEquiv_rationalExtend`: the scalar extension to `K` of the rational point
  of `𝔾_{m,F}` with coordinate `t ∈ Fˣ`, read in `𝔾_{m,K}` through the base-change
  isomorphism `Gm.baseChangeIso`, has coordinate the image of `t` in `Kˣ`.
- `rationalExtend_cocharacterPoints`: for a cocharacter `c` of a commutative group scheme
  `S` over `F` and `t ∈ Fˣ`, the scalar extension of the point `c(t) ∈ S(F)` is the point
  `c_K(t) ∈ S_K(K)` of the base-changed cocharacter `c_K` at the image of `t`.

The linear map `f_*`:

- `descendedTorusHom B C f`: `f`, read as a homomorphism of commutative group schemes
  `S_K → C.S` (`Additive.ofMul f`).
- `descendedCocharacterMap B C f : V S →ₗ[ℝ] V C.S`: the composite of the
  isomorphism `V S ≅ V S_K` given by base change of cocharacters of the split torus `S`
  (Library `splitCocharacterBaseChange`) with the map `V S_K → V C.S` given by composition
  with `f` (Library `cocharacterMapReal`). On simple tensors it is
  `r ⊗ c ↦ r ⊗ (c_K ≫ f)` (`descendedCocharacterMap_tmul`, by definition).
- `eval_descendedCocharacterMap`: if `χ` is a character of `C.S` and `ψ` a character of
  `S` with `ψ_K = f ≫ χ`, then `⟨χ, f_* v⟩ = ⟨ψ, v⟩` for all `v ∈ V S`.
- `map_rationalExtend_cocharacterPoints`: `f` sends the scalar extension of `c(t)` to
  the point `(c_K ≫ f)(t)` of `C.S`.

The descended apartment map. Let `e : B.ReducedBuilding → C.ReducedBuilding` satisfy
`e (g • z) = g_K • e z` for `g ∈ G(F)` (hypothesis `he`; `g_K` is
`rationalExtend F K G g`), and let the affine map
`a : B.Apartment →ᵃ[ℝ] C.Apartment` satisfy
`e (B.apartmentMap w) = C.apartmentMap (a w)` (hypothesis `ha`). Let
`f ≫ C.i = (B.i)_K` (hypothesis `hf`). These hypotheses have the same form as hypotheses
of `UnramifiedFacetCommonTorusStatement`, together with the factorization `f`.

- `descendedApartment_map_neg_one_tmul_vadd`: for every cocharacter `c` of `S` and every
  `w`, `a ([(-1) ⊗ c] +ᵥ w) = [f_*((-1) ⊗ c)] +ᵥ a w`.
- `descendedApartment_map_vadd` (main result): for every `v ∈ V S` and every `w`,
  `a ([v] +ᵥ w) = [f_* v] +ᵥ a w`. Equivalently, the linear part of `a` is the map
  `TranslationSpace B.i → TranslationSpace C.i` induced by `f_*`.

## Proofs

`Gm.affinePointsEquiv_rationalExtend`. Rewrite the coordinate of the composite with
`Gm.pointsEquiv_baseChangeIso_hom` and `Gm.baseChangeUnitsEquiv_apply`; the base-changed
point is the point of `𝔾_{m,F}` precomposed with `Spec K → Spec F` (`rationalExtend_fst`),
so by `Gm.pointsEquiv_naturality` its coordinate is the image of `t` under the ring map on
global sections, and `Scheme.ΓSpecIso_naturality` identifies that map with
`algebraMap F K`.

`rationalExtend_cocharacterPoints`. The point `c(t)` is `rationalPoints.map c` of the
`𝔾_m`-point with coordinate `t`. Scalar extension commutes with `rationalPoints.map`
(Library `rationalExtend_map`), the group-scheme map of `c_K` is the base change of that of
`c` composed with the inverse of `Gm.baseChangeIso` (Library
`cocharacterLattice.groupHom_baseChange`), and the previous lemma identifies the extended
`𝔾_m`-point.

`eval_descendedCocharacterMap`. Library lemmas `eval_cocharacterMapReal` (evaluation after
composition with `f` is evaluation of `f ≫ χ`, here `ψ_K`) and
`eval_splitCocharacterBaseChange` (evaluation of `ψ_K` after base change is evaluation of
`ψ`).

`map_rationalExtend_cocharacterPoints`. `rationalExtend_cocharacterPoints` and
functoriality of `rationalPoints.map` (a private lemma
`rationalPoints_map_comp_apply'`).

`descendedApartment_map_neg_one_tmul_vadd`. Let `ϖ` be the Library's order-one
uniformizer unit (`SplitTorusValuation.uniformizerUnit`), `z = s(c(ϖ)) ∈ Z(F)`, and
`z' = s'((c_K ≫ f)(ϖ)) ∈ Z'(K)` the Library's `cocharacterCentralizerPoint` for `C`.

1. The translation of `z` is `(-1) ⊗ c` (private lemma
   `translation_cocharacterPoints_uniformizer`): apply the Library lemma
   `translation_cocharacterCentralizerPoint` to the integer-valued data
   `IntegerValuationBuildingData.ofLocal B`, whose translation is that of `B`
   (`ofLocal_translation`), and use `order_normalized` and `ord ϖ = 1`.
2. The translation of `z'` is `f_*((-1) ⊗ c)` (private lemma
   `translation_descendedCocharacterPoint`): the same Library lemma for `C`, with the
   order on `K` of the image of `ϖ` equal to `1`
   (`MaximalUnramified.order_base_eq_localFieldOrder`), and `descendedCocharacterMap_tmul`.
3. `(j(z))_K = j'(z')` (private lemma `rationalExtend_centralizerPoint`): `j(z)` is the
   image of `c(ϖ)` under `i = s ≫ j`; scalar extension turns it into the image of the
   extended point under `i_K = f ≫ C.i` (`rationalExtend_map`, `hf`);
   `map_rationalExtend_cocharacterPoints` and `C.i = s' ≫ j'` conclude.
4. Since `C.apartmentMap` is injective (Library `maximalUnramifiedApartmentInjective`), it
   suffices to compare images. Then
   `C.apartmentMap (a ([(-1) ⊗ c] +ᵥ w)) = e (B.apartmentMap ([ν(z)] +ᵥ w))`
   `= e (j(z) • B.apartmentMap w)` (Library `centralizer_smul_apartmentMap`)
   `= j(z)_K • e (B.apartmentMap w) = j'(z') • C.apartmentMap (a w)` (`he`, step 3, `ha`)
   `= C.apartmentMap ([ν'(z')] +ᵥ a w)` (`centralizer_smul_apartmentMap` for `C`), and step
   2 identifies `ν'(z')`.

`descendedApartment_map_vadd`. By `AffineMap.map_vadd`, it suffices to show that the two
`ℝ`-linear maps `a.linear ∘ mkQ` and `mkQ ∘ f_*` from `V S` to `TranslationSpace C.i`
agree. Cancelling `a w` in the previous lemma shows that they agree on `(-1) ⊗ c`. The
general case follows by induction on tensors (`TensorProduct.inductionOn`): a simple
tensor is `r ⊗ c = (-r) • ((-1) ⊗ c)`, and both maps are additive and `ℝ`-linear.

## Imports

The module imports the helper module
`Langlands.Geometry.Building.AffineFacetIncidenceTransfer` (submitted together with it),
which this module does not use; the import ensures that the helper is built with it.

## Provenance

Internal infrastructure for the proof of `UnramifiedFacetCommonTorusStatement`
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, Axiom 4.1.22(3), in the setting of
models descended from the maximal unramified extension). The argument is the usual computation of the linear part of
the embedding of apartments under unramified descent: the translation of a point `c(ϖ)` of
the centralizer is `-c`, and `c(ϖ)` maps to `(c_K ≫ f)(ϖ)`. The module uses only Library
definitions and lemmas and makes no further literature assertion.
