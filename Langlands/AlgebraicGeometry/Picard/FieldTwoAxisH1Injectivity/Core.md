# Degree-one Čech cocycles on a product cover over a field

Author: Worker 727.

This module proves the Čech-cochain core of
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`: over a field, a Čech
`1`-cocycle of the structure sheaf of `X ×_R Y` on a product cover whose pullbacks along the two
axes are coboundaries is a coboundary. It is stated in plain ring-presheaf terms and contains
no cohomology. It contains no `sorry` and no new axioms.

## Main result

`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.exists_coboundary_of_axes`.
The setting of `ProductCover` is used: `R : CommRingCat.{u}`, `πX : X ⟶ Spec R`,
`πY : Y ⟶ Spec R`, `hP : IsPullback p₁ p₂ πX πY`, and algebra instances on sections with
`halgX`, `halgY` identifying them with the Library's `secHom`. The further hypotheses are:

- `hR : IsField R`;
- finite index types `I`, `J` and opens `U : I → X.Opens`, `V : J → Y.Opens` with every `U i`,
  `U i ⊓ U k`, `V j`, `V j ⊓ V l` affine (`hU`, `hUU`, `hV`, `hVV`), covering `X` and `Y`
  (`hcovU : ⊤ ≤ iSup U`, `hcovV`);
- every global section of `X` and of `Y` comes from `R`
  (`hglobX : Function.Surjective (secHom πX ⊤).hom`, `hglobY`);
- `R`-points `x₀ : Spec R ⟶ X`, `y₀ : Spec R ⟶ Y` with `x₀ ≫ πX = 𝟙`, `y₀ ≫ πY = 𝟙`, lying in
  `U i₀` and `V j₀` (`hi₀ : ⊤ ≤ x₀ ⁻¹ᵁ U i₀`, `hj₀`);
- axes `i₁ : X ⟶ P` with `i₁ ≫ p₁ = 𝟙 X`, `i₁ ≫ p₂ = πX ≫ y₀`, and `i₂ : Y ⟶ P` with
  `i₂ ≫ p₁ = πY ≫ x₀`, `i₂ ≫ p₂ = 𝟙 Y`;
- `z : ∀ a b : I × J, Γ(P, prodCover p₁ p₂ U V a ⊓ prodCover p₁ p₂ U V b)`, where
  `prodCover p₁ p₂ U V (i, j) = prodOpen p₁ p₂ (U i) (V j) = p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ V j`;
- `hz`: the Čech cocycle condition `z a b|_O + z b c|_O = z a c|_O` on every open `O` below the
  three pairwise intersections;
- `hz₁`: the pullback `i₁^♯ (z a b)` (via `i₁.app`) is a coboundary of sections
  `g a ∈ Γ(X, i₁ ⁻¹ᵁ prodCover a)`; `hz₂`: the same along `i₂`.

The conclusion: there are `y a ∈ Γ(P, prodCover a)` with
`z a b = y b|_{Za ⊓ Zb} - y a|_{Za ⊓ Zb}` for all `a b`.

All restriction maps are written as `(P.presheaf.map (homOfLE h).op).hom`; in the final proof
these hypotheses are obtained from `CechDegreeOne.IsCocycle` and `CechDegreeOne.IsCoboundary`
by definitional unfolding.

## Provenance

This is an internal lemma. It carries out, in degree one and for the structure sheaf, the
argument of Stacks, Varieties, Lemma 0BED (`lemma-kunneth`, `varieties.tex` lines 5441-5630 of
the registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`, Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`): the Čech complex of the product cover is compared
with the tensor product of the Čech complexes of `X` and `Y`, and the Künneth formula over a
field is applied. Instead of the full comparison of complexes, the Lean proof decomposes a
`1`-cocycle into a horizontal and a vertical part and uses only the degree-one lemma
`Langlands.Algebra.TensorDegreeOneKunneth.exists_eq_of_degreeOne`.

## Proof

Write `C₀ = ∏_i Γ(X, U i)`, `C₁ = ∏_{(i,k)} Γ(X, U i ⊓ U k)`, `D₀ = ∏_j Γ(Y, V j)`,
`D₁ = ∏_{(j,l)} Γ(Y, V j ⊓ V l)`, with differentials `dC = cechD πX halgX U` and
`dD = cechD πY halgY V`. Tensor products are over `R`.

1. **Horizontal and vertical parts.** The opens `prodOpen (U i ⊓ U k) (V j)` lie in
   `Z(i,j) ⊓ Z(k,j)`, and `prodOpen (U i) (V j ⊓ V l)` in `Z(i,j) ⊓ Z(i,l)`. Since
   `tensorFam` is bijective for finite families of affine opens (`tensorFam_bijective`), there
   are `h ∈ C₁ ⊗ D₀` and `v ∈ C₀ ⊗ D₁` whose images under `tensorFam` are the restrictions of
   `z (i,j) (k,j)` and of `z (i,j) (i,l)` to these opens.
2. **Mixed condition** `(1 ⊗ dD) h = (dC ⊗ 1) v`. Both sides lie in `C₁ ⊗ D₁`, on which
   `tensorFam` is injective. After `tensorFam`, the components at `((i,k),(j,l))` are, by
   `tensorFam_lTensor_resPi` and `tensorFam_rTensor_resPi`, restrictions of
   `z(i,l)(k,l) - z(i,j)(k,j)` and `z(k,j)(k,l) - z(i,j)(i,l)` to
   `prodOpen (U i ⊓ U k) (V j ⊓ V l)`. They agree by the cocycle condition applied to the
   triples `(i,j),(k,j),(k,l)` and `(i,j),(i,l),(k,l)`.
3. **Axis conditions.** Let `εC = evalSec x₀ ∘ proj i₀ : C₀ → R` and
   `εD = evalSec y₀ ∘ proj j₀ : D₀ → R`. By `appLE_axis₂_tensorFam`, the `(j,l)` component of
   `lid ((εC ⊗ 1) v)` is the pullback along `i₂` of `z (i₀,j) (i₀,l)`, restricted to
   `V j ⊓ V l`. By `hz₂` it equals `β l - β j` with `β j` the restriction of `g (i₀, j)` to
   `V j`, so `lid ((εC ⊗ 1) v) = dD β` lies in the range of `dD`. Symmetrically
   `rid ((1 ⊗ εD) h)` lies in the range of `dC` (`appLE_axis₁_tensorFam`, `hz₁`).
4. **Kernels.** By `exists_eq_smul_one_of_cechD_eq_zero` (with `hcovU`, `hglobX`), every
   element of `ker dC` is a multiple of `1`; likewise for `dD`. Also `dD 1 = 0` (`cechD_one`)
   and `εC 1 = 1 = εD 1`, since `evalSec` is a ring map.
5. **Künneth.** With the field structure `hR.toField` on `R`,
   `TensorDegreeOneKunneth.exists_eq_of_degreeOne` (with `eC = 1`, `eD = 1`) gives
   `w ∈ C₀ ⊗ D₀` with `(dC ⊗ 1) w = h` and `(1 ⊗ dD) w = v`.
6. **The coboundary.** Put `y (i,j) = tensorFam w i j`. Applying `tensorFam` to the two
   equations of step 5 and restricting to `Z(i,j) ⊓ Z(k,l)` gives
   `z(i,j)(k,j)| = y(k,j)| - y(i,j)|` and `z(k,j)(k,l)| = y(k,l)| - y(k,j)|`. The cocycle
   condition for `(i,j),(k,j),(k,l)` on `Z(i,j) ⊓ Z(k,l)` adds them to
   `z(i,j)(k,l) = y(k,l)| - y(i,j)|`. Here `Z(i,j) ⊓ Z(k,l) = prodOpen (U i ⊓ U k)
   (V j ⊓ V l)` (`prodOpen_inf`) lies in both `Z(k,j)` and the opens of step 1.

## Auxiliary results

- `map_map_apply`, `map_self_apply`: composition and identity of restriction maps on elements.
- `map_app_apply`, `appLE_map_apply`: `appLE` as `app` followed by restriction, and
  restriction followed by `appLE` on elements.
- `prodOpen_mono`, `prodOpen_inf`: monotonicity of `prodOpen` and
  `prodOpen U V ⊓ prodOpen U' V' = prodOpen (U ⊓ U') (V ⊓ V')`.
- `prodCover p₁ p₂ U V` (abbreviation): the family `(i, j) ↦ prodOpen p₁ p₂ (U i) (V j)`.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`: `varieties.tex`, Lemma 0BED
(`lemma-kunneth`, lines 5441-5630). The use of the axes follows the proof of Stacks Lemma 0BF3
(`more-morphisms.tex` lines 9634-9650 of the registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`), which deduces injectivity on the two axes
from Künneth and `H⁰(X, 𝒪_X) = K = H⁰(Y, 𝒪_Y)`.
