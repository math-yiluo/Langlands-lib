# Uniform two-sided contraction by `A^+(ε)`: proof

Author: Worker 167.

Module: `Langlands.Representation.Exponents.SplitComponentOppositeContractionProof`.

This module proves the proposition
`Langlands.Aubert.General.RepresentedParabolic.SplitComponentOppositeContractionStatement.{u}`
(module `Langlands.Representation.Exponents.SplitComponentOppositeContractionStatement`) as

```text
Langlands.Aubert.General.RepresentedParabolic.splitComponentOppositeContraction :
  SplitComponentOppositeContractionStatement.{u}
```

The statement is the derived two-sided form of Renard 2026, V.5.2 Théorème (iii), on all of
`A^+(ε)`, as explained in its own Markdown. The proof adds no hypothesis. It keeps the field
universe `u`, both characteristics, the canonical point topology, the actual maps `p`, `m`, `n`,
`pbar`, `mbar`, `nbar`, the split component `a` and the compatible presentation `pres` exactly as
the statement gives them. The hypothesis `IsIso (subgroupMultiplication mbar nbar)` is not
used. The instances `LocallyCompactSpace` and `NonarchimedeanGroup` are only passed on to the
published `presentationConeContraction`, whose statement quantifies over them. Only the axioms
`propext`, `Classical.choice` and `Quot.sound` are used.

The `N` half on the lattice part is the published theorem
`RepresentedParabolic.presentationConeContraction` (module
`Langlands.Representation.Exponents.PresentationConeContractionProof`). This module adds the
`N̄` half on the lattice part, and then extends both halves from `C_A^+(ε)` to `A^+(ε)` by
using the compact common norm kernel of `A(F)`.

The helper declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic.OppositeContraction`. They reuse the published
helpers of namespace `...RepresentedParabolic.ConeContraction`: `cone`, `coneFilter`,
`torusPoint`, `conjCoord`, `conjPoint`, `affPt` and the lemmas named below. As in
`PresentationConeContractionProof.md`, `T`, `i`, `ν`, `J` and `f` stand for `pres.data.T`,
`pres.data.i`, `pres.data.ν`, `pres.data.J` and `pres.data.f : A ⟶ T`. `μ` is
`pres.splitComponentCocharacter`, and `Δ'` is `simpleRelativeRoots i ν \ J`. Weights are for
the conjugation action `AutomorphicAction.conjugation i` of `T` on `G`. Write `ϖ` for the
Library's uniformizer and `q` for the residue cardinality.

## Idea of the proof

For a cocharacter `c` of `A` in a deep cone, conjugation by `torusPoint c = i(f(c(ϖ)))`
multiplies an augmentation eigenfunction of weight `w` by `ϖ^⟨f ≫ w, c⟩`. Conjugation by
`torusPoint (-c)` multiplies it by `ϖ^(-⟨f ≫ w, c⟩)`. For the standard cocharacters `ζ` of the
presentation, `N̄(F)` is the dynamic unipotent subgroup of `-ζ`. So every eigenfunction that
does not vanish at a point of `N̄(F)` has `⟨w, ζ⟩ ≤ -1`. The argument of the published `N` half
then runs with the opposite sign: `-⟨f ≫ w, c⟩` is large uniformly on a deep cone, and
conjugation by `torusPoint (-c)` contracts compact subsets of `N̄(F)`.

To pass from `C_A` to `A(F)`, write `t ∈ A(F)` as `t = s u`. Here `s = c(ϖ)` lies in the lattice
image and `u` lies in the common kernel of all `|χ|_F`, which is compact. Every
`|α(t)|_F` equals `|α(s)|_F`. Conjugation by `u` maps `C` and `C̄` into compact
conjugation hulls `C'` and `C̄'`. These still lie in `N(F)` and `N̄(F)`, because `A` normalizes
both radicals. The lattice estimates for `C'` and `C̄'` therefore give the estimates for `t`.

## Generic filter lemmas (section `Generic`)

These two lemmas restate the last two steps of the published `N`-half argument
(`ConeContraction.tendsto_conjCoord_augmentation`, `ConeContraction.tendsto_conjPoint`) for an
arbitrary filter `F` on `cocharacterLattice A × RationalPoint k G.X`. They are used below with
the filter `coneFilter ×ˢ 𝓟 C̄` mapped through `(c, x) ↦ (-c, x)`.

- `tendsto_conjCoord_augmentation_of_weight`: if `conjCoord g → 0` along `F` for every
  augmentation eigenfunction `g` of every weight `w`, then the same holds for every element of
  the augmentation ideal. The published `CoordinateWeights.coordinateWeightDecomposition` (the
  torus `T` is split) gives `⨆ w, augmentationWeightSpace (conjugation i) w = ⊤`.
  `Submodule.iSup_induction` then reduces the claim to eigenfunctions, `0` and sums.
- `tendsto_conjPoint_of_coord`: if `conjCoord g → 0` along `F` for every augmentation element
  `g`, then `conjPoint → 1` along `F`. The published `isInducing_pointRing` reduces this to each
  coordinate `pointRing · b`. Write `chartCoordinates b` as its value `o` at the identity plus
  an augmentation element. Then `pointRing (conjPoint z) b = o + conjCoord (g - o) z`
  (`affPt_conj`, `pointCoordinates_affPt_chartCoordinates`), and `pointRing 1 b = o`
  (`affPt_one`, `Lie.pointCoordinates_one`).

## The opposite radical (section `Opposite`)

The section's hypotheses are those of the statement on `P̄`: `hG : IsConnectedReductive G`,
`IsParabolicSubgroup pbar`, `IsRationalLeviSubgroup mbar`,
`LeviSubgroup.IsGeometricUnipotentRadical nbar`, `mbar ≫ pbar = m ≫ p` and
`pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`.

- `pointImage_opposite_radical_eq_neg`: for every standard cocharacter `ζ`
  (`IsStandardCocharacter i ν J ζ`), `pointImage (nbar ≫ pbar)` is the set of rational points of
  `Dynamic.unipotent (groupHom (-ζ) ≫ i)`. The published proof
  `standardCocharacter : StandardCocharacterStatement.{u}`, together with the presentation's
  `parabolic_eq` and `levi_eq`, gives `range p = Dynamic.parabolic (groupHom ζ ≫ i)` and
  `range (m ≫ p) = Dynamic.centralizer (groupHom ζ ≫ i)`. The published
  `pointImage_opposite_radical_eq_dynamic` (module
  `Langlands.Representation.Exponents.LeviJacquetContragredientStructure`) takes the published
  proofs `parabolicDynamic` and `oppositeDynamicParabolicUniqueness` as arguments. It identifies
  `N̄(F)` with the rational points of the dynamic unipotent subgroup of the inverse cocharacter.
  `groupHom_neg_comp_eq_oppositeCocharacter` rewrites that inverse as `groupHom (-ζ) ≫ i`.
- `le_neg_one_pairing_of_ne_zero`: let `x ∈ pointImage (nbar ≫ pbar)` and let `g` lie in
  `augmentationWeightSpace (conjugation i) w`. If `g` does not vanish at `affPt x`, then
  `⟨w, ζ⟩ ≤ -1` for every standard `ζ`. Otherwise `⟨w, -ζ⟩ ≤ 0`, and `affPt x` lies in
  `Dynamic.unipotent (groupHom (-ζ) ≫ i)` by the previous lemma. The published criterion
  `Dynamic.CocharacterWeights.mem_unipotent_iff_weights` (split `T`) then makes `g` vanish at
  `affPt x`, a contradiction.
- `add_one_le_neg_pairing`: let `D` bound `⟨β, fμ⟩` for `β ∈ Δ'`. If `c ∈ cone K`, `0 ≤ m`,
  `m * D + 1 ≤ K` and `⟨w, ζ⟩ ≤ -1` for every standard `ζ`, then
  `m + 1 ≤ -⟨f ≫ w, c⟩`. The hypothesis is applied to the standard cocharacters
  `cocharacterMapInt f (c - m • μ)` (published `isStandard_sub_smul`) and `fμ` (published
  `isStandard_splitComponentCocharacter`). The two inequalities are combined by `nlinarith`,
  after the restriction identity `RelativeRoot.latticePairing_restrict_cocharacterMapInt`.
- `tendsto_conjCoord_neg_of_mem`: for compact `C̄ ⊆ pointImage (nbar ≫ pbar)` and an
  augmentation eigenfunction `g` of weight `w`, the function `(c, x) ↦ conjCoord g (-c, x)`
  tends to `0` along `coneFilter ×ˢ 𝓟 C̄`. Given a neighbourhood `V` of `0`, the published
  `exists_uniformizer_pow_mul_mem` gives `N` with `ϖ^j * y ∈ V` for all `j ≥ N` and all `y` in
  the compact image of `C̄` under `x ↦ g(affPt x)`. The published `exists_pairing_bound` gives
  `D`. Take the cone with `K = N * D + 1`. By the eigenfunction identity and the published
  `characterValue_torusPoint`, the value is `ϖ^(-⟨f ≫ w, c⟩) * g(affPt x)`. It is `0` when
  `g(affPt x) = 0`. Otherwise the exponent is a natural number at least `N + 1`, by the
  previous two lemmas.
- `tendsto_conjPoint_neg`: for compact `C̄ ⊆ pointImage (nbar ≫ pbar)`,
  `(c, x) ↦ conjPoint (-c, x)` tends to `1` along `coneFilter ×ˢ 𝓟 C̄`. This combines the two
  generic lemmas, applied to the image filter, with `tendsto_conjCoord_neg_of_mem`. Explicitly,
  `conjPoint (-c, x) = i(torusPoint (-c)) * x * i(torusPoint (-c))⁻¹`.

## The main theorem

`splitComponentOppositeContraction` introduces the statement's data. The introduction skips the
statement's local topology, so the proof re-installs `RationalPointFamily.pointTopology` on
`rationalPoints G`. It derives the instances `IsAffineHom`, `IsAffine` and `Smooth` for `G`
from `IsConnectedReductive`. It also derives that `A` is a split torus from the presentation's
`IsSplitComponent`, and puts the canonical topology on `A(F)`.

1. *Norm kernel and hulls.* `Ker` is `Plancherel.rationalCommonNormKernel A.toGrp`. It is
   compact by `Plancherel.SplitTorus.isCompact_commonNormKernel`. Put
   `C' = {incG u * c * (incG u)⁻¹ | u ∈ Ker, c ∈ C}` and
   `C̄' = {(incG u)⁻¹ * c * incG u | u ∈ Ker, c ∈ C̄}`. Both are compact: they are images of
   `Ker × C` and `Ker × C̄` under continuous maps, and `incG` is continuous by
   `continuous_rationalPointMap`. Every `incG u` lies in `pointImage p` and, by
   `mbar ≫ pbar = m ≫ p`, in `pointImage pbar`. The published `pointImage_le_normalizer_radical`
   (module `Langlands.Representation.Exponents.ArbitraryParabolicInduction`) then gives
   `C' ⊆ pointImage (n ≫ p)` and `C̄' ⊆ pointImage (nbar ≫ pbar)`.
2. *The two lattice estimates.* The published `presentationConeContraction`, applied to `C'`
   and `L`, gives `ε₁ > 0` with `incG s * y * (incG s)⁻¹ ∈ L` for all
   `s ∈ CAepsilon k A Δ ε₁` and `y ∈ C'`. `tendsto_conjPoint_neg` for `C̄'`, read through the
   published `exists_cone_subset_of_mem`, gives `K` with `conjPoint (-c, y) ∈ L` for all
   `c ∈ cone K` and `y ∈ C̄'`.
3. *Choice of `ε`.* Take `ε = min ε₁ (q ^ (-K))`, which is positive because `q > 1`
   (`LocalField.residueCardinality_gt_one`).
4. *Decomposition of `t`.* Let `t` satisfy `characterNorm k A α t < ε` for all `α ∈ Δ`. The
   third clause of the published `CocharacterUniformizer.isUniformizerLatticeSection` (for the
   split torus `A`) gives `x` with `u := t * s⁻¹ ∈ Ker`, where `s = latticeSection k A x`.
   Since `A(F)` is commutative, `t = s * u = u * s`. Every rational norm character is trivial
   on `u`, so `characterNorm k A α t = characterNorm k A α s` for every `α`.
5. *`N` half.* `s` lies in `CAepsilon k A Δ ε₁`. For `c ∈ C`, the point
   `incG u * c * (incG u)⁻¹` lies in `C'`, and
   `incG t * c * (incG t)⁻¹ = incG s * (incG u * c * (incG u)⁻¹) * (incG s)⁻¹`. Step 2
   applies.
6. *`N̄` half.* For `β ∈ Δ'`, `f ≫ β ∈ Δ`. The published
   `CocharacterUniformizer.characterNorm_latticeSection` gives
   `q ^ (-⟨f ≫ β, x⟩) = characterNorm k A (f ≫ β) s < q ^ (-K)`, so `K < ⟨f ≫ β, x⟩` and
   `x ∈ cone K`. The presentation's `factor_comp` identifies `i(torusPoint (-x))` with
   `(incG s)⁻¹`. For `c ∈ C̄`, the point `(incG u)⁻¹ * c * incG u` lies in `C̄'`, and
   `(incG t)⁻¹ * c * incG t = (incG s)⁻¹ * ((incG u)⁻¹ * c * incG u) * incG s`, which is
   `conjPoint (-x, (incG u)⁻¹ * c * incG u)`. Step 2 applies.

## Provenance

The statement is derived from Renard 2026, V.5.2 Théorème (iii) (printed p.123 / PDF p.129),
as used in the proof of Remarque 3 of VI.9.1 (printed p.198 / PDF p.204). Its Markdown records
the details. The proof route is internal. It does not follow the source's appeal to a basis of
compact open subgroups with Iwahori decompositions. The `N̄` half adapts the published proof of
the `N` half (Worker 74's `PresentationConeContractionProof`) by reversing signs. The extension
from `C_A^+(ε)` to `A^+(ε)` is the decomposition `A(F) = C_A · A(F)⁰` (Renard V.2.5), with
`A(F)⁰` compact, which the statement Markdown names as a proof obligation. It is implemented
with the published uniformizer lattice section and the compactness of the common norm kernel.
