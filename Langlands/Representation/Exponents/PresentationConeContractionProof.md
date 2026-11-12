# Uniform contraction of compact subsets of `N(F)` by `C_A^+(ε)`: proof

Author: Worker 74.

Module: `Langlands.Representation.Exponents.PresentationConeContractionProof`.

This module proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.PresentationConeContractionStatement.{u}` as

```text
Langlands.Aubert.General.RepresentedParabolic.presentationConeContraction :
  PresentationConeContractionStatement.{u}
```

The statement is the `N` half of Renard 2026, V.5.2 Théorème (iii), in the neighbourhood form
explained in its own Markdown. The proof adds no hypothesis. The field universe, both
characteristics, the canonical point topology, the arbitrary actual triple `p`, `m`, `n`, the
split component `a` and the compatible presentation `pres` are exactly those of the statement.
Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.

The helper declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic.ConeContraction`. Below, `T`, `i`, `ν`, `J`
and `f` are the presentation data `pres.data.T`, `pres.data.i`, `pres.data.ν`, `pres.data.J`
and `pres.data.f : A ⟶ T`. Write `μ` for the published `pres.splitComponentCocharacter` and
`fμ` for its image `RealTorusSpace.cocharacterMapInt f μ` in `T`. Write `Δ'` for
`simpleRelativeRoots i ν \ J`. Weights are taken for the conjugation action
`AutomorphicAction.conjugation i` of `T` on `G`.

## Idea of the proof

A point `t` of `C_A` is `λ(ϖ)` for a cocharacter `λ` of `A` and the Library's uniformizer `ϖ`.
The condition `t ∈ C_A^+(ε)` makes `⟨f ≫ β, λ⟩` large for every `β ∈ Δ'`. A coordinate of
`G` is a constant plus a finite sum of augmentation eigenfunctions of `T`. Conjugation by `t`
multiplies an eigenfunction of weight `w` by `ϖ^⟨f ≫ w, λ⟩`. The radical `N` is the dynamic
identity-limit subgroup of every standard cocharacter of `T`. Therefore an eigenfunction that
does not vanish at a point of `N(F)` has a weight pairing at least `1` with every standard
cocharacter. Splitting `fλ` as a standard cocharacter plus a large multiple of `fμ` makes the
exponent large, uniformly on the cone. Compactness of `C` bounds the eigenfunction values.

## Points, coordinates and characters (section `Points`, `Characters`)

- `affPt x` is a rational point `x`, precomposed with the Library's
  `Dynamic.GradedCoordinates.toBase` for the test algebra `k`. It is an affine point over
  `Spec k`, the argument type of `Lie.pointCoordinates`.
- `pointCoordinates_affPt_chartCoordinates`: for a global section `b`,
  `Lie.pointCoordinates G (affPt x) (DynamicLie.chartCoordinates G b)` is
  `Dynamic.AffineChart.pointRing x b`. The proof uses
  `DynamicLie.pointRing_eq_pointCoordinates`, `Dynamic.AffineChart.pointRing_comp` and
  `Spec.preimage_map` for the structure map `Spec k ⟶ Spec k`.
- `affPt_mul`, `affPt_inv`, `affPt_one` are the group-object identities. `affPt_conj` says that
  `affPt` of `i(s) * x * i(s)⁻¹` is `(AutomorphicAction.conjugation i).act (affPt s) (affPt x)`
  (`AutomorphicAction.conjugation_act`).
- `characterValue_affPt`: the value `Lie.characterValue w (affPt t)` is the published
  `rationalCharacterEval` of the corresponding rational character at `t`. The proof compares
  the two uses of `Gm.affinePointsEquiv` by `Gm.pointsEquiv_naturality` and
  `Scheme.ΓSpecIso_naturality`. `characterValue_affPt_comp` adds a torus homomorphism `f`, by
  `Lie.characterValue_comp`.

## The radical and standard cocharacters (section `Structure`)

- `groupHom_splitComponentCocharacter_comp`: `groupHom μ ≫ a ≫ l ≫ p` equals
  `groupHom fμ ≫ i`, by the presentation's `factor_comp`.
- `range_radical_eq_unipotent`: for a connected reductive `G`, every `n` with
  `LeviSubgroup.IsGeometricUnipotentRadical n`, and every `ζ` with
  `IsStandardCocharacter i ν J ζ`,
  `SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent (groupHom ζ ≫ i)`, on every test scheme.
  The published `ParabolicRootPresentation.range_comp_radical_eq` identifies the range with the
  dynamic unipotent subgroup of `μ`, hence of `fμ`. The published proof
  `standardCocharacter : StandardCocharacterStatement.{u}` identifies `standardUnipotent i ν J`
  with the dynamic unipotent subgroup of every standard cocharacter. It is applied to `fμ`
  (`isStandard_splitComponentCocharacter`) and to `ζ`.
- `cone K` is the set of cocharacters `c` of `A` with `K ≤ ⟨f ≫ β, c⟩` for all `β ∈ Δ'`;
  `cone_antitone` holds.
- `exists_pairing_bound` gives `D ≥ 1` with `⟨β, fμ⟩ ≤ D` for all `β ∈ Δ'`. It uses finiteness
  of the simple roots (`ParabolicRootPresentation.finite_simpleRoots`).
- `isStandard_sub_smul`: if `c ∈ cone K`, `0 ≤ m` and `m * D + 1 ≤ K`, then
  `cocharacterMapInt f (c - m • μ)` is standard. On `β ∈ J` both pairings vanish, by
  `selectedRoot_restrict_eq_zero` and standardness of `fμ`. On `β ∈ Δ'` the pairing is at least
  `K - m * D ≥ 1`. The restriction identity is `RelativeRoot.latticePairing_restrict_cocharacterMapInt`.

## Topology of the field and of the points

- `tendsto_uniformizer_pow`: `ϖ^n → 0`. The order of `ϖ` is `1`
  (`LocalField.ord_uniformizer`), so its valuation is below `1` (`FML.ord_lt_ord_iff`), and
  Mathlib's `Valued.tendsto_zero_pow_of_v_lt_one` applies, as in the Library's
  `exists_unit_tendsto_pow_zero`.
- `exists_uniformizer_pow_mul_mem`: for compact `K ⊆ F` and a neighbourhood `U` of `0`, there
  is `N` with `ϖ^n * y ∈ U` for all `n ≥ N` and `y ∈ K`. Continuity of multiplication at
  `(0, y)` and Mathlib's `IsCompact.eventually_forall_of_forall_eventually` give a neighbourhood
  `V` of `0` with `V * K ⊆ U`.
- `isInducing_pointRing`: the canonical topology `rationalPointTopology` is induced by
  `x ↦ (b ↦ pointRing x b)`. This composes the published homeomorphisms
  `rationalPointHomeomorph` and `affineSchemePointHomeomorph` with
  `AlgPoint.isEmbedding_evaluation` (`DynamicUnipotentContainment.pointRing_apply`).
- `continuous_pointCoordinates_affPt`: every Lie coordinate of `affPt x` is continuous in `x`,
  by surjectivity of `DynamicLie.chartCoordinates` and
  `DynamicUnipotentContainment.continuous_pointRing_apply`.

## The contraction estimate (section `Contraction`)

- `coneFilter = ⨅ K, 𝓟 (cone K)`. `mem_coneFilter_of_subset` and `exists_cone_subset_of_mem`
  relate its members to cones; the second uses that the cones decrease in `K`.
- `torusPoint c` is the image in `T(F)` of `latticeSection k A c = c(ϖ)`.
  `characterValue_torusPoint`: `Lie.characterValue w (affPt (torusPoint c)) = ϖ ^ ⟨f ≫ w, c⟩`,
  by `CocharacterUniformizer.rationalCharacterEval_cocharacterPoints`.
- `conjCoord g (c, x)` is the Lie coordinate `g` of the conjugate of `affPt x` by
  `affPt (torusPoint c)`. `conjPoint (c, x)` is the conjugate of the rational point `x` by
  `i (torusPoint c)`.
- `one_le_pairing_of_ne_zero`: let `x ∈ pointImage (n ≫ p)` and let `g` be in
  `CoordinateWeights.augmentationWeightSpace (conjugation i) w`. If `g` does not vanish at
  `affPt x`, then `1 ≤ ⟨w, ζ⟩` for every standard `ζ`. Otherwise `affPt x` lies in
  `Dynamic.unipotent (groupHom ζ ≫ i)` by `range_radical_eq_unipotent`, and the published
  criterion `Dynamic.CocharacterWeights.mem_unipotent_iff_weights` (which uses that `T` is
  split) makes `g` vanish there.
- `add_one_le_pairing`: if `c ∈ cone K`, `0 ≤ m`, `m * D + 1 ≤ K` and `w` pairs at least `1`
  with every standard cocharacter, then `m + 1 ≤ ⟨f ≫ w, c⟩`. Apply the hypothesis to the
  standard cocharacters `cocharacterMapInt f (c - m • μ)` and `fμ` and add.
- `tendsto_conjCoord_of_mem`: for compact `C ⊆ pointImage (n ≫ p)` and an augmentation
  eigenfunction `g`, `conjCoord g` tends to `0` along `coneFilter ×ˢ 𝓟 C`. Given a
  neighbourhood `V` of `0`, take `N` from `exists_uniformizer_pow_mul_mem` for the compact image
  of `C` under `x ↦ g(affPt x)`, and take the cone with `K = N * D + 1`. By the eigenfunction
  identity, the value is `ϖ^⟨f ≫ w, c⟩ * g(affPt x)`. It is `0` if `g(affPt x) = 0`. Otherwise
  the exponent is at least `N + 1` by the previous two lemmas.
- `tendsto_conjCoord_augmentation`: the same for every element of the augmentation ideal. The
  published `CoordinateWeights.coordinateWeightDecomposition` (split `T`) gives
  `⨆ w, augmentationWeightSpace (conjugation i) w = ⊤`, and `Submodule.iSup_induction` reduces
  to eigenfunctions, `0` and sums.
- `tendsto_conjPoint`: `conjPoint` tends to `1` along `coneFilter ×ˢ 𝓟 C`. By
  `isInducing_pointRing` it suffices to treat each `pointRing · b`. Write
  `g = chartCoordinates b` as its value `o` at the identity plus the augmentation element
  `g - o`. Then `pointRing (conjPoint z) b = o + conjCoord (g - o) z` (`affPt_conj`), and
  `pointRing 1 b = o` (`Lie.pointCoordinates_one`).

## The main theorem

`presentationConeContraction` introduces the statement's data. The instances
`IsAffineHom`, `IsAffine` and `Smooth` come from `IsConnectedReductive`; the statement's
`RationalPointFamily.pointTopology` is the canonical topology used above. For the given
neighbourhood `L` of `1`, `tendsto_conjPoint` and `exists_cone_subset_of_mem` give `K` such
that `conjPoint (c, x) ∈ L` whenever `c ∈ cone K` and `x ∈ C`. Take `ε = q ^ (-K)`, with `q`
the residue cardinality. A point `t` of `CAepsilon k A Δ ε` is `latticeSection k A c` for some
`c`. For `β ∈ Δ'`, the restriction `f ≫ β` lies in `Δ`, and
`CocharacterUniformizer.characterNorm_latticeSection` gives `q ^ (-⟨f ≫ β, c⟩) < q ^ (-K)`.
Since `q > 1`, `K < ⟨f ≫ β, c⟩`, so `c ∈ cone K`. Finally `factor_comp` identifies
`rationalPoints.map (a ≫ m ≫ p) t` with `i (torusPoint c)`.

## Provenance

The statement is derived from Renard 2026, V.5.2 Théorème (iii) (printed p.123 / PDF p.129),
as recorded in its Markdown. The proof route is internal. It does not follow the source's
appeal to a basis of compact open subgroups with Iwahori decompositions. Instead it combines
published Library results: the root-presentation radical identification, the proved standard
cocharacter statement, the torus-weight criterion for dynamic unipotent subgroups, the
coordinate weight decomposition, the uniformizer evaluation of the lattice section and the
point-topology comparisons.
