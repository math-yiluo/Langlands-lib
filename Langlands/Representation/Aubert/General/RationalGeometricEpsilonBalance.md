# Cancellation of the two original epsilon corrections

Module: `Langlands.Representation.Aubert.General.RationalGeometricEpsilonBalance`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 4021.

This module proves that the two original Haar corrections of the rational
geometric lemma cancel. The corrections are `geometricEpsilonOne` and
`geometricEpsilonTwo` (module `RationalGeometricCorrections`), the source and
target corrections `ε₁`, `ε₂` of BZ77 2.12. Both are characters of the literal
common Levi `Lt = (M_I ∩ n M_J n⁻¹).subgroupOf M_I`. The main theorem
`geometricEpsilon_mul_eq_one` states

`geometricEpsilonOne i ν I J dI dJ n (hU J) (hP I) * geometricEpsilonTwo i ν I J dI dJ n (hU I) (hP J) = 1`.

It holds for all standard subsets `I`, `J`, all actual decompositions
`dI`, `dJ` and every actual torus-normalizer point `n`. No minimality is
required.

## Setting and premises

The field `k` is a nonarchimedean local field. `G(k)` carries the canonical
`pointTopology`, and its local compactness, nonarchimedean group structure and
Hausdorffness are explicit instance hypotheses. The other premises are:

- `StandardCocharacterStatement`, connected reductivity of `G`, the maximal
  split torus `i` with `Mono i.hom.hom.left`, the generic cocharacter `ν`, and
  `HasPointNormalizerComparison i`;
- `HasRelativeRootSystem i`;
- closedness of all standard unipotent, parabolic and Levi subgroups;
- continuity of the two Levi projections.

All of these are premises of the published target
`RationalGeometricK0ExpansionStatement`. In the target, `Mono` comes from
`hi.isSplitSubtorus.mono`. Second countability of `G(k)` is derived internally
from `reductiveRationalPoint_secondCountable`.

## Declarations

- `GeometricCocharacterRealization i ν I J m` records two cocharacters of the
  original torus. The first, `ζ`, realizes the standard Levi and radical of
  `I` as dynamic centralizer and unipotent subgroup. The second, `η`, realizes
  the conjugates by `Int(m)` of the standard Levi and radical of `J`, as
  equalities of subgroup functors. `geometricCocharacterRealization` builds it
  at every actual normalizer point. It uses `StandardCocharacterStatement`,
  the scheme normalizer point given by `HasPointNormalizerComparison`, and
  `groupHom_cocharacterAut_comp`, following the published
  `correctedOrbitCocharacterRealization`.
- The lemmas `levi_left_points`, `unipotent_left_points`,
  `levi_right_points` and `unipotent_right_points` identify the rational points
  of these dynamic subgroups. They are `M_I`, `U_I`, `m M_J m⁻¹` and
  `m U_J m⁻¹`, the last two written as `Subgroup.map (MulAut.conj m)`.
  `map_conj_eq_comap` converts between map and comap forms.
- `exists_common_centralizer_cocharacter` produces a cocharacter `μ` of the
  same torus with

  `Dynamic.centralizer (μ ∘ i) = Dynamic.centralizer (ζ ∘ i) ⊓ Dynamic.centralizer (η ∘ i)`.

  The published `Dynamic.exists_dominant_inclusions` gives `N`. For
  `μ = N • ζ + η`, the point formula `t ↦ ζ(t)^N η(t)` follows from
  `comp_groupHom_add`, `comp_groupHom_zsmul`, `MonObj.mul_comp` and
  `GrpObj.zpow_comp`. Hence `μ ∘ i` equals the published
  `cocharacterCombination`, and `centralizer_combination_eq_inf` applies.
- `characterRestrict_torusFactor_injective` covers every cocharacter `μ` of the
  maximal split torus. It proves that restriction of rational characters from
  the represented centralizer `Dynamic.Affine.centralizerScheme (μ ∘ i)` to its
  torus factor is injective. The published `leviSplitComponentStatement`
  makes the centralizer connected reductive and supplies a split component
  `iM` that factors through the torus, for a split component of `G` given by
  `splitComponentStatement`. The published `centralSplitTorusCharacter`,
  through `characterRestrict_injective_of_centralSplitTorusCharacter`, makes
  restriction to `iM` injective. Cancelling the closed immersion of the
  centralizer gives the factorization of `iM` through the torus factor.
- `correctionProduct_apply_eq` is an algebraic transport lemma. If five
  positive moduli agree pointwise along a map, then the two factorized
  correction products agree there as well.
  `closedNormalizerCharacter_congr'` compares closed Haar normalizer characters
  of equal subgroups at points with the same ambient value.

## Proof of `geometricEpsilon_mul_eq_one`

1. The published `geometricEpsilonOne_eq_factorized_half` and
   `geometricEpsilonTwo_eq_factorized_half` rewrite the two corrections on
   `Lt` as
   `v^{1/2} b^{-1/2} c^{-1/2}` and `u^{1/2} a^{-1/2} c^{-1/2}`. The five moduli
   are the forward Haar characters of:
   - `u`: `U_I`;
   - `v`: `n U_J n⁻¹`;
   - `a`: `U_I ∩ n M_J n⁻¹`;
   - `b`: `M_I ∩ n U_J n⁻¹`;
   - `c`: `U_I ∩ n U_J n⁻¹`.
2. The acting group is `Z = Dynamic.Affine.centralizerScheme (μ ∘ i)`, which
   lies in both centralizers. The five models are the represented groups
   `U(ζ)`, `U(η)`, `U(ζ) ⊓ Z(η)`, `U(η) ⊓ Z(ζ)` and `U(ζ) ⊓ U(η)`, built from
   `Dynamic.Affine.unipotentHom`, `Dynamic.Affine.centralizerHom` and
   `subgroupIntersectionHom`. They have closed-subgroup affineness, finite
   type and `Lie.finiteCoordinates`. Their rational points are the five
   literal subgroups above, and `Z(k) = M_I ∩ n M_J n⁻¹`.
3. The published
   `centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective`
   (module `CommonCentralizerFullHaarBalance`) proves that the corresponding
   product of the five centralizing Haar characters is `1` on `Z(k)`. Its
   inputs are `HasRelativeRootSystem`, splitness of the torus, the torus factor
   `Dynamic.torusFactor` and the injectivity above.
4. The points equivalence of the represented centralizer, followed by the
   point identification and `subgroupOfEquivOfLe`, gives an equivalence
   `Z(k) ≃* Lt` that preserves ambient points. Along it, each centralizing
   Haar character equals the literal `Lt` modulus, by
   `closedNormalizerCharacter_congr'`. `correctionProduct_apply_eq` then turns
   the identity on `Z(k)` into `ε₁ ε₂ = 1` on `Lt`.

## Provenance and dependencies

This is the classical cancellation of BZ77 2.12's correction characters. It
amounts to the identity `δ_{U_I} δ_{nU_Jn⁻¹} = δ_{U_I∩N} δ_{M_I∩V} δ_{U_I∩V}^2` of
moduli on the common Levi. The Lean proof is an internal derivation from the
published declarations named above:

- `RationalGeometricEpsilonFactorization` and
  `RationalGeometricTargetEpsilonFactorization`;
- `CommonCentralizerFullHaarBalance`, with its determinant and Haar
  comparisons;
- `DominantCombinationInclusions` and `CommutingRefinements`;
- `LeviSplitComponentProof`, `SplitComponentProof`,
  `CentralSplitTorusCharacterProof` and `CharacterRestrictionInjective`;
- `RationalPointSecondCountable`.

These proof bodies invoke no geometric-lemma expansion, adjointness, cuspidal
support, character independence or Langlands classification. The imported
module closure is larger.
