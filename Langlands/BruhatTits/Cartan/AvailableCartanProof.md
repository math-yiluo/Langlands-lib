# Proof of the corrected KP Theorem 5.2.1 on available Bruhat–Tits data

Module `Langlands.BruhatTits.Cartan.AvailableCartanProof`.

`availableCartan : AvailableCartanStatement.{u}` proves the published target
`Langlands.BruhatTits.Cartan.AvailableCartanStatement` exactly, at an arbitrary
universe `u`. The target is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Theorem 5.2.1 with the corrected (5.2.2), on data satisfying the full
corrected Definition 4.1.26. The statement and its source scope are explained in
`AvailableCartanStatement.md`; this file describes the proof.

The final theorem introduces the field `F`, the group `G` with `hG`, the affine
instance `hG.isAffineHom`, an assignment `𝔅` with `𝔅.IsAvailableFor F G hG`, a
generic `ν` and a special apartment vertex `x`. It applies the datum-level
theorem below to `𝔅.datum F G hG` and the published projection
`IsAvailableFor.groupAxioms`. No other premise is used. In particular neither
`𝔅.IsValid`, nor existence of available data, nor any unproved proposition
target (such as `IwahoriDoubleCosetStatement` or `AvailableIwasawaStatement`)
enters.

## The datum-level theorem

`parahoricCartanConclusions_of_satisfiesGroupAxioms Dt hD ν hν x hx` proves
`ParahoricCartanConclusions Dt.base ν x` for any `Dt : KPBuildingDatum G` with
`hD : Dt.SatisfiesGroupAxioms`. Write `B = Dt.base`, `P_x = B.parahoricAt x`,
`D = parahoricDominantSet B ν`, `j` for the point map of `B.centralizer.j`,
`N(F) = normalizerPoints B.i` and `W = relativeWeylGroup B.i = N(F)/Z(F)`. The
proof uses only these clauses of `hD`:

- Axiom 4.1.1: `building.isBuilding` (common apartments) and
  `building.normalizerApartmentStabilizer` (the stabilizer of `A(S)` is `N(F)`);
- Axiom 4.1.6: `affineRootSystem.apartmentAxioms` and
  `affineRootSystem.compatibleApartmentFacets`;
- Axiom 4.1.8 (2): `rootGroupAction.zeroFixerGenerators`;
- Axiom 4.1.9: `titsSystem`.

The public theorem `parahoricCartanConclusions_of_buildingGeometry` states the same
conclusions directly for `B : ParahoricBuildingData G`. It takes
`B.SatisfiesApartmentAxioms`, `B.HasZeroFixerGenerators`,
`B.HasNormalizerApartmentStabilizer`, injectivity of `B.apartmentMap`, and
`B.HasTitsSystem`, together with the generic cocharacter, special vertex `x`,
and `B.toValuationBuildingData.HasCommonApartmentWith (B.apartmentMap x)`.
These are the precise inputs used below. It requires no `KPBuildingDatum`,
assignment, integral models, or reductive quotients. The group-axioms theorem
is a wrapper that supplies these inputs from the clauses just listed and
`Dt.realization.hasCommonApartmentWith_of_isBuilding`. The original theorem
and `availableCartan` retain their types. This generalization is an internal
refactoring of the proof: it supplies no inheritance or existence theorem for
Levi building geometry.

`parahoricCartanEquiv_of_buildingGeometry` applies the existing
`parahoricDominantDoubleCosetEquiv` to the resulting proved bijectivity. It
therefore constructs the equivalence from the actual dominant centralizer
quotient modulo `Z(F)^0` to the actual `P_x` double cosets, with no separate
bijectivity premise. Its `_class` theorem records by reflexivity that the
class of `z` maps to the double coset of `j(z)`.

Write `ω(z) = centralizerValuation B.centralizer.s B.centralizer.bijective z`.
KP's translation of Axiom 4.1.4 (A 1), written `t` here to avoid a clash
with the cocharacter `ν`, is `t(z) = -ω(z)` (`B.centralizer.translation`), and
`z` acts on the apartment by `x ↦ [t(z)] + x` (published
`IsOmegaCompatible.smul_eq_vadd`). Here `[·]` is the class in
`TranslationSpace B.i = V(S)/V(S)^Φ`.

## Auxiliary lemmas

**Special Weyl representatives** (`special_parahoric_normalizer_surjective`).
If `x` is a special point, every `w ∈ W` has a representative in
`N(F) ∩ P_x`. This lemma and its three helpers are imported from
[the shared special-point Weyl module](../SpecialCompact/WeylRepresentatives.md),
extracted without changing their statements or proofs from the published
`Langlands.BruhatTits.Iwasawa.AvailableProof` (author of that unit: Worker 102).
The proof combines KP Lemma 1.3.42 and Axiom 4.1.6. For each simple root, a
vanishing affine root at `x` gives a reflection representative from the
published rank-one factorization (`rootRankOneFactorization`,
`reflectionElement`). That representative lies in the zero fixer of `{x}`,
hence in `P_x` by Axiom 4.1.8 (2). Its class equals the simple reflection
because the linear reflections coincide (`linear_reflection_eq_of_ker_eq`). The
simple reflections generate `W` by the published `relativeTitsSystem`.

**Conjugating translations** (`translation_conj`, `eval_valuation_conj`). If
`z' = n z n⁻¹` in `N(F)`, then `[t(z')] = n · [t(z)]`. Evaluate the apartment
action of `z'` at one point, using the affine law `n(v + y) = n·v + n y`
(published `KPApartmentData.smul_vadd`). Applying root forms gives
`α(ω(z')) = α(n • ω(z))` for every relative root `α`. `exists_conj_centralizer`
produces such a `z'`, by normality of `Z(F)` in `N(F)` and the published
`exists_toNormalizer_eq_of_mem_centralizerPoints`.

**Parahoric facts.** `parahoricAt_smul_apartmentMap`: `P_x` fixes the image of
`x` (published `parahoricAt_le_compactStabilizer`).
`mem_parahoricAt_of_smul_eq`: an element of `G(F)^0` fixing the image of `x`
lies in `P_x`, by Axiom 4.1.8 (2) (`HasZeroFixerGenerators.zeroFixer_le_parahoric`
for the bounded set `{x}`). `eval_translation` records `α(t(z)) = -α(ω(z))`.

**The dominant chamber.** The helper module `RelativeWeylChamber` proves that
every `W`-orbit in `V(S)` meets the cone where all positive roots of `ν` are
nonnegative, and that two dominant vectors in one orbit are equal. Both proofs
use the published Coxeter realization `relativeWeylCoxeter`.

## (1) Coverage: `Set.univ = P_x · j(D) · P_x`

`exists_parahoric_normalizer_parahoric` proves `G(F) = P_x N(F) P_x`. For `g`,
Axiom 4.1.1 gives an apartment `Y` containing `[x]` and `g[x]`
(the explicit `HasCommonApartmentWith` premise, supplied by
`hasCommonApartmentWith_of_isBuilding` in the group-axioms wrapper). The published
`exists_sharpFixer_smul_apartmentImage` follows from the defining relation of
the building quotient. It gives `p₁ ∈ G(F)^♯_x` with `p₁ Y = A` and, applied to
`g⁻¹ Y ∋ [x]`, `p₂ ∈ G(F)^♯_x` with `p₂ g⁻¹ Y = A`. Then
`(p₁ g p₂⁻¹) A = A`, so `n = p₁ g p₂⁻¹ ∈ N(F)` by the stabilizer clause of
Axiom 4.1.1. Hence `g = p₁⁻¹ n p₂` with `p₁⁻¹, p₂ ∈ G(F)^♯_x ⊆ P_x`.

`exists_dominant_of_normalizer` moves `n ∈ N(F)` into `P_x j(D) P_x`. Choose
`m ∈ N(F) ∩ P_x` with the class of `n`; then `m⁻¹ n = j(z)` for some
`z ∈ Z(F)`. Choose `w ∈ W` with `w • ω(z)` dominant, a representative
`m' ∈ N(F) ∩ P_x` of `w`, and `z_d` with `j(z_d) = m' j(z) m'⁻¹`. The root
values of `ω(z_d)` are those of `m' • ω(z) = w • ω(z)`, so `z_d ∈ D`. Then
`n = (m m'⁻¹) j(z_d) m'`. Combining the two steps gives the first conclusion as
the literal equality of pointwise set products.

## (2) Classification: `P_x j(z) P_x = P_x j(z') P_x ↔ z' z⁻¹ ∈ Z(F)^0`

The converse direction is the published `parahoricDominantRespects`
(`j(Z(F)^0) ≤ P_x`), turned into equality of double-coset sets with
`DoubleCoset.doubleCoset_eq_of_mem`.

For the forward direction, `mem_centralizerZero_of_eq` starts from
`j(z') = a j(z) b` with `a, b ∈ P_x` and `z, z' ∈ D`. It follows KP's proof,
with one step replaced.

1. Let `x' = z' x`. It is special, because `N(F)` preserves the affine roots
   (`range_le_extendedAffineWeylGroup`, `isSpecialPoint_apply_iff`), hence a
   vertex (`isVertex_of_isSpecialPoint`). So `apartmentBuildingFacet x` and
   `apartmentBuildingFacet x'` are the singleton facets `{[x]}` and `{[x']}`.
   Both points lie in `A` and in `aA`, since `a` and `b` fix `[x]` and
   `[x'] = a j(z)[x]`.
2. Axiom 4.1.9 at any chamber gives a Tits system. The published
   `IsBuildingTitsSystem.exists_twoFacet_smul_apartment_eq` then gives
   `k ∈ G(F)^0` stabilizing both singleton facets with `kA = aA`. This
   two-facet transport replaces KP's appeal to Proposition 4.2.24. KP's
   Proposition 1.5.13(1) moves an apartment while fixing the vertices of a
   single facet, whereas here both `[x]` and `[x']` must be fixed. The 2024
   corrections (PDF p.30) accordingly keep only Proposition 4.2.24 at this
   step. The Library lemma is the two-facet transport of KP
   Proposition 1.5.6(5) for the Tits system of Axiom 4.1.9, proved from that
   axiom's facet–parabolic and apartment correspondences. It fixes both
   points.
3. `k` fixes `[x]` and `[x']`, so `k ∈ P_x`. `n₀ = k⁻¹ a` stabilizes `A`,
   so `n₀ ∈ N(F) ∩ P_x`. `j(z')⁻¹ k j(z')` lies in `G(F)^0` (normality,
   `normal_zeroSubgroup`) and fixes `[x]`, so it lies in `P_x`. Hence
   `q = j(z')⁻¹ n₀ j(z) = (j(z')⁻¹ k j(z'))⁻¹ b⁻¹` lies in `N(F) ∩ P_x`, and
   `j(z') = n₀ q⁻¹ · (q j(z) q⁻¹)`. This is KP's `z' ∈ N_x z N_x`.
4. Let `j(z'') = q j(z) q⁻¹` and `z₀ = z' z''⁻¹`, so `j(z₀) = n₀ q⁻¹ ∈ P_x`.
   It fixes `[x]`. Since `j(z₀)[x] = [[t(z₀)] + x]` and the apartment map is
   injective (compatible apartment facets), `[t(z₀)] = 0`. This replaces KP's
   use of Axiom 4.1.2. Consequently `α(ω(z')) = α(q • ω(z))` for every relative
   root `α`.
5. `ω(z)` and `q • ω(z)` are both dominant, the latter because its positive-root
   values are those of `ω(z')`. The fundamental-domain lemma gives
   `q • ω(z) = ω(z)`, so `ω(z')` and `ω(z)` agree on every relative root.
6. Hence `[t(z' z⁻¹)] = 0` and `z' z⁻¹` acts trivially on the apartment
   (`IsOmegaCompatible.normalizerAffineEquiv_eq`). Also
   `j(z' z⁻¹) = a (j(z) b j(z)⁻¹) ∈ G(F)^0 ⊆ G(F)^1`, using `P_x ≤ G(F)^0`
   (`parahoric_le_zeroSubgroup`). The published
   `mem_rationalCommonNormKernel_of_normalizerAffineEquiv_eq_one` gives
   `z' z⁻¹ ∈ Z(F)^1`. KP Corollary 2.6.28, the published
   `ZeroSubgroupDatum.minimalLeviZeroComparison` (`G(F)^0 ∩ Z(F)^1 = Z(F)^0`),
   gives `z' z⁻¹ ∈ Z(F)^0`.

## (3) Bijectivity

The published `RestrictedRightQuotient.doubleCosetMap_bijective` turns coverage
(each `g` has a dominant `z` with `P_x j(z) P_x = P_x g P_x`) and the forward
classification into bijectivity of `parahoricDominantDoubleCosetMap B ν x`. That
map is by definition the quotient map built from `parahoricDominantRespects`.

## Scope

The theorem is conditional on availability for the given `F` and `G`; it
constructs no available data. The proof keeps the actual `P_x`, the corrected
dominant set (5.2.2 with the reversed inequality, positive normalization of
`ω_Z`) and `Z(F)^0`. It does not substitute `K₀` or `Z(F)^1`.
