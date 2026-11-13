# The distance of two minimal semi-standard parabolics is a Weyl length (Renard VII.3.5, opening paragraph, corrected form): proof

Module `Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthProof`.
Author: Worker 164, under task `bcd5a768-26e2-4fa1-a8f3-4bc6f23a730f`.

`Langlands.GroupScheme.minimalParabolicDistanceLength` proves the published proposition
`MinimalParabolicDistanceLengthStatement.{u}` from
`Rational.MinimalParabolicDistanceLengthStatement`. Its type is exactly that proposition,
with the same universe `u`. It adds no hypothesis. The statement's Lean/Markdown pair and
its imports are unchanged. The proof only combines published, unconditional Library
theorems with the elementary lemmas below, all in the namespace
`Langlands.GroupScheme.MinimalParabolicDistanceLength`.

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the module
with no errors or warnings. For `minimalParabolicDistanceLength` it reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Notation

`k` is a field, `G` a connected reductive group over `k` (`hG`), and
`i : T.toGrp ⟶ G` a maximal split torus (`hi`). `N = normalizerPoints i`,
`Z = centralizerPoints i`, and `W = relativeWeylGroup i = N/Z`. For a cocharacter `ξ`,
`P(ξ)(k)` is `parabolicPoints i ξ`: the carrier, at the identity test object, of
`Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)`. This is the same term as the
statement's local `parabolicPoints ξ`. For `n ∈ N`, `n · ξ` is
`cocharacterAut (normalizingAut i n) ξ`, and `weylAction i n` is the action of `n` on
characters. "`n` moves `P(ν)` to `P(ξ)`" means
`(parabolicPoints i ν).map (MulAut.conj n) = parabolicPoints i ξ`, that is,
`n P(ν)(k) n⁻¹ = P(ξ)(k)`. `⟨α, ξ⟩` is `latticePairing T α ξ`.

## Route

The statement's own sketch uses two facts: the rational points of `P(ξ)` determine
`Σ⁺(ξ)`, and `W` acts simply transitively on chambers. The Lean proof uses neither.
Instead:

- **Existence** comes from the published dominant chamber move. It gives a normalizing
  point that moves `P(ν)` to `P(ξ)` and carries the root signs of `ν` to those of `ξ`.
- **Uniqueness** comes from the published relative Tits system of `ξ`. `P(ξ)(k)` contains
  its Borel subgroup, so `P(ξ)(k)` is self-normalizing, and `P(ξ)(k) ∩ N = Z`.

So every point that moves `P(ν)` to `P(ξ)` has the Weyl class of the chamber move. It
therefore carries the signs as well. The distance then becomes the size of an inversion
set. The Coxeter realization identifies that size with a length.

## Elementary lemmas

- `mem_map_conj`: in any group, `x ∈ H.map (MulAut.conj g)` iff `g⁻¹ x g ∈ H`.
- `neg_iff_of_pos_iff`: two nonzero integers with the same positivity have the same
  negativity.
- `parabolicPoints_map_conj`: `n P(ξ)(k) n⁻¹ = P(n · ξ)(k)`. This applies the published
  `dynamicParabolic_comap_normalizerPoint` to `n⁻¹`. Then the published
  `SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map` turns the comap along the
  inner automorphism into a map under conjugation.
- `weylAction_inv_apply`: `weylAction i n⁻¹ (weylAction i n x) = x`.
- `weylAction_mem_indivisibleRoots_iff`: `weylAction i n α` is an indivisible root iff
  `α` is. It uses the published `weylAction_mapsTo_relativeRoots` and
  `weylAction_mem_roots_iff`, and `weylAction i n⁻¹` to move divisibility back.
- `mem_reducedPositiveRelativeRoots_iff`: a reduced positive root for `ν` is an
  indivisible root with `⟨α, ν⟩ > 0`. This only reorders the two definitions.
- `neg_mem_positiveRelativeRoots_iff`: given root negation, for a root `x`,
  `-x` is positive for `ν` iff `⟨x, ν⟩ < 0`.
- `ncard_eq_relativeInversionSet` (counting lemma): for `a, b ∈ N` and a cocharacter `ν`,
  the set of indivisible `α` with `⟨a⁻¹ α, ν⟩ > 0` and `⟨b⁻¹ α, ν⟩ < 0` is the preimage
  under the bijection `weylAction i a⁻¹` of `relativeInversionSet i ν (mk (b⁻¹ a))`.
  So the two sets have the same `ncard` (`Set.ncard_preimage_of_injective_subset_range`).
  To see the equality, substitute `β = a⁻¹ α`. Then `b⁻¹ α = (b⁻¹ a) β`, using
  `schemeWeylCharacterAction_mk` and the three lemmas above.

## Main lemmas

1. **Uniqueness, `mk_eq_of_map_conj_eq`.** Let `ξ` be generic and let
   `n₁ P(ξ)(k) n₁⁻¹ = n₂ P(ξ)(k) n₂⁻¹`. Then `mk n₁ = mk n₂` in `W`. Put `m = n₂⁻¹ n₁`.
   Apply the hypothesis to `n₁ x n₁⁻¹` and use `mem_map_conj` twice. This shows that `m`
   lies in the normalizer of `P(ξ)(k)`. The published `relativeTitsSystem` gives
   `HasRelativeTitsSystem i ξ`, with Borel subgroup `B = standardParabolicPoints i ξ ∅`. The
   first conjunct of the published `standardParabolicEndpoints` gives
   `standardParabolic i ξ ∅ = Dynamic.parabolic (groupHom ξ ≫ i)`, so `B = P(ξ)(k)`.
   `IsTitsSystem.normalizer_eq_of_le` (subgroups containing `B` are self-normalizing)
   gives `m ∈ P(ξ)(k)`. `HasRelativeTitsSystem.inf_eq` (`B ∩ N = Z`) gives `m ∈ Z`.
   Then `QuotientGroup.eq` gives `mk n₂ = mk n₁`.
2. **Existence by a chamber move, `exists_map_conj_eq`.** For generic `ν`, `ξ` there is
   `n ∈ N` that moves `P(ν)` to `P(ξ)` and satisfies, for every relative root `α`,
   `⟨n⁻¹ α, ν⟩ > 0 ↔ ⟨α, ξ⟩ > 0`. The published `relativeRootSystem` gives
   `HasRelativeRootSystem i`. Its `exists_normalizerPoint_dominant` gives `m ∈ N` with
   `⟨α, m · ξ⟩ ≥ 0` for every positive root `α` of `ν`. By the published
   `latticePairing_cocharacterAut_normalizingAut`, `⟨α, m · ξ⟩ = ⟨m⁻¹ α, ξ⟩`. That is
   nonzero, because `ξ` is generic and `m⁻¹ α` is a root. So `ν` and `m · ξ` have the
   same positive roots. For a root `α` with `⟨α, ν⟩ < 0`, the published
   `relativeRootNegation` puts `-α` among the positive roots of `ν`, which forces
   `⟨α, m · ξ⟩ < 0`. With both cocharacters generic, the first conjunct of the published
   `relativeRootSignInclusions` (inclusion of dynamic parabolics is inclusion of the
   nonnegative roots), used in both directions, gives
   `Dynamic.parabolic (groupHom ν ≫ i) = Dynamic.parabolic (groupHom (m · ξ) ≫ i)`.
   With `parabolicPoints_map_conj`, `m P(ξ)(k) m⁻¹ = P(ν)(k)`. Take `n = m⁻¹`. The sign
   condition is the sign agreement applied to the root `m α`, since `m⁻¹ m α = α`.
3. **Sign transfer, `pos_iff_of_map_conj_eq`.** Every `n` moving `P(ν)` to `P(ξ)`
   (`ν`, `ξ` generic) satisfies `⟨n⁻¹ α, ν⟩ > 0 ↔ ⟨α, ξ⟩ > 0` for every root `α`.
   Let `n₀` be the point of lemma 2. Both move `P(ν)` to `P(ξ)`, so lemma 1 gives
   `mk n = mk n₀`. Hence `weylAction i n⁻¹ = weylAction i n₀⁻¹`, by
   `schemeWeylCharacterAction_mk` and `QuotientGroup.mk_inv`.
4. **The distance as an inversion count,
   `ncard_eq_relativeInversionSet_of_map_conj_eq`.** Let `ν`, `ξ`, `ξ'` be generic, let
   `a` move `P(ν)` to `P(ξ)` and let `b` move `P(ν)` to `P(ξ')`. Then the statement's
   `d ξ ξ'` equals `(relativeInversionSet i ν (mk (b⁻¹ a))).ncard`. `G` is smooth
   (`hG.smooth`), so the published `RelativeRoot.intertwiningRelativeRoots_dynamic`
   rewrites the root set of `d` as the roots `α` with `⟨α, ξ⟩ > 0` and `⟨α, ξ'⟩ < 0`.
   Lemma 3 for `a` turns `⟨α, ξ⟩ > 0` into `⟨a⁻¹ α, ν⟩ > 0`. Lemma 3 for `b`, with
   `neg_iff_of_pos_iff` (both pairings are nonzero by genericity), turns `⟨α, ξ'⟩ < 0`
   into `⟨b⁻¹ α, ν⟩ < 0`. The counting lemma finishes.

## The theorem

After introducing the data, the proof first shows conclusion 3. Let `u = mk a` move `P_ν`
to `P_ξ`, `v = mk b` move `P_ν` to `P_ξ'`, and let `cs` realize the root action for `ν`.
Lemma 4 gives `d ξ ξ' = |relativeInversionSet i ν (mk (b⁻¹ a))|`. The fourth component
of `IsRelativeWeylCoxeterRealization` says `cs.length w = |relativeInversionSet i ν w|`.
Also `mk (b⁻¹ a) = (u⁻¹ v)⁻¹`, and `CoxeterSystem.length_inv` gives
`d ξ ξ' = cs.length (u⁻¹ v)`.

- **Conclusion 1.** Lemma 2 for `(ξ, ξ')` gives some `n`, so `mk n` moves `P_ξ` to
  `P_ξ'`. If `mk m` also does, the two conjugates of `P(ξ)(k)` agree. Lemma 1 then gives
  `mk m = mk n`.
- **Conclusion 2.** `1` moves `P_ξ` to itself, with representative `1`. So conclusion 3
  with `ν = ξ` and `u = 1` gives `d ξ ξ' = cs.length (1⁻¹ w) = cs.length w`.

## Published results used

| Lean name | Use |
| --- | --- |
| `relativeTitsSystem`, `HasRelativeTitsSystem.isTitsSystem`, `HasRelativeTitsSystem.inf_eq` | Tits system of `ξ`; `B ∩ N = Z` |
| `Langlands.Group.IsTitsSystem.normalizer_eq_of_le` | subgroups containing `B` are self-normalizing |
| `standardParabolicEndpoints` (first conjunct) | `P_∅` for `ξ` is `P(ξ)` |
| `relativeRootSystem`, `HasRelativeRootSystem.exists_normalizerPoint_dominant` | chamber move |
| `latticePairing_cocharacterAut_normalizingAut` | `⟨α, n · ξ⟩ = ⟨n⁻¹ α, ξ⟩` |
| `relativeRootNegation` | `-α` is a root |
| `relativeRootSignInclusions` (first conjunct) | equality of dynamic parabolics from root signs |
| `dynamicParabolic_comap_normalizerPoint`, `SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map` | `n P(ξ)(k) n⁻¹ = P(n · ξ)(k)` |
| `RelativeRoot.intertwiningRelativeRoots_dynamic` | the root set of `d` |
| `schemeWeylCharacterAction_mk`, `weylAction_mapsTo_relativeRoots`, `weylAction_mem_roots_iff` | the Weyl action on roots |
| `IsRelativeWeylCoxeterRealization` (length = size of the inversion set), `CoxeterSystem.length_inv` | the length |

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthStatement` | the target statement |
| `Langlands.GroupScheme.Rational.StandardParabolicClassificationProof` | `dynamicParabolic_comap_normalizerPoint` |
| `Langlands.GroupScheme.Rational.ParabolicPointConjugation` | `SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map` |
| `Langlands.GroupScheme.Rational.RelativeTitsSystemProof` | `relativeTitsSystem` |
| `Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof` | `standardParabolicEndpoints` |
| `Langlands.GroupScheme.Rational.RelativeRootNegationProof` | `relativeRootNegation` |
| `Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof` | `relativeRootSignInclusions` |
| `Langlands.GroupScheme.Rational.RelativeRootSystemProof` | `relativeRootSystem` |
| `Langlands.GroupScheme.Rational.DominantChamberMove` | chamber move and pairing transport |
| `Langlands.Group.TitsSystemBruhat` | `IsTitsSystem.normalizer_eq_of_le` |

## Source

The statement is Renard, *Représentations des groupes réductifs p-adiques* (2026),
VII.3.5, opening paragraph (printed p.236 / PDF p.242), in the corrected minimal-Levi form
explained in the statement's Markdown. Renard calls the assertion "bien connu" and gives
no proof. The route above is internal to this Library: it uses the relative Tits system
(Borel–Tits 5.15–5.16, Renard V.4.1) and the dominant chamber move, both already
published.
