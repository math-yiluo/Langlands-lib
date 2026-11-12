# The adelic modulus `δ_P` of a parabolic, and Haar probability on compact subgroups

Author: Worker 3659.

This module constructs two measure-theoretic objects that the global
theory of parabolic induction and Eisenstein series uses on actual adelic
points. Both are needed by Mœglin–Waldspurger I.1.13 and its integration
formula.

1. The modulus `δ_P` of a parabolic `P = M U` of `G`, a homomorphism
   `P(𝔸_F) → ℝ_{>0}`.
2. The Haar probability measure `dk` on a compact subgroup `K` of
   `G(𝔸_F)`.

Two statement modules use these objects.
`AdelicParabolicModulusStatement.lean` compares `δ_P` with the idele norm
of `det(Ad | Lie U)` and with Mathlib's modular character of `P(𝔸_F)`.
`AdelicIwasawaIntegrationStatement.lean` states the Iwasawa integration
formula.

Throughout, `F` is a number field, `G` is a group scheme over `Spec F`
with `IsAffine G.X.left`, and `AdelicGroupPoints F H` is the published
adelic point group of a group scheme `H`. It carries its published
evaluation topology and the Borel σ-algebra of `AdelicGroupHaarMeasure`.
`map F H G f` is the published continuous homomorphism induced by
`f : H ⟶ G`.

## Closed images

- `isClosed_range_map_of_isClosedSubgroup`: if `f : H ⟶ G` is a closed
  subgroup (`IsClosedSubgroup f`), the image of `H(𝔸_F)` is closed in
  `G(𝔸_F)`. The proof uses the published `isClosedEmbedding_map`.
- `isAffine_left_of_isClosedSubgroup`: the source of such an `f` is
  affine.
- `rangeEquiv F f hf`: if `map F H G f` is a topological embedding, this
  is the topological group isomorphism from `H(𝔸_F)` onto its image. It
  is `MonoidHom.ofInjective`, with continuity of the inverse taken from
  the embedding. `rangeEquiv_apply_coe` and `map_rangeEquiv_symm` are the
  two evaluation rules.

## The image modulus

Let `iP : P ⟶ G` and `iU : U ⟶ G` be homomorphisms, with
`LocallyOfFiniteType G.X.hom`. Suppose that the image of `U(𝔸_F)` is
closed (`hcl`) and that each `map F P G iP p` normalizes it (`hn`). Then
`imageModulus F iP iU hcl hn : P(𝔸_F) →* ℝ≥0ˣ` is the published
closed-subgroup Haar character `HaarModulus.closedNormalizerCharacter`
of the image of `U(𝔸_F)`, composed with
`p ↦ ⟨map F P G iP p, hn p⟩` (`MonoidHom.codRestrict`).

By the definition of `HaarModulus.normalizerCharacter`, its value at `p`
is `mulEquivHaarChar` of conjugation `u ↦ g u g⁻¹`, where `g` is the
image of `p`. In terms of sets this is `μ(g E g⁻¹) = δ(p) μ(E)` for every
Haar measure `μ` on the image of `U(𝔸_F)`. It is the factor
`|det(Ad(p) | Lie U)|`, with no inverse.

`integral_conj_imageModulus` gives the same factor in the form used for
integration over `U(𝔸_F)` itself. Assume `IsAffine U.X.left`,
`LocallyOfFiniteType U.X.hom` and that `map F U G iU` is an embedding.
Then, for every Haar measure `m` on `U(𝔸_F)` with `m.Regular` and every
function `f : G(𝔸_F) → E` into a real normed space,

`∫ f(g⁻¹ · u · g) dm(u) = δ(p) · ∫ f(u) dm(u)`, where `g = map F P G iP p`
and `u` stands for `map F U G iU u`.

The proof transports conjugation from the image back to `U(𝔸_F)` along
`rangeEquiv`. The published `Aubert.General.mulEquivHaarChar_trans_symm`
shows that the Haar scaling factor is unchanged. Mathlib's
`mulEquivHaarChar_smul_eq_comap` then gives the integral identity.

## The dynamic parabolic

Fix a cocharacter `χ : 𝔾_m ⟶ G` and group schemes representing the
published dynamic subgroup functors:

- `hP : (Dynamic.parabolic χ).IsRepresentedBy iP` for `P = P_G(χ)`;
- `hU : (Dynamic.unipotent χ).IsRepresentedBy iU` for its unipotent
  radical `U = U_G(χ)`;
- `hM : (Dynamic.centralizer χ).IsRepresentedBy iM` for the Levi factor
  `M = Z_G(χ)`, where needed.

For connected reductive `G`, `U_G(χ)` is the unipotent radical of
`P_G(χ)` and `Z_G(χ)` is a Levi subgroup. Over an algebraically closed
field, the subgroups `P_G(λ)` are exactly the parabolic subgroups
(Conrad 2014, Example 4.1.9, which refers to Conrad–Gabber–Prasad for the
proof). The analogous description of parabolic `F`-subgroups by
`F`-cocharacters is the reason the dynamic data are used here. It is
neither proved nor used in this module.

The published `Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_*`
makes each representing inclusion a closed subgroup. This gives:

- `isClosed_range_map_unipotent`: `U(𝔸_F)` is closed in `G(𝔸_F)`.
- `isClosedEmbedding_map_unipotent`: `U(𝔸_F) → G(𝔸_F)` is a closed
  embedding.
- `isAffine_parabolic`, `isAffine_unipotent`, `isAffine_centralizer`,
  `locallyOfFiniteType_parabolic`, `locallyOfFiniteType_unipotent` and
  `locallyOfFiniteType_centralizer`: the representing schemes are affine
  and locally of finite type. This makes their adelic points locally
  compact by the published instances.
- `map_parabolic_mem_normalizer`: `P(𝔸_F)` normalizes `U(𝔸_F)` inside
  `G(𝔸_F)`. This is the published
  `Dynamic.range_unipotent_isNormalizedBy_range_parabolic` at the adelic
  test object.

The main definitions and results of this section:

- **`parabolicModulus F hP hU : P(𝔸_F) →* ℝ≥0ˣ`** is `δ_P`, the
  `imageModulus` of these data.
- `parabolicModulus_apply` unfolds it.
- `integral_conj_parabolicModulus` is the integral identity above for
  `δ_P`: `∫ f(p⁻¹ u p) du = δ_P(p) ∫ f(u) du` on `U(𝔸_F)`.

For `m ∈ M(𝔸_F)` this is the modulus `δ_P(m) = m^{2ρ_P}` of
Mœglin–Waldspurger I.1.13. MW write `m^{-2ρ_P}` for its inverse in the
integration formula. Getz–Hahn (8.1) gives the local analogue
`δ_P(p) = |det(Ad(p) : Lie P → Lie P)|`. For reductive `M` this is
`|det(Ad(p) | Lie U)|`, because `det(Ad | Lie M)` is trivial on `M`.

Two conditional consequences are proved:

- `parabolicModulus_rational_of_eq`: suppose that `δ_P` equals
  `characterNorm F P δ` for some algebraic character `δ` of `P`. Then the
  published product formula `characterNorm_rational` makes `δ_P` trivial
  on the principal points `P(F)`.
- `continuous_parabolicModulus_of_eq`: under the same hypothesis, `δ_P`
  is continuous.

`AdelicParabolicModulusStatement` asserts that this hypothesis holds,
with `δ = det(Ad | Lie U)`. Neither consequence assumes that statement.

## Haar probability on compact subgroups

Assume `LocallyOfFiniteType G.X.hom`. Let `K` be a subgroup of `G(𝔸_F)`
with `IsCompact (K : Set _)`. Then `compactHaarProbability F G K hK` is
Mathlib's `Measure.haarMeasure ⊤` on the compact group `K`, normalized by
`meas(K) = 1`. The measurable structure on `K` is the subspace one, which
is Borel. The module proves:

- `compactHaarProbability_isHaarMeasure`: it is a left Haar measure.
- `compactHaarProbability_isProbabilityMeasure`: it is a probability
  measure, by `haarMeasure_self`.
- `eq_compactHaarProbability`: every left Haar probability measure on `K`
  equals it. The proof uses Haar uniqueness
  (`isMulLeftInvariant_eq_smul_of_innerRegular`) and evaluation on
  `univ`.

This is the measure `dk` with `meas(K) = 1` in Mœglin–Waldspurger I.1.13.
Mœglin–Waldspurger take `K` maximal compact. Here `K` is any compact
subgroup.

## What is not claimed

- No identification of `δ_P` with `|det(Ad | Lie U)|` or with the modular
  character of `P(𝔸_F)`. These are `AdelicParabolicModulusStatement`.
- No continuity of `δ_P` without that comparison.
- No integration formula on `G(𝔸_F)`. That is
  `AdelicIwasawaIntegrationStatement`.
- No right invariance of `compactHaarProbability`, and no existence of a
  compact `K` with `P(𝔸_F) K = G(𝔸_F)`.

## Sources

- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
  (`moeglin-waldspurger-1995-spectral-decomposition`), chapter file
  `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, I.1.13, printed
  p. 18 (PDF p. 18). It covers the Haar measure on `K` with
  `meas(K) = 1`, the factor `m^{-2ρ_P}` and the integration formula over
  `U(𝔸) × M × K`.
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024)
  (`getz-hahn-2024-automorphic-representations`):
  - §3.2, (3.6)–(3.8), printed p. 82 (PDF p. 98): the modular
    quasi-character convention. It agrees with Mathlib's
    `Measure.modularCharacter`.
  - Proposition 3.6.1, printed p. 88 (PDF p. 104): the local modulus as
    `|det Ad|`.
  - (8.1), printed p. 213 (PDF p. 226): `δ_P(p) = |det(Ad(p) : p → p)|`.
- Conrad, *Reductive group schemes* (2014)
  (`conrad-2014-reductive-group-schemes`), Example 4.1.9, printed p. 114
  (PDF p. 114). It describes the parabolics `P_G(λ)`, the unipotent
  radicals `U_G(λ)` and the Levi subgroups `Z_G(λ)`. Context only.
