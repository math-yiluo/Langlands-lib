# `Ξ` through a standard Levi subgroup on actual rational points (Lemma II.1.6)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLevi`,
namespace `Langlands.HarishChandraSchwartz`.

Take a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter, a compact open subgroup `K` of `G(F)` with `G(F) = P₀(F) K`, and an actual
standard parabolic subgroup `P_J = M_J U_J ⊇ P₀`. For these data the module

- proves that `δ₀` is trivial on `U₀(F)` with no structural hypothesis;
- assembles the Library's abstract `LeviData` for `(K, P₀(F), P_J(F), M_J(F))`;
- defines Waldspurger's `Ξ^M` for `M = M_J` (`rationalLeviXi`, the recorded declaration);
- proves Lemma II.1.6 on actual points:
  `Ξ(g) = ∫_K δ_{U_J}(m_P(kg))^{1/2} Ξ^{M_J}(m_P(kg)) dk`.

The only hypothesis beyond the group-theoretic data is the Iwasawa decomposition
`M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. The module also derives this decomposition from Renard's
`K ∩ P = (K ∩ M)(K ∩ U)`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
pages; the PDF page is the printed page minus 234. The author checked the quotations below on the
text of PDF pages 6, 18 and 19.

- I.1, printed p. 240: "Soit `P = MU` un sous-groupe parabolique semi-standard de `G`. Alors
  `G = PK` et le groupe `M ∩ K` vérifie relativement à `M` les mêmes propriétés que `K`
  relativement à `G`. Pour tout `g ∈ G`, on choisit `u_P(g) ∈ U`, `m_P(g) ∈ M` et `k_P(g) ∈ K` de
  sorte que `g = u_P(g) m_P(g) k_P(g)`." Also on p. 240: `δ_H` "est le module du groupe `H`".
- II.1, printed p. 252: "Soit `P = MU` un sous-groupe parabolique semi-standard de `G`. On définit
  une fonction `Ξ^M` sur `M` comme on vient de définir `Ξ` sur `G`."
- Lemme II.1.6, printed p. 252: "Pour tout `g ∈ G`, on a l'égalité
  `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`."
- Proof, printed p. 253: "Quitte à changer `P_0`, on peut supposer `P ⊃ P_0`. … Identifions `V` à
  `I_P^G V^M`. … `⟨e(kg), e(k)⟩ = δ_P(m_P(kg))^{1/2} ⟨π^M(m_P(kg)) e^M, e^M⟩ =
  δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg))`."
- II.2 (1), printed p. 253: "`δ_P^{alg}(m)` est le déterminant de `Ad(m)` dans l'algèbre de Lie de
  `U` (on a `δ_P(m) = |δ_P^{alg}(m)|_F`)".

The module treats the case `P ⊃ P₀` to which the source's proof reduces, for standard parabolic
subgroups `P_J`, `J ⊆ Δ`.

## Setting

- `F` is a nonarchimedean local field of any characteristic.
- `G` is a group scheme over `Spec F` with `[IsAffineHom G.X.hom]` and
  `[LocallyOfFiniteType G.X.hom]`, and `hG : IsConnectedReductive G`.
- `i : S → G` is a maximal split torus (`hi`), `ν` a generic cocharacter (`hν`) and
  `J ⊆ simpleRelativeRoots i ν` (`hJ`).
- `G(F) = rationalPoints G` carries the canonical topology, through the local instances of
  `RationalWeights`, `rationalPoint_secondCountableTopology` and
  `Plancherel.rationalPoints_nonarchimedeanGroup`.
- `P_J(F)`, `M_J(F)`, `U_J(F)` are `standardParabolicPoints`, `standardLeviPoints`,
  `standardUnipotentPoints`, with `P₀ = P_∅` and `U₀ = U_∅`.
- `δ₀ = rationalMinimalModulus i ν` and `Ξ = rationalXi` are the published definitions of
  `RationalWeights`.
- `δ_{U_J} = standardUnipotentModulus` and `δ₀^{M_J} = standardLeviMinimalModulus` are the
  published definitions of `RationalModulusFactorization`.

## Contents

### Abstract lemmas

These two lemmas concern a group `H` with subgroups `K, P₀, P, M, U`, where `P = M ⋉ U` is given by
the Library's `Aubert.General.IsSemidirectDecomposition`.

- `leviData_of_isSemidirectDecomposition h hP₀ hUP₀ hδ₀U hδ₀M hδP` builds `LeviData` (the data of
  the Library's `SphericalLevi`, with Levi projection `h.projection`) from these hypotheses:
  `P₀ ≤ P`; `U ≤ P₀`; `δ₀ = 1` on `U`; `δ₀ = δ_P δ₀^M` on `P₀ ∩ M`; and `δ_P = 1` on `K ∩ M`. Two
  clauses of `LeviData` come from the projection: the kernel of `m_P` is `U`
  (`projection_eq_one_iff`), and `m_P` is the identity on `M` (`projection_levi`).
- `isIwasawaPair_of_isSemidirectDecomposition h hP₀ hUP₀ hP₀K hmK` proves
  `M = (P₀ ∩ M)(K ∩ M)` from two hypotheses: `G = P₀ K`, and the projection maps `P ∩ K` into `K`.
  The proof is the Library's `LeviData.isIwasawaPair` for trivial characters. The projection maps
  `P₀` into `P₀` because `m_P(p) = p (m_P(p)⁻¹ p)⁻¹` and `m_P(p)⁻¹ p ∈ U ⊆ P₀`.

### `δ₀` on `U₀(F)` (section `Unipotent`)

- `closedNormalizerCharacter_eq_one_of_eq` transports the unimodularity of a closed subgroup along
  an equality of subgroups.
- **`rationalMinimalModulus_eq_one_of_mem_standardUnipotent hG hi hν p hp`**: `δ₀(p) = 1` for
  `p ∈ U₀(F)`.
  - Proof: by the proved `standardCocharacter` for `J = ∅` (with `ν` itself as standard
    cocharacter), `U₀(F)` is the actual dynamic radical of `ν`. That radical is unimodular by the
    Library's proved `DynamicNormalization.dynamicUnipotent_isUnimodular` (limit of compact
    subgroups).
  - The Library's `rationalMinimalModulus_eq_one_of_mem_unipotent` (`RationalXiLowerBound`)
    proves the same identity, but assumes a compatible split component for `J = ∅`. The version
    here assumes only that `G` is connected reductive.

### Levi data and `Ξ^{M_J}` (section `Levi`)

- `standardUnipotentModulus_eq_one i ν J hKo hKc m hm`: `δ_{U_J}(m) = 1` for `m ∈ M_J(F) ∩ K` and
  every compact open subgroup `K`. Conjugation by `m` preserves the compact open subgroup
  `K ∩ U_J(F)` of `U_J(F)`, so the Library's `HaarModulus.normalizerCharacter_eq_one_of_preimage`
  applies.
- `standardLeviMinimalModulusOf i ν J`: `δ₀^{M_J}` (`standardLeviMinimalModulus`, defined on the
  subgroup `P₀(F) ⊓ M_J(F)` of `G(F)`), viewed on the subgroup `P₀(F).subgroupOf M_J(F)` of
  `M_J(F)`. `standardLeviMinimalModulusOf_apply` is its defining equation.
- **`rationalLeviData hG hi hν hJ hKo hKc`** is `LeviData K P₀(F) P_J(F) M_J(F) δ₀ δ_{U_J}
  δ₀^{M_J} m_P`, where `m_P` is the projection of `isSemidirectDecomposition_standard`. It applies
  `leviData_of_isSemidirectDecomposition` with these inputs:
  - `P₀(F) ⊆ P_J(F)` (`standardParabolicPoints_empty_le`);
  - `U_J(F) ⊆ U₀(F) ⊆ P₀(F)` (`standardUnipotentPoints_le_empty_of_subset`);
  - `δ₀ = 1` on `U_J(F)`, by the previous section;
  - `δ₀ = δ_{U_J} δ₀^{M_J}` on `P₀(F) ∩ M_J(F)` (published `rationalMinimalModulus_eq_mul`);
  - `δ_{U_J} = 1` on `M_J(F) ∩ K`.
- `compactSpace_subgroupOf_standardLevi`: `K ∩ M_J(F)` is compact (`M_J(F)` is closed).
- **`rationalLeviXi hKc hM m`** (definition, the recorded declaration): Waldspurger's `Ξ^M` for
  `M = M_J`. It is the Library's generic spherical function `xi` of the group `M_J(F)`, built from
  three pieces:
  - its minimal parabolic `P₀(F) ∩ M_J(F)`;
  - the compact subgroup `K ∩ M_J(F)`;
  - the modulus `δ₀^{M_J}`.

  Here `hM` is the Iwasawa decomposition `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`. Explicitly,
  `Ξ^{M_J}(m) = ∫_{K ∩ M_J(F)} δ₀^{M_J}(p(k m))^{1/2} dk`, where `p(x) ∈ P₀(F) ∩ M_J(F)` comes
  from a factorization `x = p(x) k'` with `k' ∈ K ∩ M_J(F)`, and `dk` is the Haar probability
  measure. This is exactly how the published `rationalXi` defines `Ξ` on `G` (Waldspurger's
  "comme on vient de définir `Ξ` sur `G`"), with `(G, P₀, K, δ₀)` replaced by
  `(M_J, P₀ ∩ M_J, K ∩ M_J, δ₀^{M_J})`.
- `isIwasawaPair_standardLevi hG hi hν hJ hPK hmK` gives the hypothesis `hM` whenever
  `G(F) = P₀(F) K` and the Levi projection maps `P_J(F) ∩ K` into `K`. The latter holds when
  `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)`, which is the third clause of Renard V.5.1 (row S19 of the
  Library's `notes/renard/chapter-v-structural-inputs.md`). The fifth clause of S19 ("the
  corresponding properties inside every standard Levi") gives `hM` directly.
- **`rationalXi_eq_integral_rationalLeviXi hG hi hν hJ hKo hKc hPK hM g`** (Lemme II.1.6) states,
  for every `g ∈ G(F)`,
  `rationalXi hKc hPK g = ∫ k : K, √(δ_{U_J}(m_P(k g))) · rationalLeviXi hKc hM (m_P(k g))
  ∂(normalizedHaar K)`.
  - `m_P(x) = leviComponent … x` is the projection to `M_J(F)` of the `P_J(F)`-component of a
    chosen factorization `x = p k'` with `p ∈ P_J(F)`, `k' ∈ K`, i.e. Waldspurger's `m_P(x)`.
  - Proof: the Library's generic `LeviData.xi_eq_integral` for `rationalLeviData`, with `δ₀ = 1`
    on `P₀(F) ∩ K` (published `rationalMinimalModulus_eq_one`).
  - The Library's proof is the analytic one: a Fubini argument over `(K ∩ M) × K` with the
    pointwise identity `LeviData.iwasawaWeight_mul`. It is not the source's identification
    `V ≃ I_P^G V^M`. The resulting identity is the same.

## Relation to the source and scope

- **Moduli.** The Library's `δ₀`, `δ₀^{M_J}` and `δ_{U_J}` are Haar moduli of conjugation on the
  radicals `U₀(F)`, `M_J(F) ∩ U₀(F)` and `U_J(F)`. Waldspurger's `δ_P` is the modulus of the
  group `P(F)`; on the Levi it is `|det Ad(m)|_{Lie U}|_F` (II.2 (1)), the Haar modulus of
  conjugation on `U(F)`. The Library's `RationalParabolicModulusStatement` follows from proved
  results (`rationalParabolicModulus_of_reductiveUnimodularity` with
  `rationalReductiveUnimodularity` and `dynamicCentralizerReductive`). It identifies Mathlib's
  modular character of an actual standard parabolic with the radical modulus, but in the
  `Aubert.General.RationalPointFamily` presentation. This module does not connect that
  presentation with `standardParabolicPoints`/`standardUnipotentPoints`, and states everything
  for the radical moduli. The published `rationalXi` uses the same convention.
- **Hypotheses on `K`.** The source fixes a special maximal compact `K`. Here `K` is any compact
  open subgroup with `G(F) = P₀(F) K` and `M_J(F) = (P₀(F) ∩ M_J(F))(K ∩ M_J(F))`; for a special
  `K` both hold by Renard V.5.1. No other structural hypothesis is used.
- **Parabolics.** Only standard `P_J ⊇ P₀` are treated. The source reduces semi-standard `P` to
  this case by changing `P₀` ("Quitte à changer `P_0`"), using the independence of `Ξ` from `P₀`;
  that reduction is not formalized.
- **Downstream use.** The Library's abstract consumers of `LeviData` can now be instantiated with
  `rationalLeviData` on actual points: `LeviData.norm_compactIntegral_le_xi` (core of Lemma
  VI.2.2), `LeviData.norm_compactIntegral_le_xi_mul_rpow` (Lemma III.2.3),
  `LeviData.unipotentWeightIntegrable` (Lemma II.4.3) and the proof of Lemma VII.1.2
  (`InducedCoefficientConvergence`). That instantiation is not done here.
- **Lean technique.** `rationalLeviData` and `isIwasawaPair_standardLevi` go through the abstract
  lemmas. Building `LeviData` directly on the concrete subgroups made the kernel time out.
