# Waldspurger's weights `Ξ`, `σ` and the Schwartz space `C(G)` on actual rational points

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights`, namespace
`Langlands.HarishChandraSchwartz`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234. The quotations and paraphrases below are those checked in
the Library's `Spherical.md`, `Height.md`, `Basic.md`, `TestFunctions.md` and
`TemperedExponentCone.md`; the present author could not open the PDF in this session.

- I.1, printed p. 240 (PDF p. 6): `G = P₀ K` for the minimal parabolic `P₀ = M₀ U₀` and the special
  maximal compact subgroup `K`; Haar measures are normalized by `mes(H ∩ K) = 1`.
- I.1, printed p. 242 (PDF p. 8): for an algebraic embedding `τ : G → GL_n(F)` with
  `τ(K) ⊂ GL_n(𝒪)`, `‖g‖ = sup_{i,j} sup(|a_ij|_F, |b_ij|_F)` where `τ(g) = (a_ij)` and
  `τ(g)⁻¹ = (b_ij)`; "`‖g‖ ⩾ 1`, `‖g_1g_2‖ ⩽ ‖g_1‖‖g_2‖`" and "`σ(g) = log‖g‖`".
- II.1, printed pp. 250–251 (PDF pp. 16–17): `Ξ(g) = ⟨π(g)e, e⟩` for `π = I_{P₀}^G 1` and its
  `K`-invariant vector `e` with `e(1) = 1`, and the formula `Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk`,
  where `g = u₀(g) m₀(g) k₀(g)` and `δ₀` is the modulus of `P₀`.
- Lemme II.1.1, printed p. 251: `Ξ` is bi-`K`-invariant (first assertion). Lemme II.1.3, printed
  p. 252: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`.
- III.6, printed p. 271 (PDF p. 37): `ν_r(f) = sup_g |f(g)| Ξ(g)⁻¹ (1 + σ(g))^r`; `C_H` is the
  space of `H`-bi-invariant functions with all `ν_r(f)` finite; `C(G) = ⋃_H C_H` with the
  inductive-limit topology; "L'espace `C_c^∞(G)` est inclus et dense dans `C(G)`."

## Setting

`F` is a nonarchimedean local field (any characteristic), `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, and `G(F) = rationalPoints G` carries
the canonical topology `rationalPointTopology F G.X` (a locally compact, Hausdorff, totally
disconnected, second countable topological group by the Library's `rationalPoint_*` results) and
its Borel σ-algebra. `i : S → G` and `ν` are a torus homomorphism and a cocharacter; in the
intended use `i` is a maximal split torus and `ν` is generic, so that
`P₀(F) = standardParabolicPoints i ν ∅` and `U₀(F) = standardUnipotentPoints i ν ∅` are the
minimal standard parabolic and its radical. No reductivity, splitness or quasi-splitness is
needed for the constructions of this module.

The special maximal compact subgroup is not constructed here. `Ξ` takes as data a subgroup `K` of
`G(F)` that is compact (`hKc`) with `G(F) = P₀(F) K` (`hPK : IsIwasawaPair P₀(F) K`); the results
also assume `K` open (`hKo`). The Library's actual Iwasawa product equalities
(`BruhatTits.Iwasawa.PointProductEqualities`, whose existence for special compact subgroups is the
unproved `IwasawaExistenceStatement`) supply `hPK` by `isIwasawaPair_of_pointProductEqualities`.

## Definitions

- **`rationalMinimalModulus i ν : P₀(F) →* ℝ≥0ˣ`** (Waldspurger's `δ₀`): the Haar modulus of
  conjugation by `p ∈ P₀(F)` on the closed subgroup `U₀(F)`, i.e. `μ(p E p⁻¹) = δ₀(p) μ(E)` for a
  Haar measure `μ` of `U₀(F)` (the Library's `HaarModulus.closedRestrictCharacter`, built on
  Mathlib's `mulEquivHaarChar`). On the Levi component this is `|det Ad(m)|_{Lie U₀}|_F`, the
  modulus used in `I_{P₀}^G`; this comparison is not proved here.
- **`rationalXi hKc hPK`** (the recorded declaration; Waldspurger's `Ξ`): the Library's generic
  `xi hPK (rationalMinimalModulus i ν)`, that is `Ξ(g) = ∫_K δ₀(p(kg))^{1/2} dk` for the Haar
  probability measure of `K`, where `kg = p(kg) k'` with `p(kg) ∈ P₀(F)`, `k' ∈ K`.
- **`rationalHeight ρ`** (Waldspurger's `σ`): `σ(g) = log ‖ρ(g)‖`, with
  `MatrixRepresentation.rationalMatrixNorm F ρ g` the largest residue-normalized absolute value of
  an entry of `ρ(g)` or `ρ(g)⁻¹`, for a matrix representation `ρ : G → GL_n`.
- `rationalHeightSubgroup ρ`: the points of norm at most `1`, `ρ⁻¹(GL_n(𝒪))` on `G(F)`;
  `rationalHeightCompactOpen ρ hρ` is this subgroup as a compact open subgroup when `ρ` is a
  closed immersion (`hρ : IsClosedSubgroup ρ`).
- **`RationalSchwartzSpace hKc hPK ρ`** (Waldspurger's `C(G)`): the Library's generic
  `Space Ξ σ` for these weights, with its locally convex inductive-limit topology.
- `rationalSchwartzOfTestFunction hKo hKc hPK ρ`: the inclusion `C_c^∞(G(F)) → C(G)`.

### Correspondence with the source

- In the source, `δ₀(m₀(kg))` is evaluated at the `M₀`-component. Here `δ₀` is evaluated at the
  `P₀`-component `p(kg)`; the two agree when `δ₀` is trivial on `U₀(F)`.
  `rationalMinimalModulus_eq_one_of_mem_compactOpen` proves this triviality at every point of
  `U₀(F)` lying in a compact open subgroup of `U₀(F)`, so the two agree whenever `U₀(F)` is the
  union of its compact open subgroups (as follows, for instance, from Renard's exhaustion
  property V.5.2(iii)). This union property is not proved in this module; the companion module
  `RationalXiLowerBound` (same candidate) proves `δ₀ = 1` on `U₀(F)` from one Renard V.5.2 basis
  member for the minimal parabolic.
- The identification of `Ξ` with the matrix coefficient `⟨π(g)e, e⟩` of `I_{P₀}^G 1` is not
  proved here (as in the Library's `Spherical`).
- The source takes `τ` with `τ(K) ⊂ GL_n(𝒪)`, which makes `σ` bi-`K`-invariant. Here `ρ` is any
  matrix representation; `σ` is bi-invariant under `ρ⁻¹(GL_n(𝒪))`
  (`rationalHeight_mul_mul`), which contains `K` exactly when `ρ(K) ⊂ GL_n(𝒪)`.

## Results

- `standardParabolicPoints_le_normalizer_standardUnipotentPoints` (any `J`): `P_J(F)` normalizes
  `U_J(F)`, directly from the defining intersections over standard cocharacters and
  `Dynamic.conj_mem_unipotent`.
- `isIwasawaPair_of_pointProductEqualities`.
- `rationalMinimalModulus_eq_one`: `δ₀(p) = 1` for `p ∈ P₀(F) ∩ K`, `K` compact open (conjugation by
  `p` preserves the compact open subgroup `K ∩ U₀(F)`, and the Library's
  `normalizerCharacter_eq_one_of_preimage` applies). This is the hypothesis `hδ` of the generic
  `Spherical` results.
- `rationalMinimalModulus_eq_one_of_mem_compactOpen`: as above for a point of `U₀(F)` in a compact
  open subgroup of `U₀(F)`.
- `rationalXi_one` (`Ξ(1) = 1`), `rationalXi_pos` (`Ξ > 0`), `rationalXi_mul_mul` (bi-`K`-invariance,
  first assertion of Lemme II.1.1), `continuous_rationalXi`, and `integral_rationalXi_mul_mul`
  (Lemme II.1.3), from the generic `xi_one`, `xi_pos`, `xi_mul_mul`, `continuous_xi`,
  `integral_xi_mul_mul`.
- `rationalHeight_nonneg`, `rationalHeight_one`, `rationalHeight_inv`, `rationalHeight_mul_le`
  (`σ(gh) ≤ σ(g) + σ(h)`), `continuous_rationalHeight`, from the Library's laws of
  `rationalMatrixNorm` (`one_le_rationalMatrixNorm`, `rationalMatrixNorm_mul_le`, ...).
- `rationalMatrixNorm_mul_mul`, `rationalHeight_mul_mul`: bi-invariance under `ρ⁻¹(GL_n(𝒪))`.
- `isOpen_rationalHeightSubgroup`: `ρ⁻¹(GL_n(𝒪))` is open. Points whose matrix entries (and those
  of the inverse) are within distance `< 1` of the identity entries form a neighbourhood of `1`
  (continuity of the entries and of the absolute value), and by the ultrametric inequality their
  entries have absolute value `≤ 1`.
- For a closed immersion `ρ : G → GL_N`: `isCompact_rationalHeight_le` (every `{σ ≤ C}` is compact)
  and `isCompact_rationalHeightSubgroup`, from the Library's `isCompact_rationalMatrixNorm_le`.
- `rationalSchwartzOfTestFunction_injective` and
  **`denseRange_rationalSchwartzOfTestFunction`** (for a closed immersion `ρ`): the inclusion
  `C_c^∞(G(F)) ⊆ C(G)` and its density (III.6), from the Library's `ofSchwartzBruhat` and
  `denseRange_ofSchwartzBruhat` with the compact open subgroup `ρ⁻¹(GL_N(𝒪))`.

## Scope

- The existence of a compact open `K` with `G(F) = P₀(F) K` (special maximal compact subgroup and
  Iwasawa decomposition) and of a closed immersion with `ρ(K) ⊂ GL_n(𝒪)` are not proved here.
- The upper bound of Lemme II.1.1, II.1.2 and II.1.4–II.1.6 for the actual `Ξ` (the lower bound of
  Lemme II.1.1 on the lattice chamber of `M₀` is in the companion module `RationalXiLowerBound`),
  the completeness of `C(G)`, and the comparison of `δ₀` with `|det Ad|` and with
  Mathlib's modular character of `P₀(F)` (the Library's `RationalParabolicModulusStatement`) are
  not treated in this module.
