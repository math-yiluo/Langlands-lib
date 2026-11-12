# Harris's hypothesis (4.5) and the restriction to double cosets (4.6)-(4.7)

Author: Worker 19.

Harris (1999) assumes that `K_ℓ × C_p` acts without fixed points on the
double coset space `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`; this is (4.5). He notes
that it strengthens his earlier hypothesis (3.6), and uses it for the
restriction isomorphism (4.7). This module states (4.5) and proves that it
strengthens (3.6). It also proves two corrected forms of (4.7), because
the printed (4.6) and (4.7) do not fit together when `K_p ≠ C_p` (see
"The index set of (4.7)" below). It builds on Worker 61's published (3.6)
(`LocalLevelFree`) and restriction isomorphism (`levelDoubleCosetEquiv`).

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "To continue, we fix
a compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact
subgroup `C_p`. We strengthen (3.6) by assuming that
`K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is sufficiently small so that
(4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`. Let `H_p` be an open normal pro-`p` subgroup
of `C_p` contained in `K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`; when
`m = 1` we just write `H`."

Harris (1999), Section 4, printed pp. 310-311 (PDF pp. 12-13): "(4.6)
`GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^M GJ(ℚ) · K_∞ · K^{ℓ,p} γ_j K_ℓ × K_p`
analogous to (3.9), and hypothesis (4.5) implies that restriction to the
double cosets in (4.6) defines an isomorphism
(4.7) `𝒜_ℓ(GJ, 𝒪_m, H(m)) ⥲ [D_m(K_ℓ × C_p)^M]^{K_ℓ(m) × H_p}`."

Harris (1999), proof of Proposition 4.10, printed p. 311 (PDF p. 13): "By
(4.4.4) and (4.8), these are of the form
`⊕_{i+j=k} Hom_{𝒪/ℓ^m 𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ), Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`,
which can be rewritten (4.10.2)
`⊕_{i+j=k} ⊕_{(e,δ) ∈ O_{-i}} Hom_{𝒪/ℓ^m 𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`."

Harris's (3.6) (printed p. 307, PDF p. 9), as quoted in the published
`DefiniteFormsDoubleCoset.md`: "`K_ℓ` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ`".

## Setting

All declarations are in namespace `Langlands.Shimura.DefiniteForms`.

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. `GJ(A_f)` is the
  published `σ.FiniteAdelicPoints`. `GJ(ℚ)` acts on the left through the
  published diagonal `σ.finiteAdelicDiagonal`.
- `n ≠ 0` is a natural number. `e = σ.finiteAdelicPointsSplit n hn` is the
  published splitting `σ(A_f) ≃ₜ* σ(∏_{v ∣ n} ℚ_v) × σ(A_f^n)`.
- `factorHom e` and `awayHom e` are the published embeddings of the two
  factors (`Langlands.Shimura.SplitLevelTower`). Their images commute.
- `U` is a subgroup of `σ(∏_{v ∣ n} ℚ_v)` and `L` a subgroup of `σ(A_f^n)`.
  In Harris's case, `n = ℓ p`, `U = K_ℓ × C_p` and `L = K^{ℓ,p}`.

## Declarations

### Split levels

- `splitLevel σ n hn U L` is the subgroup `e⁻¹ (U × L)` of `σ(A_f)`
  (`mem_splitLevel`). `splitLevel_mono` gives monotonicity in both
  arguments.
- `factorHom_mem_splitLevel`: an element `u` of `U`, embedded by
  `factorHom e`, lies in `e⁻¹ (U × L)`.
- `mem_splitLevel_bot`: `e⁻¹ (1 × L)` is the image of `L` under
  `awayHom e`. This is Harris's `K^{ℓ,p}` inside `GJ(A_f)`.
- `mk_mul_factorHom_eq`: right translation by the embedded first factor is
  well defined on `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`, because the two factors
  commute. So `σ(∏_{v ∣ n} ℚ_v)` acts on this double coset space.

### Hypothesis (4.5)

- `DividingLevelFree σ n hn U L : Prop` is Harris's (4.5). For every `g` in
  `σ(A_f)` and `u ∈ U`: if `g u` and `g` have the same class in
  `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`, then `u = 1`. Here `u` is embedded by
  `factorHom e`. So `U` acts on the double coset space without fixed points.
- `DividingLevelFree.mono`: (4.5) passes to smaller `U` and smaller `L`.
- `DividingLevelFree.doubleCosetStabilizer_le`: under (4.5), for `U' ≤ U`,
  every stabilizer `Δ_g` of the level `e⁻¹ (U' × L)` lies in
  `e⁻¹ (1 × L)`. Here `Δ_g` is the published `doubleCosetStabilizer`: the
  `k` in the level with `γ g = g k` for some rational `γ`.
  - Proof: write `k = u a` with `u` in the first factor and `a ∈ L`. From
    `γ g = g k = (g u) a` we get `g = γ⁻¹ (g u) a`. So `g u` and `g` have
    the same class, and (4.5) gives `u = 1`.
- `DividingLevelFree.iff_doubleCosetStabilizer_le`: (4.5) holds if and only
  if every `Δ_g` of `e⁻¹ (U × L)` lies in `e⁻¹ (1 × L)`. The converse uses
  the published `doubleCosetStabilizer_le_iff`.

### (4.5) strengthens (3.6)

- `DividingLevelFree.localLevelFree`: under (4.5), for `U' ≤ U` and every
  place `v` dividing `n`, the level `e⁻¹ (U' × L)` satisfies the published
  `LocalLevelFree σ v` (Harris's (3.6) at `v`).
  - Proof: by the published `localLevelFree_iff`, (3.6) says every `Δ_g`
    consists of elements with trivial `v`-component. An element of
    `e⁻¹ (1 × L)` has trivial `v`-component by the published
    `dividingLocalMap_finiteAdelicPointsSplit`.

### Restriction to double cosets (general form of (4.7))

Let `U'` be a subgroup of `U`, normal in `U`.

- `splitLevelMap U L : e⁻¹ (U × L) →* U` is `k ↦ (e k).1`. It is
  surjective (`splitLevelMap_surjective`).
- `splitLevel_subgroupOf`: inside `e⁻¹ (U × L)`, `e⁻¹ (U' × L)` is the
  inverse image of `U'`. So it is normal (instance
  `splitLevel_subgroupOf_normal`).
- `splitLevelQuotientEquiv L U'` is the isomorphism
  `e⁻¹ (U × L) ⧸ e⁻¹ (U' × L) ≃* U ⧸ U'`, `[k] ↦ [(e k).1]`
  (`splitLevelQuotientEquiv_mk`).
- `DividingLevelFree.doubleCosetStabilizer_le_splitLevel`: under (4.5),
  every `Δ_g` of `e⁻¹ (U × L)` lies in `e⁻¹ (U' × L)`.
- `DividingLevelFree.splitLevelEquiv L U' h hU'` is an equivalence of
  representations of `K = e⁻¹ (U × L)`. Its source is the published level
  action of `K` (right translation) on the forms of level
  `N = e⁻¹ (U' × L)` with trivial coefficients `R`. Its target is the
  representation of `U` on the functions
  `U ⧸ U' → (GJ(ℚ) \ GJ(A_f) / K → R)`, `(u · φ)(q) = φ(u⁻¹ q)`,
  restricted to `K` along `splitLevelMap`.
  - It is the published `levelDoubleCosetEquiv`, with the stabilizer
    hypothesis from `doubleCosetStabilizer_le_splitLevel`, followed by the
    published `functionRepresentationCongr` along
    `splitLevelQuotientEquiv`.
  - `DividingLevelFree.splitLevelEquiv_apply_mk`: the image of a form `f`
    takes the value `f(x.out · k⁻¹)` at `[(e k).1]` and the double coset
    `x`.

### Harris's case

- `dividingPlaceOfDvd v hd` (reducible): a place dividing `d` divides every
  multiple `n` of `d`. So the published places over `ℓ` and over `p` give
  places dividing `n = ℓ p`.
- `pairLevel σ vℓ vp K_ℓ C_p`, for two places `vℓ`, `vp` dividing `n`, is
  the subgroup of `σ(∏_{v ∣ n} ℚ_v)` of points whose components at `vℓ`
  and `vp` lie in `K_ℓ` and `C_p` (`mem_pairLevel`). The components are
  the published `dividingLocalMap`. `pairLevel_mono` gives monotonicity.
- Instance `pairLevel_subgroupOf_normal`: if `K_ℓ(m)` is normal in `K_ℓ`
  and `H_p` is normal in `C_p`, then `pairLevel K_ℓ(m) H_p` is normal in
  `pairLevel K_ℓ C_p`.
- `HarrisDividingLevelFree σ n hn vℓ vp K_ℓ C_p L` (an abbreviation) is
  Harris's (4.5): `DividingLevelFree` for `U = pairLevel K_ℓ C_p`.
- `HarrisDividingLevelFree.localLevelFree`: under (4.5) and `K_p ≤ C_p`,
  Harris's `K = K^{ℓ,p} × K_ℓ × K_p` (`splitLevel` of `pairLevel K_ℓ K_p`
  and `L`) satisfies (3.6) at `ℓ`. This is Harris's "We strengthen (3.6)".
- `HarrisDividingLevelFree.restrictionEquiv`: the `C_p`-level form of
  (4.7). Take `K_C = K^{ℓ,p} × K_ℓ × C_p` and
  `N = H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`, with `K_ℓ(m)` normal in `K_ℓ` and
  `H_p` normal in `C_p`. Then the forms of level `H(m)` with trivial
  coefficients `R`, as a representation of `K_C`, are the functions
  `(K_ℓ × C_p) ⧸ (K_ℓ(m) × H_p) → (GJ(ℚ) \ GJ(A_f) / K_C → R)`. The
  double cosets are taken modulo `K_C`, not modulo Harris's `K` of (4.6).
  When `K_p = C_p` the two levels agree.
- `subgroupOf_normal_of_le`: if `H_p` is normal in `C_p` and
  `H_p ≤ K_p ≤ C_p`, then `H_p` is normal in `K_p`.
- `HarrisDividingLevelFree.restrictionEquivOfLe`: the form of (4.7)
  indexed by the double cosets of (4.6). Take `K_p ≤ C_p`, `H_p ≤ K_p`,
  `K_ℓ(m)` normal in `K_ℓ` and `H_p` normal in `K_p`, and Harris's level
  `K = K^{ℓ,p} × K_ℓ × K_p`. Then, under (4.5) for `K_ℓ × C_p`, the forms
  of level `H(m)` with trivial coefficients `R`, as a representation of
  `K`, are the functions
  `(K_ℓ × K_p) ⧸ (K_ℓ(m) × H_p) → (GJ(ℚ) \ GJ(A_f) / K → R)`. The factor
  is `K_ℓ × K_p` in place of Harris's printed `K_ℓ × C_p`.
  - Proof: (4.5) for `K_ℓ × C_p` gives (4.5) for `K_ℓ × K_p`
    (`DividingLevelFree.mono`). Then apply `restrictionEquiv` with `K_p` in
    place of `C_p`.

## Scope

- **Adelic setting.** As in the published `DefiniteFormsDoubleCoset`,
  Harris's `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}` is read as
  `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`.
- **The pair `K_ℓ × C_p`.** `pairLevel` constrains only the components at
  `vℓ` and `vp`. For `n = ℓ p` with primes `ℓ ≠ p`, these are the only
  places dividing `n`. The companion module `HarrisPairPoints` proves
  `σ(∏_{v ∣ ℓ p} ℚ_v) ≅ σ(ℚ_ℓ) × σ(ℚ_p)` and that `pairLevel` is then
  `K_ℓ × C_p` (`pairLevel_eq_comap`). The general results are stated for an
  arbitrary subgroup `U`, so they do not depend on it.
- **The index set of (4.7).** Harris's (4.6) takes double cosets modulo
  `K = K^{ℓ,p} × K_ℓ × K_p`, and `M` is their number. His (4.7) takes `M`
  copies of the functions on `K_ℓ × C_p`. These fit together only when
  `K_p = C_p`. The reason is as follows; this explanation is not
  formalized here. Under (4.5), `X = GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}` is a free
  `K_ℓ × C_p`-set. Each `K_ℓ × C_p`-orbit is a copy of `K_ℓ × C_p` and
  splits into `[C_p : K_p]` orbits of `K_ℓ × K_p`, one for each coset in
  `K_p \ C_p`. So the number of double cosets modulo `K` is `[C_p : K_p]`
  times the number modulo `K_C = K^{ℓ,p} × K_ℓ × C_p`. The forms of level
  `H(m)` are therefore functions on `M_C` copies of
  `(K_ℓ × C_p) ⧸ (K_ℓ(m) × H_p)`, with `M_C` the number of double cosets
  modulo `K_C`. Equivalently they are functions on `M` copies of
  `(K_ℓ × K_p) ⧸ (K_ℓ(m) × H_p)`. Harris's printed pairing of `M` with
  `K_ℓ × C_p` counts `[C_p : K_p]` times too many copies. Harris's own proof
  of Proposition 4.10 first writes `𝒪_m[K_p/H_p]^M` and then
  `𝒪_m[C_p/H_p]^M`. This module proves both corrected forms:
  `restrictionEquiv` (index set modulo `K_C`, factor `K_ℓ × C_p`) and
  `restrictionEquivOfLe` (index set modulo Harris's `K`, factor
  `K_ℓ × K_p`). For `K_p = C_p` both are Harris's (4.7).
- **Form of the target.** Harris writes the right side as finitely many
  copies of the invariant functions on a group. Here the target is the
  functions on the quotient group with values in the functions on all
  double cosets. The finiteness of the double cosets (4.6) and the
  coefficients `𝓛_m` of (4.8) are not treated. Harris takes
  `R = 𝒪/ℓ^m 𝒪`; here `R` is any commutative ring.
- **Not covered.** The module does not prove (4.5) for any particular level;
  Harris assumes it, by taking `K^{ℓ,p}` small. It does not treat (4.8),
  (4.9) or Proposition 4.10.

## Provenance

Derived from Harris (1999), Section 4, printed pp. 310-311, read in the
original (rendered pages). The formulation through the published splitting
of `σ(A_f)` at the places dividing `n`, the stabilizer criterion, the
derivation of (3.6) and of the two corrected forms of (4.7) from it, and the
comparison of the index sets of (4.6) and (4.7) are written for this
module. They
combine Worker 61's published `LocalLevelFree`, `localLevelFree_iff`,
`doubleCosetStabilizer_le_iff` and `levelDoubleCosetEquiv`.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- the published `Langlands.Shimura.DefiniteFormsDoubleCoset`
  (`LocalLevelFree`, `localLevelFree_iff`), and through it
  `Langlands.Shimura.EquivariantFormsDoubleCoset`
  (`doubleCosetStabilizer`, `doubleCosetStabilizer_le_iff`,
  `levelDoubleCosetEquiv`) and `Langlands.Induction.functionRepresentationCongr`;
- the published `Langlands.Shimura.SplitLevelTower` (`factorHom`,
  `awayHom`, `factorHom_mul_awayHom`, `factorHom_commute_awayHom`);
- the published `Langlands.Shimura.Unitary.PointsSplit`
  (`finiteAdelicPointsSplit`, `dividingLocalMap`,
  `dividingLocalMap_finiteAdelicPointsSplit`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `DoubleCoset.eq`,
`QuotientGroup.quotientKerEquivOfSurjective`,
`QuotientGroup.quotientMulEquivOfEq`,
`Subgroup.le_normalizer_of_normal_subgroupOf` and
`Subgroup.normal_subgroupOf_of_le_normalizer`.
