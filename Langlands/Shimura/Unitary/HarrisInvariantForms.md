# Harris's (4.8): `K_ℓ`-invariant forms at level `H(m)`

Author: Worker 19.

Harris (1999) identifies the `K_ℓ`-invariants of the forms of level
`H(m) = K^{ℓ,p} × K_ℓ(m) × H_p` with coefficients `𝓛_m` with
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`; this is (4.8). This module proves (4.8) under
his hypothesis (4.5), for any commutative ring `R` and any representation
`V` of `K_ℓ`. It specializes the general results of
`Langlands.Shimura.EquivariantFormsFactor` to Harris's levels at two distinct
primes `ℓ` and `p`.

## Source

Harris (1999), Section 4, printed p. 310 (PDF p. 12): "To continue, we fix
a compact open subgroup `K_p ⊂ GJ_p` contained in a fixed maximal compact
subgroup `C_p`. We strengthen (3.6) by assuming that
`K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is sufficiently small so that
(4.5) `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`. Let `H_p` be an open normal pro-`p` subgroup
of `C_p` contained in `K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`; when
`m = 1` we just write `H`. We now assume `𝓛_m` is a module for
`K_ℓ/K_ℓ(m)`, as in §3."

Harris (1999), Section 4, printed p. 311 (PDF p. 13): "The right-hand side
of (4.7) is the sum of `M` copies of the group `D_m(K_{ℓ,m} × C_p/H_p)` of
`𝒪_m`-valued functions on `K_{ℓ,m} × C_p/H_p`. Via the duality between
functions and group rings, this is canonically isomorphic to
`Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`, and thus the decomposition (4.6)
yields a canonical isomorphism
(4.8) `𝒜_ℓ(GJ, 𝓛_m, H(m))^{K_ℓ} ⥲ Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`."

## Setting

All declarations are in namespace `Langlands.Shimura.DefiniteForms`.

- `σ : AlgebraInvolution ℚ A`, with `A` finite over `ℚ`. `GJ(A_f)` is the
  published `σ.FiniteAdelicPoints`, and `GJ(ℚ)` acts on the left through
  the published diagonal `σ.finiteAdelicDiagonal`.
- `ℓ ≠ p` are primes, with places `vℓ` over `ℓ` and `vp` over `p`.
  `e = σ.finiteAdelicPointsSplit (ℓ p) hn` is the published splitting
  `σ(A_f) ≃ₜ* σ(∏_{v ∣ ℓ p} ℚ_v) × σ(A_f^{ℓ p})`.
- `pairPointsEquiv` (`HarrisPairPoints`) identifies `σ(∏_{v ∣ ℓ p} ℚ_v)`
  with `σ(ℚ_ℓ) × σ(ℚ_p)`. Its components are the published local maps
  `dividingLocalMap` at `ellPlace p vℓ` and `primePlace ℓ vp`.
- `K_ℓ` and `K_ℓ(m)` are subgroups of `σ(ℚ_ℓ)`, `C_p` and `H_p` subgroups of
  `σ(ℚ_p)`, and `L = K^{ℓ,p}` a subgroup of `σ(A_f^{ℓ p})`.
- For subgroups `U ≤ σ(ℚ_ℓ)` and `W ≤ σ(ℚ_p)`, `splitLevel` of
  `pairLevel U W` and `L` (`HarrisDividingLevelFree`) is the level
  `K^{ℓ,p} × U × W` of `GJ(A_f)`. Below, `K_C = K^{ℓ,p} × K_ℓ × C_p`,
  `K_H = K^{ℓ,p} × K_ℓ × H_p` and `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`.
- (4.5) is `HarrisDividingLevelFree σ (ℓ p) hn (ellPlace p vℓ)
  (primePlace ℓ vp) K_ℓ C_p L` (`HarrisDividingLevelFree`).

## Declarations

### Components

- Instance `subgroupOf_self_normal`: a subgroup `H` is normal in itself
  (`H.subgroupOf H`). It is needed for the normality of `H(m)` in `K_H`.
- `pairLevelFst K_ℓ C_p` and `pairLevelSnd K_ℓ C_p` are the components
  `pairLevel K_ℓ C_p →* K_ℓ` and `→* C_p` at the two places
  (`pairLevelFst_apply_coe`, `pairLevelSnd_apply_coe`).
- `finiteAdelicPointsSplit_factorHom`: `e (factorHom e u) = (u, 1)`.
- `pairInl` and `pairInr` embed `σ(ℚ_ℓ)` and `σ(ℚ_p)` into
  `σ(∏_{v ∣ ℓ p} ℚ_v)` with trivial other component, through
  `pairPointsEquiv`. `pairPointsEquiv_pairInl` and `pairPointsEquiv_pairInr`
  give their images `(a, 1)` and `(1, c)`. The four lemmas
  `dividingLocalMap_ellPlace_pairInl`, `dividingLocalMap_primePlace_pairInl`,
  `dividingLocalMap_ellPlace_pairInr` and
  `dividingLocalMap_primePlace_pairInr` give their components.

### The level factorization

- `harrisLevelFactorization σ hℓ hp hℓp vℓ vp hn K_ℓ L hHp`, for
  `H_p ≤ C_p`, is a `LevelFactorization` of `K_C` adapted to `K_H`, with
  `A = K_ℓ`, `B = C_p` and `H = H_p` (as a subgroup of `C_p`):
  - `fst` and `snd` are the components at `ℓ` and `p`
    (`harrisLevelFactorization_fst_coe`, `harrisLevelFactorization_snd_coe`);
  - `inr c = factorHom e (pairInr c)` embeds `C_p` with trivial other
    components (`harrisLevelFactorization_inr_coe`);
  - an element of `K_C` lies in `K_H` exactly when its `p`-component lies in
    `H_p`.
- `harrisLevelFactorization_stabilizer_le`: under (4.5), every stabilizer
  `Δ_g` of `K_C` lies in `ker fst ⊓ ker snd`. This is the hypothesis `hΔ` of
  `EquivariantFormsFactor`.
  - Proof: by `DividingLevelFree.doubleCosetStabilizer_le`, an element `k` of
    `Δ_g` has `(e k).1 = 1`, so both local components of `k` are trivial.
- `ellLevelHom σ hℓ hp hℓp vℓ vp hn K_ℓ L H_p : K_ℓ →* K_H` is
  `a ↦ factorHom e (pairInl a)`, the embedding of `K_ℓ` with trivial other
  components (`ellLevelHom_coe`).
- `exists_eq_ellLevelHom_mul`: every `k ∈ K_H` is `ellLevelHom a · m` with
  `m ∈ H(m)`, for any `K_ℓ(m)`. Take `a` the `ℓ`-component of `k`; then
  `(ellLevelHom a)⁻¹ k` has trivial `ℓ`-component and the same `p`- and
  away components as `k`.

### Harris's (4.8)

Assume `H_p` is normal in `C_p`. Let `ρ` be a representation of `K_ℓ` on an
`R`-module `V`. The forms below have coefficients `ρ` through the
`ℓ`-component (`(harrisLevelFactorization …).rep ρ`).

- `harrisFormsEquiv h hHp ρ`: under (4.5), the forms of level `K_H` are the
  `R`-linear maps `R[(C_p ⧸ H_p) × GJ(ℚ) \ GJ(A_f) / K_C] → V`. It is
  `factorFinsuppEquiv` with the stabilizer hypothesis above.
  - `harrisFormsEquiv_apply_single`: the linear map attached to a form `f`
    sends the basis vector of `([c], x)` to
    `f (x.out · (factorHom e (pairInr c))⁻¹)`.
- `harrisInvariantsEquiv h hℓm hHp ρ`: Harris's (4.8). Assume also that
  `K_ℓ(m) ≤ K_ℓ` is normal in `K_ℓ`. Then `H(m)` is normal in `K_H`, and `K_H`
  acts on the forms of level `H(m)` by the published `levelAction`,
  `(k • f) g = ρ (k_ℓ) (f (g k))`. The invariants of `K_ℓ`, acting through
  `ellLevelHom`, are the `R`-linear maps
  `R[(C_p ⧸ H_p) × GJ(ℚ) \ GJ(A_f) / K_C] → V`.
  - Proof: `H(m)` acts trivially (the published instance for `levelAction`),
    so by `exists_eq_ellLevelHom_mul` and `invariants_comp_eq` the
    `K_ℓ`-invariants are the `K_H`-invariants. The published
    `levelInvariantsEquiv` identifies these with the forms of level `K_H`.
    Then apply `harrisFormsEquiv`.

## Scope

- **Coefficients.** Harris takes `R = 𝒪_m` and `V = 𝓛_m`, a module for
  `K_ℓ/K_ℓ(m)`. Here `R` is any commutative ring and `ρ` any representation
  of `K_ℓ`. When `ρ` is trivial on `K_ℓ(m)`, the forms of level `H(m)` with
  coefficients `ρ` are the `H(m)`-invariant functions, as in Harris. This
  is immediate from the definition of `forms` and is not stated separately
  in Lean.
- **The index set.** The double cosets are taken modulo
  `K_C = K^{ℓ,p} × K_ℓ × C_p`. So the number of copies of `R[C_p ⧸ H_p]` is
  the number `M_C` of these double cosets. Harris's `M` is defined in (4.6)
  as the number of double cosets modulo `K = K^{ℓ,p} × K_ℓ × K_p`. As
  explained in `HarrisDividingLevelFree` ("The index set of (4.7)"), under
  (4.5) `M = [C_p : K_p] · M_C`. So the printed (4.8) with `C_p/H_p` holds
  with `M_C` copies, or with `M` copies when `K_p = C_p`. The relation
  between `M` and `M_C` is not formalized. For a version with `K_p` in place
  of `C_p`, apply this module with `C_p := K_p`. Its hypothesis (4.5) for
  `K_ℓ × K_p` follows from (4.5) for `K_ℓ × C_p` by
  `DividingLevelFree.mono`.
- **Finiteness.** The target uses all double cosets, not a finite number of
  them. The finiteness in (4.6) is not treated.
- **Not covered.** (4.5) is assumed, not proved for any level. The descent
  of the sheaf `𝓛_m`, the spectral sequence (4.9) and Proposition 4.10 are
  not treated.

## Provenance

Derived from Harris (1999), Section 4, printed pp. 310-311, (4.5)-(4.8),
read in the original (rendered pages). The identification of Harris's
levels with a `LevelFactorization`, the embeddings `pairInl` and `pairInr`,
the stabilizer argument and the reduction from `K_ℓ`-invariants to forms of
level `K_H` are written for this module.

Source ID and SHA-256 fingerprint:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies:

- `Langlands.Shimura.EquivariantFormsFactor` (`LevelFactorization`,
  `factorFinsuppEquiv`, `invariants_comp_eq`), submitted in the same
  candidate;
- `Langlands.Shimura.Unitary.HarrisPairPoints` (`pairPointsEquiv`,
  `pairPointsEquiv_apply`, `ellPlace`, `primePlace`) and
  `Langlands.Shimura.Unitary.HarrisDividingLevelFree` (`splitLevel`,
  `pairLevel`, `splitLevelMap`, `HarrisDividingLevelFree`,
  `DividingLevelFree.doubleCosetStabilizer_le`, `factorHom_mem_splitLevel`,
  `pairLevel_subgroupOf_normal`, `splitLevel_subgroupOf_normal`), from
  candidate `2de966a9-8fd3-4a35-8cf5-91658db2a30a`;
- the published `Langlands.Shimura.EquivariantForms` (`forms`,
  `levelAction`, its triviality instance on the smaller level,
  `levelInvariantsEquiv`) and `Langlands.Shimura.SplitLevelTower`
  (`factorHom`, `factorHom_apply`);
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0.

The Mathlib results used include `MonoidHom.codRestrict`,
`MonoidHom.inl`, `MonoidHom.inr`, `Subgroup.subgroupOf_self`,
`ContinuousMulEquiv.apply_symm_apply` and `LinearEquiv.ofEq`.
