# Invariant pairings with compact induction from a character are integrals

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`. It proves the general form
of the pairing input `DeltaPairingStatement`. `DeltaPairingGL` specializes it to `GL_(n+1)`.

## Setting

- `G` is a topological group, `N` a subgroup and `θ : N →* ℂˣ` a character.
- `ν` is a measure on `N \ G` (`QuotientIntegration.LeftQuotient N`).
- Hypotheses are added as needed:
  - `SigmaCompactSpace G`;
  - `ν ≠ 0`;
  - right invariance `hνinv`: right translation by each `s ∈ G` preserves `ν`;
  - `IsFiniteMeasureOnCompacts ν` and a Borel structure on `N \ G`;
  - `hcof`: every identity neighbourhood of `G` contains a compact open subgroup;
  - `hθ`: `θ` has open kernel.

This is the classical identification of invariant pairings with compact induction, through
delta functions on `N g K` for small compact open `K`. The Lean argument is self-contained. It
uses no Haar measure on `G` and no integration formula, only the properties of `ν` listed above.

## Coset measures

- `measure_orbit_pos`: for open `K`, the image `orbit N K g` of `g K` has positive measure.
  - Otherwise each translate `rightTranslate N (q.out⁻¹ g)⁻¹(orbit N K g)`, a neighbourhood of
    `q`, would be null.
  - `N \ G` is Lindelöf, so countably many of these sets cover it.
  - Then `ν = 0`.
- `measure_orbit_lt_top`: for compact `K` the image is compact, hence of finite measure.
- `measureReal_orbit_ne_zero` combines the two.

## The representing function

Let `L` be a linear functional on `c-Ind_N^G θ` and `K` a compact open subgroup.
- `reprFun ν L K hK g` is `L(δ_g) / ν(orbit N K g)` for good `g`, and `0` otherwise. Here `δ_g`
  is `deltaVector K hK g`.
- `reprFun_isInverseEquivariant`: `reprFun` is `θ⁻¹`-equivariant. This uses
  `deltaVector_mul_left` and `orbit_mul_left`.
- `reprFun_right`: `reprFun` is right `K`-invariant. This uses `deltaVector_mul_right` and
  `orbit_mul_right`.
- `pairingFun x hf` is the function `x(g) f(g)` descended to `N \ G`, for a `θ⁻¹`-equivariant
  `f`. The product is left `N`-invariant by `eval_mul_invariant`.
- `pairingFun_eq_sum`: for right `K`-invariant `x` and `f`, the delta decomposition
  `exists_delta_decomposition` writes `pairingFun x hf` as a finite sum of constant multiples of
  indicator functions of coset images.
- `integrable_sum_indicator` and `integral_sum_indicator` integrate such sums.
- `integral_pairingFun_reprFun`: for right `K`-invariant `x`, `∫ pairingFun x (reprFun) dν = L x`.
  This is the delta decomposition together with `ν(orbit) ≠ 0`.

## Functionals and uniqueness

- `exists_compact_le` and `exists_compact_stabilizer` give compact open subgroups inside a given
  open subgroup that also fix a given vector.
- `integrable_pairingFun`: `pairingFun x hf` is integrable when `f` is right invariant under
  some open subgroup.
- `pairingFunctional ν hcof hf K0 hfK` is the linear functional `x ↦ ∫ pairingFun x hf dν`.
  - `pairingFun_translate` and `pairingFunctional_translate`: it is invariant under `K0` when
    `f` is right `K0`-invariant. This uses right invariance of `ν`.
- `eq_pairingFunctional_reprFun`: if `L` is invariant under a compact open subgroup `K0`, then
  `L` equals the pairing functional of its representing function on every vector.
  - Replace `x` by its `K0`-average `Compact.averageMap`.
  - Both functionals are unchanged by averaging (`Compact.dual_averageMap_eq_of_mem_fixedVectors`
    with `mem_fixedVectors_dual_of_invariant`).
  - They agree on the averaged, right `K0`-invariant vector by `integral_pairingFun_reprFun`.
- `exists_good_compact`: for a character with open kernel, every open subgroup contains a compact
  open `K` with `g` good for `K`. Take `K` inside `g⁻¹ O g`, where `O ∩ N = ker θ`.
- `eq_of_pairingFunctional_eq`: two right-invariant `θ⁻¹`-equivariant functions with the same
  pairing functional are equal. At each `g`, pair both with a delta vector of a small good `K`.
  `integral_deltaFun_mul` gives `ν(orbit) f₁(g) = ν(orbit) f₂(g)`, and the measure is nonzero.

## Main theorem

- `IsInverseEquivariant.add`, `.smul` and `.translate` give closure properties.
- `pairingFun_add_fun`, `pairingFun_smul_fun` and `pairingFun_translate_fun` give the
  corresponding identities for pairing functions.

`exists_pairing_intertwiner`. Let `π` be a smooth representation of `G` on `E`. Let `β` be a
bilinear form on `c-Ind_N^G θ × E` with `β(g·x, π(g) e) = β(x, e)`. Then there is an intertwiner
`Φ : π → Whittaker.functionRepresentation N θ⁻¹` such that, for all `x` and `e`,
`(Φ e).val` is `θ⁻¹`-equivariant and `β x e = ∫ pairingFun x _ dν`.

Proof:
1. For each `e`, choose a compact open subgroup `Ke e` fixing `e`. Then `β(·, e)` is
   `Ke e`-invariant.
2. Set `Φ(e) = reprFun ν (β(·, e)) (Ke e)`. It represents `β(·, e)` by
   `eq_pairingFunctional_reprFun`.
3. Additivity, homogeneity and equivariance follow from uniqueness (`eq_of_pairingFunctional_eq`).
   - Equivariance means `Φ(π(g) e) = Φ(e)(· g)`.
   - For it, the translated function is right invariant under the open subgroup
     `g (Ke e) g⁻¹`.
   - Its pairing integral is computed by the change of variables `rightTranslate N g`, together
     with the invariance of `β` under `g⁻¹`.
