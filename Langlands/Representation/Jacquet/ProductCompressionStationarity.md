# Stationary compression from a countable power family

Module `Langlands.Representation.Jacquet.ProductCompressionStationarity`.

## Content

Notation: `ρ` is a smooth complex representation of `G` on `V`, `K` a compact open subgroup,
`c = compressedAction ρ hρ K hK g` the compression `v ↦ e_K(ρ(g) v)` on the `K`-fixed vectors,
and `h : IsIwahoriContraction K N M Nbar g` an Iwahori contraction whose first slot `N` is the
subgroup whose coinvariants (`mk ρ N`) are taken.

- `range_pow_le_range_pow_of_le`, `ker_pow_le_ker_pow_of_le`: power ranges decrease and power
  kernels increase.
- `iInf_range_iSup_ker_of_stationary`: if the ranges and kernels of `f ^ s` are constant for
  `s ≥ b`, then for `s ≥ b` they equal the intersection of all power ranges and the union of all
  power kernels (the form required by `CompactCompressionEventuallyStable`).
- `stationary_of_transpose`: over a field, let `p : F → Dual E` be a linear bijection with
  `p (f' ℓ) v = p ℓ (f v)`. If the power ranges and kernels of `f'` are constant from `b` on, so
  are those of `f`. Indeed `ker (f ^ n)` is the annihilator of `p (range (f' ^ n))` and
  `range (f ^ n)` is the joint kernel of `p (ker (f' ^ n))` (the latter uses that a vector
  outside a subspace is separated from it by a functional,
  `Submodule.exists_dual_map_eq_bot_of_notMem`).
- `stationary_of_powerFamily`: assume `g` commutes with every element of `M` and let
  `q n : σ → ρ` (`n : ℕ`) be intertwiners from a smooth `σ` such that
  - (`hlift`) every sequence `x n` of `K`-fixed vectors of `ρ` is `q n w` for one `K`-fixed `w`;
  - (`hinj`) if `mk ρ N (q n w) = 0` for all `n` then `mk σ N w = 0`;
  - (`hsurj`) every sequence `y n` of `N`-coinvariant vectors of `ρ` fixed by `K ∩ M` is
    `mk ρ N (q n w)` for one `w`.

  Then there is `b` with `range (c ^ s) = range (c ^ b)` and `ker (c ^ s) = ker (c ^ b)` for all
  `s ≥ b`.
- `compactCompressionSplits_of_stationary`: if the power ranges and kernels of the compression
  `c` are constant from `b` on, then `CompactCompressionSplits ρ hρ K hK g`.
- `compactCompressionSplits_of_powerFamily`: under the same hypotheses as
  `stationary_of_powerFamily`,
  `CompactCompressionSplits ρ hρ K hK g`.
- `compactCompressionSplits_inv_of_contragredient_stationary`: if the compression by `g` on the
  `K`-fixed vectors of the smooth contragredient has stationary power ranges and kernels from `b`
  on, then `CompactCompressionSplits ρ hρ K hK g⁻¹`.

These are exactly the hypotheses that a power `σ = ρ^ℕ` (realized as a categorical product of
smooth representations) satisfies when the Jacquet functor preserves that product; the module
itself only uses the stated properties.

## Proof

`stationary_of_powerFamily` follows Renard's argument for the uniform bound in VI.9.

1. *Bounded torsion.* Suppose no `b` kills, by `c ^ b`, every `K`-fixed vector in the kernel of
   the Jacquet map. Choose `K`-fixed `x n` with `mk ρ N (x n) = 0` and `c ^ n (x n) ≠ 0`, and a
   `K`-fixed `w` of `σ` with `q n w = x n` (`hlift`). Then `mk σ N w = 0` (`hinj`), so by
   `powerKernelSup_eq_ker_of_iwahoriContraction` (Renard VI.9.1 for `σ`) some power
   `cσ ^ r` kills `w`. Compression is natural for intertwiners (`compressedAction_natural`,
   iterated by `Module.End.commute_pow_left_of_commute`), so `c ^ r (x r) = q r (cσ ^ r w) = 0`,
   a contradiction.
2. *The Jacquet map on `K`-fixed vectors is onto the `K ∩ M`-fixed coinvariants.* Given such `y`,
   put `y n = g^{-n} · y` in the Levi action on coinvariants; these remain `K ∩ M`-fixed because
   `g` is central in `M`. Take `w` with `mk ρ N (q n w) = y n` (`hsurj`). Then `mk σ N w` is
   `K ∩ M`-fixed (its translates differ by an element whose images under all `q n` vanish, so it
   vanishes by `hinj`). By `exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction`
   (Renard VI.9.1.3 for `σ`) there are `s` and a `K`-fixed `x` with
   `mk σ N x = g^s · mk σ N w`. Then `q s x` is `K`-fixed and
   `mk ρ N (q s x) = g^s · y s = g^s g^{-s} y = y`.
3. *Stationarity.* Kernels: `ker (c ^ s)` lies in the union of power kernels, which is the kernel
   of the Jacquet map (`powerKernelSup_eq_ker_of_iwahoriContraction`), hence in `ker (c ^ b)` by
   step 1. Ranges: for `s = b + t` and `K`-fixed `x`, step 2 gives `z` with
   `mk ρ N z = g^{-t} · mk ρ N x`; by `mk_compressedAction_pow_of_iwahoriContraction`,
   `mk ρ N (c ^ t z) = mk ρ N x`, so step 1 gives `c ^ b x = c ^ b (c ^ t z) = c ^ s z`.

`compactCompressionSplits_of_stationary` feeds stationarity through
`iInf_range_iSup_ker_of_stationary` into `compactCompressionSplits_of_eventuallyStable`;
`compactCompressionSplits_of_powerFamily` applies it to `stationary_of_powerFamily`.

`compactCompressionSplits_inv_of_contragredient_stationary` applies `stationary_of_transpose`
with `p = smoothDualFixedRestriction ρ K`, which is bijective
(`smoothDualFixedRestriction_bijective`), and the adjunction identity
`compressedAction_adjoint` for `g⁻¹` (after `inv_inv`), then concludes as above.

## Provenance

Internal to the project. It serves the proof of Renard, *Représentations des groupes réductifs
p-adiques* (French edition dated 9 July 2026), VI.9.6, where the opposite Jacquet functor is
known to preserve countable powers of contragredients, and the stable splitting of compression
(the input to the second adjointness construction of VI.9) must be deduced from that. The
library inputs are the Renard VI.9.1 results (the kernel of the Jacquet map is the union of the
power kernels of compression, and (VI.9.1.3)). The packaging of the hypotheses (`hlift`,
`hinj`, `hsurj`) is chosen to match what a preserved product provides. The transposition step is
standard linear algebra.
