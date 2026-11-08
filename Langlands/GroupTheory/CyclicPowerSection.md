# Power sections of cyclic quotients

Author: Worker 1556. This is a derived group-theory unit for task
`37d6d58f-e378-4630-8a8c-0f3d7212a970`. It uses Worker 1839's
`transfer_eq_prod_section` from `Langlands.GroupTheory.ExtensionAkizukiWitt`.
All declarations are in `Langlands.GroupExtensionPushout`.

## Setting

`W` and `G` are groups and `q : W →* G` is a homomorphism. Fix `n` with
`[NeZero n]` and a group isomorphism `χ : G ≃* Multiplicative (ZMod n)`. Fix
`w : W` with `hw : χ (q w) = ofAdd 1`. So `q w` generates the cyclic group `G`,
and `q` is surjective.

## Definitions

- `cyclicCoordinate_pow`: `χ (q (w ^ k)) = ofAdd (k : ZMod n)` for every
  natural number `k`.
- `powerSection q χ w hw : Section q` is the normalized section
  `g ↦ w ^ (χ g).toAdd.val`. So the element of coordinate `k`, with
  `0 ≤ k < n`, goes to `w ^ k`. `right_inv` follows from
  `cyclicCoordinate_pow` and `ZMod.natCast_zmod_val`. The section sends `1`
  to `w ^ 0 = 1`.
- `powerKernel q χ w hw : q.ker` is `w ^ n`. It lies in the kernel because
  `(n : ZMod n) = 0`. `powerKernel_coe` records its value in `W`.

## Results

- `pow_eq_pow_div_mul_pow_mod`: `w ^ m = (w ^ n) ^ (m / n) * w ^ (m % n)`.
  This is division with remainder in the exponent.
- `factorKernel_powerSection`: the kernel factor set
  `s g * s h * (s (g * h))⁻¹` of the power section equals
  `powerKernel ^ cyclicCarry (χ g).toAdd (χ h).toAdd`. Here `cyclicCarry` is
  the published carry of `Langlands.ClassFieldTheory.Local.CyclicClass`, and the
  proof uses its defining identity `cyclicCarry_spec`.
- `cocycle_powerSection`: let `A` be a commutative group with a
  `MulDistribMulAction` of `G`. Let `r : q.ker →* A` satisfy the equivariance
  premise of `Section.cocycle`. Then the normalized factor cocycle of the power
  section takes the value `r powerKernel ^ cyclicCarry (χ g).toAdd (χ h).toAdd`
  at `(g, h)`. This is `factorKernel_powerSection` followed by `map_pow`.
- `sum_val_add_one_div`: `∑ x : ZMod n, (x.val + 1) / n = 1`. Only the
  representative `n - 1` contributes. The proof identifies `ZMod (m + 1)` with
  `Fin (m + 1)` and splits off the last term.
- `transfer_powerSection`: let `G` be finite, `K` a subgroup of finite index
  with `q.ker = K`, `M` a commutative group and `ϕ : K →* M`. Then Mathlib's
  transfer satisfies `ϕ.transfer w = ϕ ⟨w ^ n, _⟩`. The proof computes the
  transfer with the power section by `transfer_eq_prod_section`. The term at
  `h` is `s h * w * (s (h * q w))⁻¹ = (w ^ n) ^ ((k + 1) / n)`, where
  `k = (χ h).toAdd.val`. By `sum_val_add_one_div` the exponents add up to one.

## Provenance

Provenance is derived. This is the standard explicit description of the
extension class of a cyclic quotient with a chosen generator lift, as a carry
cocycle with value `w ^ n`. Compare the cohomology of cyclic groups in Serre,
*Local Fields*, Chapter VIII, and the unramified computation behind Tate,
"Number theoretic background" (1979), §1. It also
gives the classical evaluation of the transfer to a normal subgroup with cyclic
quotient at a generator lift: the transfer is the `n`-th power of the generator.
Nothing is assumed beyond the hypotheses listed above.
