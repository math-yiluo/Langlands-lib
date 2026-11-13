# Compression by an element dominating a power of an Iwahori contraction

Author: Worker 5457. Module `Langlands.Representation.Jacquet.DominatedIwahoriContraction`,
namespace `Langlands.Jacquet`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.9.1, Remarque 3 after the Proposition and the last paragraph of the
proof of the Remarks (printed p.198 / PDF p.204). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This module is the group-theoretic and linear-algebraic part of Remark 3, for an arbitrary
topological group `G`. It contains no geometry of split tori and does not prove the
Proposition of VI.9.1. The conclusions of that Proposition are explicit hypotheses here.

## Setting

`K` is a compact open subgroup of `G`, and `N`, `M`, `Nbar` are subgroups of `G` with
`M ≤ normalizer N` and `M ≤ normalizer Nbar`. `t₀` satisfies the Library predicate
`IsIwahoriContraction K N M Nbar t₀`: `t₀ ∈ M`, the Iwahori factorization of `K`,
conjugation by `t₀` preserving `K ∩ N`, conjugation by `t₀⁻¹` preserving `K ∩ M` and
`K ∩ Nbar`, exhaustion of `N`, and uniform contraction of `K ∩ Nbar`. `t₀` and `g` are
`M`-central, i.e. they commute with every element of `M`. For a smooth complex
representation `ρ`, `compressedAction ρ hρ K hK x` is `A_x : v ↦ e_K(ρ(x) v)` on `V^K`.
`powerKernelSup` is Renard's `V^K_0`, the supremum of the kernels of the powers of `A_x`.
`stableImage` is `V^K_*`, the intersection of their ranges. `CompactCompressionSplits`
says that these two submodules are complementary.

We say that `g ∈ M` **dominates** `t₀ ^ b` when

* (`hup`) `g (t₀^{-b} u t₀^b) g⁻¹ ∈ K` for every `u ∈ K ∩ N`, and
* (`hlow`) `g⁻¹ (t₀^b l t₀^{-b}) g ∈ K` for every `l ∈ K ∩ Nbar`.

These are Renard's conditions `C ⊂ t^{-1} K_N t` and `C̄ ⊂ t K_{N̄} t^{-1}` with
`C = t₀^{-b} K_N t₀^b` and `C̄ = t₀^b K_{N̄} t₀^{-b}`, for `t = g`. The word "dominates"
and the packaging below are ours.

## Declarations

### Group lemmas

* `conj_pow_mem_of_conj_mem`: if conjugation by `y` maps a subgroup `H` into itself, then
  so does conjugation by `y ^ r` for every `r`. Proof by induction on `r`.
* `inv_conj_pow_mem_of_inv_conj_mem`: the same for conjugation by `y⁻¹` and `(y ^ r)⁻¹`.

### `IsIwahoriContraction.of_dominates`

Let `t₀` be an Iwahori contraction and `b ≥ 1`. Let `g ∈ M` be `M`-central and dominate
`t₀ ^ b`. Then `IsIwahoriContraction K N M Nbar g`.

Proof. Since `g` is `M`-central and `t₀ ∈ M`, `g` commutes with `t₀ ^ b`. Put
`Y = t₀^{-b} g = g t₀^{-b} ∈ M`, so `g = Y t₀^b = t₀^b Y` and `Y` commutes with `t₀ ^ b`.
The condition `hup` says that conjugation by `Y` maps `K ∩ N` into `K`, hence into
`K ∩ N` because `Y ∈ M` normalizes `N`. Likewise `hlow` says that conjugation by `Y⁻¹`
maps `K ∩ Nbar` into `K ∩ Nbar`. The fields are proved as follows.

* `upper`: for `u ∈ K ∩ N`, `u' = t₀^b u t₀^{-b} ∈ K ∩ N` (`upper_pow`), and
  `g u g⁻¹ = g (t₀^{-b} u' t₀^b) g⁻¹ ∈ K` by `hup`. It lies in `N` since `g ∈ M`.
* `levi`: `g⁻¹ m g = m` by centrality.
* `lower`: symmetric to `upper`, using `l' = t₀^{-b} l t₀^b` and `hlow`.
* `exhaust`: for `x ∈ N`, `eventually_mem` gives `r` with `t₀^s x t₀^{-s} ∈ K` for all
  `s ≥ r`. Then `g^r x g^{-r} = Y^r (t₀^{br} x t₀^{-br}) Y^{-r}`. Since `br ≥ r`, the
  inner element lies in `K ∩ N`, and conjugation by `Y^r` preserves `K ∩ N`.
* `contract`: for an open subgroup `L`, the `contract` field of `t₀` gives `s`. Write
  `bs = s + c`. Then `g^{-s} l g^s = t₀^{-s} (t₀^{-c} (Y^{-s} l Y^s) t₀^c) t₀^s`, and the
  inner element lies in `K ∩ Nbar`.

### `compressedAction_eq_of_dominates`

Assume in addition that `t₀` is `M`-central. Then
`A_g = A_Y ∘ A_{t₀}^b` and `A_g = A_{t₀}^b ∘ A_Y` with `Y = t₀^{-b} g`. Both follow from
the Library multiplicativity `compressedAction_mul_of_factor` and
`IsIwahoriContraction.compressedAction_pow`.

* For `g = Y · t₀^b`, conjugation by `Y` must map `K ∩ N` into `K`, which is `hup`.
  Conjugation by `t₀^{-b}` must map `K ∩ Nbar` and `K ∩ M` into `K`.
* For `g = t₀^b · Y`, conjugation by `t₀^b` must map `K ∩ N` into `K`. Conjugation by
  `Y⁻¹` must map `K ∩ Nbar` into `K`, which is `hlow`. It must also map `K ∩ M` into `K`,
  which holds because `Y` commutes with `M`; this uses the centrality of `t₀`.

### `ker_range_compressedAction_of_dominates`

Assume the hypotheses of `of_dominates` and that `t₀` is `M`-central. Assume also:

* `V^K_0(t₀) = ker A_{t₀}^b` and `V^K_*(t₀) = Im A_{t₀}^b`, and
* the compressions of `t₀` and of `g` split.

Then `V^K_0(t₀) = ker A_g` and `V^K_*(t₀) = Im A_g`.

Proof.

* `V^K_0(t₀) = ker A_{t₀}^b ⊆ ker (A_Y ∘ A_{t₀}^b) = ker A_g`.
* `ker A_g ⊆ V^K_0(g) = V^K_0(t₀)`. The equality holds because both kernel suprema are
  the kernel of the Jacquet map on `V^K`. This is the Library
  `powerKernelSup_eq_ker_of_iwahoriContraction`, applied to `g` (an Iwahori contraction by
  `of_dominates`) and to `t₀`.
* `Im A_g = Im (A_{t₀}^b ∘ A_Y) ⊆ Im A_{t₀}^b = V^K_*(t₀)`.
* `V^K_*(g) ⊆ Im A_g ⊆ V^K_*(t₀)`. By the two splittings, `V^K_*(g)` and `V^K_*(t₀)` are
  both complements of `V^K_0(t₀)`. In the modular lattice of submodules, two comparable
  complements of the same element are equal (`eq_of_le_of_inf_le_of_sup_le`). Hence
  `V^K_*(t₀) = V^K_*(g) ⊆ Im A_g`.

This differs from Renard's proof, which compares `ker` and `Im` with averages `e_C` and
`e_{C̄}` (Remark 2). Here the comparison goes through the factorization of `A_g` and the
splitting for `g`. The splitting for `g` is available in applications because `g` is
itself an `M`-central Iwahori contraction.
