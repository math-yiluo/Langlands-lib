# Normalized compact-subgroup distributions: proof of Renard II.3.11

Worker 68, Task 5525. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, II.3.11, printed p.51 /
PDF p.57; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

This proof unit proves the exact published statement
`Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroup.Statements` at its
full group universe `uG`. The final theorem is
`RenardCompactSubgroup.statements`, assembled from the five conjunct theorems
`extendedIntegral`, `doubleCosetUniqueness`, `product`, `conjugation` and
`idempotenceAbsorption`. Every compact subgroup is arbitrary: none of the
arguments assumes it is open. The proof uses the existing objects
`compactSubgroupHaar`, `compactDirac`, `compactSupportPairing`, `support`,
compact `convolution` and the original left/right actions on distributions. It
also uses the compact-convolution laws proved for Task 5394: the pairing formula,
the iterated (Fubini) evaluation, the swap of the iterated pairing,
associativity, and the Dirac laws.

## Haar measure on a compact subgroup

For a compact group `H`, Mathlib's `haarMeasure ⊤` gives the whole group mass
one, so it is a probability measure. It is also right invariant: each right
translate is again a Haar probability measure, and Mathlib's uniqueness of Haar
probability measures (`isHaarMeasure_eq_of_isProbabilityMeasure`) identifies it
with the original. On a compact subgroup `K` this gives the internal helper
`subgroupIntegral K hK φ = ∫_K φ(k) dk`. This is exactly the integral used by
`compactSubgroupHaar`, with the same Borel structure. The helper equals `c` on a
constant `c`. It is invariant under `φ ↦ φ(k₀ ·)` and under `φ ↦ φ(· k₀)` for
`k₀ ∈ K`, and it depends only on the values of `φ` on `K`.

## Extended integral formula

`support (e_K) ⊆ K` holds because `e_K` vanishes on tests vanishing on `K`. For
a locally constant `f`, choose a test function that agrees with `f` on the
compact set `K`. The published `compactSupportPairing_eq_of_agrees` computes the
extended pairing on that representative. The integral over `K` only sees values
on `K`, so the pairing is `∫_K f`. This is `extendedIntegral`.

## Invariance and absorption

Left and right `K`-invariance of `e_K` follow from the two invariances of the
subgroup integral. The published Dirac laws turn them into
`δ_k * e_K = e_K = e_K * δ_k` for `k ∈ K`. Conversely, a compact distribution `D`
with `δ_k * D = D` is left-invariant under `k`, and `D * δ_(l⁻¹) = D` gives right
invariance under `l`.

The absorption lemma says that a compact `T` that is left `K`-invariant satisfies
`e_K * T = T`. By the iterated evaluation, `(e_K * T)(f)` is `∫_K` of
`k ↦ ⟨T, x ↦ f(k x)⟩`. Each inner value is `(leftDistributions k T)(f) = T(f)`,
so the integral of this constant is `T(f)`. The right version, `T * e_L = T` for
right `L`-invariant `T`, uses the swap of the iterated pairing in the same way.
Applying the absorption lemma to the bi-invariant `e_L` gives
`e_K * e_L = e_L = e_L * e_K` for `K ≤ L`. The case `K = L` gives idempotence.
This proves `idempotenceAbsorption`.

The total mass `⟨T, 1⟩` is multiplicative under compact convolution, because
the partial pairing of `S` against the constant function `1` is the constant
`⟨S, 1⟩`. Both `e_K` and every Dirac distribution have mass one.

## Double-coset lemma

Let `A = (e_K * δ_g) * e_L`. Its support lies in `K g L` by the published
support bound for convolution, applied twice with `supp e_K ⊆ K` and
`supp δ_g ⊆ {g}`. Associativity and `δ_k * e_K = e_K` give left `K`-invariance.
`e_L * δ_l = e_L` gives right `L`-invariance. The mass is `1·1·1`.

For uniqueness, let `T` have support in `K g L`, both invariances and mass one.
Absorption gives `T = (e_K * T) * e_L`. By the iterated evaluation twice and the
swap,
`((e_K * T) * e_L)(f) = ⟨T, F⟩` with `F(y) = ∫_K ∫_L f(k y l)`. Here `F` is the
locally constant function `biAverage`, built from the published partial
pairings. The two subgroup invariances show that `F` is constant, equal to
`F(g)`, on `K g L`. Since `supp T ⊆ K g L`, the published
`compactSupportPairing_congr` gives `⟨T, F⟩ = F(g)·⟨T, 1⟩ = F(g)`. The same
computation with `T = δ_g`, whose pairing is evaluation at `g`, gives
`A(f) = F(g)`. Hence `T = A`. This proves `doubleCosetUniqueness`.

## Proposition (i): products

Suppose the supplied compact subgroup `M` has underlying set `K L`. Then
`K, L ≤ M`, so `e_M` is left `K`-invariant and right `L`-invariant. It has mass
one and support in `M = K·1·L`. The uniqueness lemma with `g = 1` and the unit
law `T * δ_1 = T` give `e_M = e_K * e_L`. Inversion shows that `M` also has
underlying set `L K`, which gives the other order. This proves `product`.

## Proposition (ii): conjugation

The image `K' = K.map (MulAut.conj g)` has elements exactly `g k g⁻¹` with
`k ∈ K`, and it is compact as a continuous image of `K`. The internal lemma
`convolution_conj_eq` proves, for any compact subgroup `K'` with that membership
description, that `(δ_g * e_K) * δ_(g⁻¹) = e_(K')`. Its support lies in
`{g} K {g⁻¹} ⊆ K' · 1 · K'`. Left `K'`-invariance uses
`δ_(g k g⁻¹) * δ_g = δ_g * δ_k` (from `convolution_dirac_dirac`), associativity
and `δ_k * e_K = e_K`. Right invariance is symmetric, and the mass is one. The
uniqueness lemma with `K = L = K'` and `g = 1` identifies it with
`e_(K') * e_(K')`, which is `e_(K')` by idempotence. This proves `conjugation`.

## Provenance of internal helpers

`subgroupIntegral`, `biAverage` and the auxiliary lemmas are internal proof
devices. They restate the existing `compactSubgroupHaar` integral and the
published partial pairings, and they introduce no new mathematical objects or
assumptions. The proof route follows Renard's argument: invariance, the
uniqueness lemma, then both propositions through uniqueness. In addition it
proves right invariance of the normalized Haar measure on the compact subgroup.
It also replaces the source's informal function computation by the extended
pairing, so it covers nonopen compact subgroups.
