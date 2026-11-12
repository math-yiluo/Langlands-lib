# The Haar modulus of a weak contraction is the inverse Iwahori index

Author: Worker 4712. Module `Langlands.Representation.Jacquet.IwahoriModulusIndex`,
namespace `Langlands.Jacquet`. This is a supporting module for the necessity half
of Casselman's criterion (Renard 2026, VII.1.2). The module adds no definitions.
It uses `conjRadicalPiece` and `iwahoriIndex` from `IwahoriCellVolume.md`.

`HaarModulus.closedNormalizerCharacter N hN ⟨g, _⟩` is the published modulus
`mulEquivHaarChar` of the automorphism `u ↦ g u g⁻¹` of the closed subgroup `N`
(`Langlands/Group/HaarModulus.lean`). `HaarModulus.closedInverseHalfCharacter N hN M hMN`
is the published character `m ↦ (√δ(m))⁻¹` of `M` by which the normalized Jacquet
module twists the ordinary one.

## Results

- `relIndex_mul_measure`: for a left-invariant measure `μ` on a group `Γ` with
  measurable multiplication, and a measurable subgroup `H ≤ L` of finite index,
  `[L : H] * μ H = μ L`. Proof: `L` is the disjoint union of the translates
  `r • H` over coset representatives `r`, and each translate has measure `μ H`.
- `iwahoriIndex_ne_zero`: for `K` compact open, `N` closed and `g` normalizing
  `N`, the relative index `iwahoriIndex K N g`, that is the index in `K ∩ N` of
  `(g (K ∩ N) g⁻¹) ∩ (K ∩ N)`, is finite and nonzero. No containment of
  `g (K ∩ N) g⁻¹` in `K ∩ N` is assumed. The intersection equals
  `{x ∈ K ∩ N | g⁻¹ x g ∈ K}` (by `mem_conjRadicalPiece_iff_of_mem`, which needs
  only `x ∈ N`), so it is an open subgroup of the compact group `K ∩ N` and has
  finite index. When `g (K ∩ N) g⁻¹ ⊆ K ∩ N`, as for a weak contraction, the
  intersection is the whole conjugated subgroup and the relative index is
  `[K ∩ N : g (K ∩ N) g⁻¹]`.
- `closedNormalizerCharacter_mul_iwahoriIndex` (main result): in a locally compact
  group, for `K` compact open, `N` closed, `g` normalizing `N` and
  `g (K ∩ N) g⁻¹ ⊆ K ∩ N`,
  `closedNormalizerCharacter N hN ⟨g, _⟩ * iwahoriIndex K N g = 1` in `ℝ≥0`.
- `norm_closedInverseHalfCharacter_sq`: for `M` normalizing `N` and `m ∈ M` with
  `m (K ∩ N) m⁻¹ ⊆ K ∩ N`,
  `‖closedInverseHalfCharacter N hN M hMN m‖² = iwahoriIndex K N m`.

## Proof of the main result

Work in `N` with a Haar measure `μ` and the conjugation automorphism
`φ : u ↦ g u g⁻¹`, so `δ(g) = mulEquivHaarChar φ`. Write `U' = K ∩ N` and
`H' = g (K ∩ N) g⁻¹`, both viewed in `N`. By hypothesis `H' ⊆ U'`, and
`φ⁻¹(H') = U'`. Write `d = [U' : H']`. Mathlib's `mulEquivHaarChar_smul_preimage`
gives `δ(g) · μ(φ⁻¹ H') = μ(H')`, that is `δ(g) · μ(U') = μ(H')`. Next,
`relIndex_mul_measure` gives `μ(U') = d · μ(H')`. Substituting,
`δ(g) · d · μ(H') = μ(H')`. Since `H'` is open (positive measure) and contained
in the compact `U'` (finite measure), cancelling `μ(H')` gives `δ(g) · d = 1`. The
relative index inside `N` is `iwahoriIndex K N g` (`Subgroup.relIndex_subgroupOf`).
For the corollary, `‖(√δ)⁻¹‖² = δ⁻¹ = iwahoriIndex K N m`.

## Provenance

Derived. This is the modulus computation that Renard cites in the proof of VII.1.2
(printed p.223 / PDF p.229): "Les calculs de fonctions modulaires effectués en
V.5.4 … donnent … `[K_{m⁻¹Nm} : K_N] = δ_P(m)`". Renard's `δ_P(m)` is the modulus
on `N` in his convention. The published `closedNormalizerCharacter` is
`mulEquivHaarChar` of `u ↦ m u m⁻¹`, which is the reciprocal of Renard's
`δ_P(m)`: its product with `[K_N : m K_N m⁻¹] = [K_{m⁻¹Nm} : K_N]` is `1`. The
proof needs no Bruhat–Tits input; it uses only the inclusion
`m (K ∩ N) m⁻¹ ⊆ K ∩ N`. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`; PDF page = printed
page + 6).
