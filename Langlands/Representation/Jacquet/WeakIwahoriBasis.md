# Iwahori bases contracted strictly by one element and weakly by another

Author: Worker 4712. Module `Langlands.Representation.Jacquet.WeakIwahoriBasis`,
namespace `Langlands.Jacquet`. This is a supporting module for the necessity half
of Casselman's criterion (Renard 2026, VII.1.2), see
`Langlands/Representation/Exponents/CasselmanNecessity.md`.

## The new definition

`IsWeakIwahoriContraction K N M Nbar g`, for an open subgroup `K` of a topological
group `Γ`, subgroups `N`, `M`, `Nbar` and an element `g`, is the structure with
fields

- `mem_levi : g ∈ M`;
- `upper`: `g u g⁻¹ ∈ K ∩ N` for every `u ∈ K ∩ N`;
- `levi`: `g⁻¹ m g ∈ K ∩ M` for every `m ∈ K ∩ M`;
- `lower`: `g⁻¹ l g ∈ K ∩ Nbar` for every `l ∈ K ∩ Nbar`.

These are exactly the conjugation fields of the published `IsIwahoriContraction`
(`Langlands/Representation/Jacquet/IwahoriContraction.lean`), without its
factorization, exhaustion and uniform-contraction fields. In Renard's notation for
`P = MN` and `K = K_N K_M K_{N̄}`, it says `g ∈ M`, `g K_N g⁻¹ ⊆ K_N`,
`g⁻¹ K_M g ⊆ K_M` and `g⁻¹ K_{N̄} g ⊆ K_{N̄}`. These are the inclusions Renard
uses for the elements `m ∈ M⁺` in the proof of VII.1.2 (printed p.222 / PDF
p.228): "`m⁻¹K_{N̄}m ⊂ K_{N̄} ⊂ K`, `m⁻¹K_M m = K_M ⊂ K`, et
`m⁻¹K_N m = K_{m⁻¹Nm} ⊃ K_N`". Points on the boundary of the chamber, such as
`λ(ϖ)` for a cocharacter `λ` that pairs to zero with some simple roots, satisfy
these inclusions but not the strict contraction fields. The weak notion exists
for these points.

## Results

- `IsIwahoriContraction.isWeakIwahoriContraction`: an Iwahori contraction is weak.
- `IsWeakIwahoriContraction.one`, `.mul`, `.pow`: `1` (when `1 ∈ M`), products and
  natural powers of weak contractions are weak contractions. Each field is a direct
  conjugation computation.
- `exists_stable_piece_of_weak`: inside a compact open subgroup `V` of a
  nonarchimedean group, for a closed subgroup `H` normalized by `M`, elements
  `h, a ∈ M` central in `M`, with the powers of `h` contracting `H` uniformly on
  compact sets and conjugation by the powers `a ^ i` equicontinuous at `1` on `H`,
  the subgroup
  `P = {x ∈ H | (a ^ i h ^ j) x (a ^ i h ^ j)⁻¹ ∈ V for all i, j ∈ ℕ}`
  is compact, contained in `V`, stable under conjugation by `h`, by `a` and by
  `V ∩ M`, and contains every element of `H` in some identity neighborhood. The
  last point uses an open subgroup `V₁ ⊆ V` on which equicontinuity gives
  `a ^ i V₁ a⁻ⁱ ⊆ V`, then uniform contraction of `V₁ ∩ H` by `h ^ j` for `j > N`,
  and continuity of the finitely many maps `x ↦ h ^ j x h⁻ʲ`, `j ≤ N`.
- `exists_weakIwahoriBasis_of_contraction` (main result). Let `Γ` be locally
  compact and nonarchimedean, `U, M, O` subgroups with `U, O` closed and normalized
  by `M`, with unique factorization in `O · M · U` and the product
  `(A ∩ O)(B ∩ M)(C ∩ U)` an identity neighborhood for all identity neighborhoods
  `A, B, C`. Let `g, a ∈ M` be central in `M`, the powers of `g` contracting `U`
  (and those of `g⁻¹` contracting `O`) uniformly on compact sets, and conjugation by
  the powers of `a` (resp. `a⁻¹`) equicontinuous at `1` on `U` (resp. `O`). Then
  every open identity neighborhood `W` contains a compact open subgroup `K` with
  `IsIwahoriContraction K U M O g` and `IsWeakIwahoriContraction K U M O a`.

## Proof of the main result

The proof follows the published strict version
`hasOppositeIwahoriContractionBasis_of_contraction`
(`OppositeIwahoriBasisAbstract.lean`), with `exists_stable_piece_of_weak` in place
of `exists_stable_piece`. Choose a compact open `V ⊆ W`. The stable pieces
`A0 ⊆ O` (for `g⁻¹`, `a⁻¹`) and `C0 ⊆ U` (for `g`, `a`) and `B0 = V ∩ M` give an
identity neighborhood `A0 B0 C0`, which contains an open subgroup `Q`. Choose `n`
such that every `gⁿ c g⁻ⁿ`, `c ∈ C0`, is conjugated into `Q` by all of `A0`, and
every `g⁻ⁿ a gⁿ`, `a ∈ A0`, has inverse in `Q` and is conjugated into `Q` by all of
`C0`. Then `A = g⁻ⁿ A0 gⁿ` (the preimage of `A0` under conjugation by `gⁿ`)
satisfies the swap property `C0 · A ⊆ A · B0 · C0`, proved with unique
factorization. Hence `K = A B0 C0` is a subgroup; it is open because it contains a
product neighborhood, compact as a closed subset of `V`, and the unique
factorization gives `K ∩ U = C0` and `K ∩ O = A`. The fields of the strict
contraction for `g` (factorization, exhaustion from contraction into the
neighborhood of `C0`, uniform contraction of `A ⊆ A0`) and the weak fields for `a`
(`a C0 a⁻¹ ⊆ C0`, `a⁻¹ A a ⊆ A`, and `a⁻¹ m a = m` on `K ∩ M` by centrality)
follow.

## Provenance

Derived. Renard (VII.1.2, printed p.221 / PDF p.227) takes `K` "admettant une
décomposition d'Iwahori selon les sous-groupes paraboliques standards", from the
Bruhat–Tits theory of V.5. This module replaces that input by the open-cell
construction of the published strict basis, adding a second, weakly contracting
element. Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`;
PDF page = printed page + 6).
