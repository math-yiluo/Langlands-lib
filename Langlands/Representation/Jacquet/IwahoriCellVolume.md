# Volumes of Iwahori double cosets in the central quotient

Author: Worker 4712. Module `Langlands.Representation.Jacquet.IwahoriCellVolume`,
namespace `Langlands.Jacquet`. This is a supporting module for the necessity half
of Casselman's criterion (Renard 2026, VII.1.2).

## Definitions

For an open subgroup `K` of a group `G`, a subgroup `N` and `g ∈ G`:

- `conjRadicalPiece K N g` is the subgroup `g (K ∩ N) g⁻¹`, the image of `K ∩ N`
  under conjugation by `g`;
- `iwahoriIndex K N g : ℕ` is the relative index of `g (K ∩ N) g⁻¹` in `K ∩ N`
  (`Subgroup.relIndex`), that is the index in `K ∩ N` of
  `(g (K ∩ N) g⁻¹) ∩ (K ∩ N)` (the value is `0` if that index is infinite). When
  `g (K ∩ N) g⁻¹ ⊆ K ∩ N` it is `[K ∩ N : g (K ∩ N) g⁻¹]`;
- `centralCell K g` is the image of the double coset `K g K` in
  `G ⧸ Subgroup.center G`;
- `cellTranslate K N g q` (an `abbrev`) is the class in `G ⧸ Z(G)` of `r g`,
  where `r = q.out` is the chosen representative of a left coset `q` of
  `g (K ∩ N) g⁻¹` in `K ∩ N`.

In Renard's notation (proof of VII.1.2, printed pp.222–223 / PDF pp.228–229),
with `K_N = K ∩ N`, the index `[K_{m⁻¹Nm} : K_N]` equals
`[K_N : m K_N m⁻¹] = iwahoriIndex K N m`, by conjugating with `m`.

## Results

Throughout, `K` has an Iwahori factorization
`K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`, factorization in `Nbar · M · N` is unique, the full
center `Z(G)` is contained in `M`, `M` normalizes `N` and `Nbar`, `g` commutes
with every element of `M`, and `g` is a weak Iwahori contraction
(`WeakIwahoriBasis.lean`).

- `conjRadicalPiece_le`: `g (K ∩ N) g⁻¹ ⊆ K ∩ N` (the `upper` field).
- `inv_mul_mem_conjRadicalPiece_of_eq`: if `u g k = u' g k' z` with
  `u, u' ∈ K ∩ N`, `k, k' ∈ K` and `z` central, then `u'⁻¹ u ∈ g (K ∩ N) g⁻¹`.
  Proof: factor `k' k⁻¹ = l m v` and conjugate by `g`. This writes `u'⁻¹ u`, an
  element of `N`, as `(g l g⁻¹)(m z)(g v g⁻¹)` with factors in `Nbar`, `M`, `N`.
  Uniqueness of factorization gives `u'⁻¹ u = g v g⁻¹` with `v ∈ K ∩ N`.
- `centralCell_eq_iUnion`: the image of `K g K` in `G ⧸ Z(G)` is the union over
  the cosets `q` of `cellTranslate K N g q • (image of K)`. For `k g k'`, factor
  `k⁻¹ = l m u`. Then `k = u⁻¹ m⁻¹ l⁻¹`. Write `u⁻¹ = r (g v g⁻¹)` with `r`
  the chosen representative of its coset. Since `g⁻¹ l⁻¹ g ∈ K` (the `lower`
  field) and `m` commutes with `g`, we get
  `k g k' = r g · (v m⁻¹ (g⁻¹ l⁻¹ g) k')`, where the second factor is in `K`.
- `cellTranslate_disjoint`: translates by different cosets are disjoint, by the
  previous criterion applied to the representatives.
- `conjRadicalPiece_mul`, `iwahoriIndex_mul`: for weak contractions `a, b`,
  `iwahoriIndex K N (a * b) = iwahoriIndex K N b * iwahoriIndex K N a`. This
  follows from the tower `ab(K∩N)(ab)⁻¹ ⊆ a(K∩N)a⁻¹ ⊆ K∩N`, multiplicativity of
  relative indices, and invariance of the index under conjugation by `a`.
- `iwahoriIndex_pow_mul`: `iwahoriIndex K N (a ^ m * b) = iwahoriIndex K N b *
  (iwahoriIndex K N a) ^ m`, by induction.
- `centralCell_eq_of_not_disjoint`: two central cells `K x K Z/Z` and `K y K Z/Z`
  that meet are equal. This needs no factorization hypothesis.
- `mem_conjRadicalPiece_iff_of_mem`: for `g` normalizing `N` and `x ∈ N`,
  `x ∈ g (K ∩ N) g⁻¹ ↔ g⁻¹ x g ∈ K`.
- `finite_quotient_conjRadicalPiece`: for `K` compact, `N` closed and `M`
  normalizing `N`, let `g` be a weak contraction, so that
  `g (K ∩ N) g⁻¹ ⊆ K ∩ N`. By the previous lemma this subgroup is
  `{x ∈ K ∩ N | g⁻¹ x g ∈ K}`. It is therefore open in the compact group `K ∩ N`,
  so the coset space `(K ∩ N) ⧸ g (K ∩ N) g⁻¹` is finite.
- `measure_centralCell` (main result): for a Haar measure on `G ⧸ Z(G)` (Borel),
  `K` compact and `N` closed,
  `haar (centralCell K g) = iwahoriIndex K N g * haar (image of K)`. Proof: the
  union decomposition and disjointness above, `measure_iUnion`, invariance of Haar
  measure under left translation (`measure_smul`), and `tsum` of a constant over
  the finite coset space, whose cardinality is the index.

## Provenance

Derived. This is the volume computation in the proof of Renard VII.1.2 (printed
pp.222–223 / PDF pp.228–229): "`KmK = m K_{m⁻¹Nm} K`", hence
"`μ_G(KmK) = [K_{m⁻¹Nm} : K_N] μ_G(K)`". The Lean version works on the actual
quotient `G ⧸ Z(G)`, which is where the published square-integrability predicate
`IsSquareIntegrableModCenter` takes its Haar measure. Renard uses `G/C_{A_G}`.
The center enters only through the hypothesis `Z(G) ≤ M` and the uniqueness of
factorization. Renard's elements `m ∈ M⁺` are replaced by weak contractions `g`.
Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`;
PDF page = printed page + 6).
