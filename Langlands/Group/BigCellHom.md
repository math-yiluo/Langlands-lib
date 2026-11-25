# Homomorphisms from relations on a big cell

The module `Langlands.Group.BigCellHom` constructs a group homomorphism from its restriction to a
subgroup and its value at one element, given the relations visible on the "big cell" `P w P`.

## Content

`Langlands.Group.exists_monoidHom_of_bigCell_relations`: let `G`, `H` be groups, `P` a subgroup of
`G` and `w ∈ G` such that every finite subset of `G` has a common right translate into `P w P`. Let
`ρ : P →* H` and `W ∈ H` satisfy

- if `w p = q w` (`p, q ∈ P`), then `W ρ(p) = ρ(q) W`;
- if `w p w ∈ P w P`, then there are `p₁, p₂ ∈ P` with `w p w = p₁ w p₂` and
  `W ρ(p) W = ρ(p₁) W ρ(p₂)`.

Then there is `Φ : G →* H` with `Φ = ρ` on `P` and `Φ(w) = W`.

Proof. On the big cell put `f(p₁ w p₂) = ρ(p₁) W ρ(p₂)`; this is well defined by the first relation
and satisfies `f(x y) = f(x) f(y)` whenever `x`, `y`, `x y` lie in the big cell, by the second. A
function multiplicative on such a "chunk" `C` of which every finite set has a common translate
extends to a homomorphism, `Φ(g) = f(g u) f(u)⁻¹` for any `u` with `u, g u ∈ C`, independent of `u`
(internal lemma `groupChunk_extend`).

For `G = U(ν, ν)`, `P` its Siegel parabolic subgroup and `w` the Weyl element, the translation
hypothesis is `UnitaryGroup.exists_mul_isInBigCell` (`Langlands/Group/Unitary/BigCell.lean`). This is
how the Weil representation of `U(ν, ν)` is defined from explicit operators on `P` and at `w`
(`Langlands/Theta/DualPair/Unitary/Splitting.lean`). Kudla, *Splitting metaplectic covers of dual
reductive pairs*, Israel J. Math. 87 (1994), 361–401, obtains the splitting differently: a function
`β_V` on each Bruhat cell `P τ_j P` trivializes Rao's cocycle (§1.2, (1.11), p. 370; Theorem 3.1 and
Corollary 3.3, pp. 378–380), and the resulting operators of the Schrödinger model are written in §5,
pp. 399–400.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomOfBigCellGenericRelations.lean`,
lines 11–126 (`groupChunk_extend`, `bigCell_hom`). The repository has no licence file; the text is
used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory` → `Langlands.Group` (public) and `Langlands.Group.BigCellHom.Internal`
  (`groupChunk_extend`).
- `bigCell_hom` (stated with `∀ (G H : Type)`) and its wrapper
  `GlobalTheory.T.exists_hom_of_bigCell_generic_relations` → `exists_monoidHom_of_bigCell_relations`,
  with named hypotheses and `G`, `H` in any universe.

## Declarations

- `Langlands.Group.exists_monoidHom_of_bigCell_relations`

## Dependencies

Mathlib: `Algebra.Group.Subgroup.Basic`, `Data.Finset.Insert`, `Tactic.Group`.
