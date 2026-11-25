# Self-dual subgroups: the regular representation and the orthogonal of a set

**GKT §1.2.1** (the dual `A^⊥` of a subgroup, (1.2), p. 18; self-dual subgroups and the extension
`ψ_A` of `ψ`, Lemma 1.3 and Corollary 1.4, p. 19).

The module `Langlands.Theta.Heisenberg.SelfDual` holds the general part of the construction of the
induced models of the Heisenberg representation: the representation on all functions on `W`
induced from the central character, the orthogonal of a set for the pairing `ψ ∘ B`, and the
translation of these notions into the abstract setting of
`Langlands.Theta.Heisenberg.SelfDualSubgroup`.

## Content

Let `R` be a commutative ring with `⅟2`, `W` an `R`-module, `B` a bilinear form and `ψ` an
additive character of `R`.

- **The regular representation.** `regular B ψ` is the representation of `HeisenbergGroup B` on
  all functions on `W` induced from the character `ψ` of the centre: `(w, t)` acts by
  `f ↦ (z ↦ ψ t · ψ(½ B(z, w)) · f(z + w))`, that is `ψ t • regularFun B ψ w`. It has central
  character `ψ` (`hasCentralCharacter_regular`). The induced models of GKT Definition 1.6 are
  realized inside it (GKT p. 29 uses the same realization on functions on `W` for the lattice
  model).
- **Orthogonals.** `charOrthogonal B ψ T = {x | ψ(B(x, t)) = 1 for t ∈ T}`, the book's `T^⊥`
  ((1.2)); a subgroup `A` is self-dual when `charOrthogonal B ψ A = A`.
- **The bicharacter.** For alternating `B`, `(x, y) ↦ ψ(½ B(x, y))` is an alternating bicharacter
  (`isAlternatingBicharacter_psi`, with `ψ(½ t)² = ψ t`, `psi_half_sq`) whose orthogonals are the
  sets `charOrthogonal B ψ T` (`orthogonal_psi_eq`), and in a representation with central
  character `ψ` the elements `(x, 0)` act by a projective representation of `W` with this cocycle
  (`isProjectiveRep_of_hasCentralCharacter`).
- **Subspaces.** Over a field, for a subspace `L` and a non-trivial `ψ`, `x ∈ charOrthogonal B ψ L`
  if and only if `B(x, l) = 0` for all `l ∈ L` (`mem_charOrthogonal_submodule`: if `B(x, l) ≠ 0`,
  then `ψ(t) = ψ(B(x, (t / B(x, l)) l)) = 1` for all `t`). So a self-dual subspace is a Lagrangian
  (its own `B`-orthogonal), the case of the Schrödinger model (GKT §1.2.2, p. 25).

## Source and licence

This file and `Langlands.Theta.Heisenberg.InducedModel` hold the text of lines 357–541 and
555–646 of `src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`; this file
holds `funRep`, `transl` (as `regularFun`), `alt_psi`, `psi_sq` and `ops_of_central`. The
repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.Published.SvN` → `Langlands.HeisenbergGroup`; `(2 : F) ≠ 0` and `/ 2`
  → `[Invertible (2 : R)]` and `⅟2 *`; any commutative ring in place of a local field.
- `funRep hB ψ` → `regular B ψ`, without the hypothesis `hB` (the representation property uses
  only bilinearity); `transl` with `c = ψ(B/2)` → `regularFun B ψ`; `alt_psi` →
  `isAlternatingBicharacter_psi`; `psi_sq` → `psi_half_sq`; `ops_of_central` →
  `isProjectiveRep_of_hasCentralCharacter`.
- New: `charOrthogonal` (the source used the orthogonal of the internal bicharacter, which
  coincides with it by `orthogonal_psi_eq`), `mem_charOrthogonal`, `regularFun_zero`,
  `regularFun_mul`, `regular_apply`, `regular_ofVec`, `orthogonal_psi_eq`,
  `mem_charOrthogonal_submodule`.

## Declarations

- `regularFun`, `regularFun_apply`, `regularFun_zero`, `regularFun_mul`, `regular`,
  `regular_apply`, `regular_ofVec`, `hasCentralCharacter_regular`.
- `charOrthogonal`, `mem_charOrthogonal`, `isAlternatingBicharacter_psi`, `psi_half_sq`,
  `orthogonal_psi_eq`, `isProjectiveRep_of_hasCentralCharacter`.
- `mem_charOrthogonal_submodule`.

## Dependencies

`Langlands.Theta.Heisenberg.Representation`, `Langlands.Theta.Heisenberg.SelfDualSubgroup`.
