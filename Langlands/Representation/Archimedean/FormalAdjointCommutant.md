# Schur's lemma for operators with a formal adjoint

Module `Langlands.Representation.Archimedean.FormalAdjointCommutant`, namespace
`Langlands.Archimedean.FormalAdjointCommutant`.

Let `G` be a group, `E` a complex Hilbert space and `ρ : G →* (E →L[ℂ] E)` a representation with
`⟪ρ g u, ρ g w⟫ = ⟪u, w⟫` that is topologically irreducible
(`Langlands.Archimedean.IsTopologicallyIrreducible`). Let `W` be a nonzero subspace of `E` with
`ρ g W ⊆ W` for all `g`. No continuity of `ρ` in `g` is used.

## Declarations

- `dense_of_invariant`: a nonzero `ρ`-invariant subspace is dense. Its closure is closed,
  invariant (`map_mem_closure`) and nonzero, hence equal to `E`.
- `eq_of_inner_dense`: two vectors with the same inner products against a dense subspace are
  equal. The set `{u | ⟪u, x - y⟫ = 0}` is closed and contains `W`.
- `inner_map_right`: `⟪x, ρ g y⟫ = ⟪ρ g⁻¹ x, y⟫`, from unitarity applied to `ρ g⁻¹ x` and `y`.
- `exists_eq_smul_of_symmetric_commute`: a linear `S : W → W` with `⟪S v, w⟫ = ⟪v, S w⟫` and
  `S (ρ g w) = ρ g (S w)` on `W` is a scalar on `W`.
- `exists_eq_smul_of_formalAdjoint_commute`: a linear `D : W → W` that has a formal adjoint
  `D' : W → W` (`⟪D v, w⟫ = ⟪v, D' w⟫` for `v, w ∈ W`) and commutes with every `ρ g` on `W` is
  a scalar on `W`: there is `c : ℂ` with `D w = c • w` for every `w ∈ W`.

## Proofs

*Symmetric case.* Put `T = S - i`. For `w ∈ W`, `⟪S w, w⟫` is real, so
`‖T w‖² = ‖S w‖² + ‖w‖² ≥ ‖w‖²` (`norm_sub_sq`). The range of `T` is `ρ`-invariant, because `T`
commutes with `ρ`, and nonzero, because `W ≠ 0` and `T` is injective; by `dense_of_invariant` it
is dense. The map `T w ↦ w` is therefore well defined with norm at most one on a dense subspace,
and `LinearMap.extendOfNorm` extends it to a bounded operator `R` of `E` with `R (T w) = w`.
`R ∘ ρ g` and `ρ g ∘ R` are continuous and agree on the range of `T`, so `R` commutes with `ρ`
(`DenseRange.equalizer`). The bounded Schur lemma `exists_eq_scalar_of_unitary_commute` gives
`R = c • id`. Then `w = c • T w` for `w ∈ W`; since `W ≠ 0`, `c ≠ 0`, and
`S w = (c⁻¹ + i) • w`.

*General case.* The reversed relation `⟪D' v, w⟫ = ⟪v, D w⟫` follows by conjugate symmetry.
`D'` commutes with `ρ`: for `x ∈ W`,
`⟪x, D' (ρ g w)⟫ = ⟪D x, ρ g w⟫ = ⟪ρ g⁻¹ (D x), w⟫ = ⟪D (ρ g⁻¹ x), w⟫ = ⟪x, ρ g (D' w)⟫`,
and `eq_of_inner_dense` concludes. The operators `S₁ = D + D'` and `S₂ = i (D - D')` on `W` are
symmetric and commute with `ρ`, so `S₁ = a` and `S₂ = b` by the symmetric case, and
`2 D = S₁ - i S₂` gives `D = (a - i b) / 2`.

## Provenance

This is the form of Schur's lemma behind Segal's theorem that the center of the enveloping
algebra acts by scalars on an irreducible unitary representation (Harish-Chandra, *Representations
of a semisimple Lie group on a Banach space I*, Trans. AMS 75 (1953), §11, citing Segal and
Mautner). The classical argument takes the closure of an unbounded operator and uses that
`(1 + T*T)⁻¹` is bounded; the implemented proof uses only the bounded inverse of `S - i` on a dense
invariant subspace and needs no theory of unbounded operators.
