# Separating a vector from a subrepresentation by the dual principal series

Module: `Langlands.Representation.Archimedean.RealJacquetSeparation` (namespace
`Langlands.Archimedean.RealJacquetSeparation`).

Main theorem: `Langlands.Archimedean.RealJacquetSeparation.exists_orthogonal_pairing_ne_zero`.

## Purpose and provenance

This is a helper module for the proof of
`Langlands.Archimedean.RealJacquetNonvanishingSubquotientReductionStatement`
(module `RealJacquetNonvanishingProof`). Casselman's argument needs a dual vector that kills
the kernel of the subquotient map but not a chosen vector. The statement is internal to this
formalization. It is derived from the Library's block decomposition of admissible
`O(n)`-representations (`Langlands.Representation.KFiniteDual`), the admissibility of real
standard modules (`realStandardAdmissible`), their `(𝔤, K)`-module structure
(`isRealGKModule_realStandardModule`), and the pairing `RealPrincipalSeriesDuality.pairing`.

## Declarations

- `KF n ds`: abbreviation for the `O(n)`-finite functions
  `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`.
- `pairing_rep_inv`: `pairing (ρ(k⁻¹) f) ψ = pairing f (ρ'(k) ψ)` for the right-translation
  representations `ρ = realStandardRep n ds`, `ρ' = realStandardRep n ds'`. This uses right
  invariance of `haarK` (`integral_mul_right_eq_self`).
- `dualOf ds ds' : KF n ds' →ₗ Dual (KF n ds)`, `ψ ↦ pairing (·) ψ`. `dual_dualOf`: it
  intertwines `ρ'` with the dual representation `ρ.dual`. `isFiniteVector_dualOf`: its values
  are `O(n)`-finite (the orbit of `dualOf ψ` lies in the image of the finite-dimensional
  orbit span of `ψ`).
- `representedSub ds ds'`: the range of `dualOf ds ds'`, a subrepresentation of `ρ.dual`.
- `exists_orthogonal_pairing_ne_zero`: assume that the pairing separates the points of `KF n ds`
  (`∀ f ≠ 0, ∃ ψ, pairing f ψ ≠ 0`). Let `N` be a subrepresentation of `realStandardRep n ds`
  and `w ∉ N`. Then some `ψ ∈ KF n ds'` has `pairing f ψ = 0` for all `f ∈ N` and
  `pairing w ψ ≠ 0`.

## Proof of `exists_orthogonal_pairing_ne_zero`

`realStandardRep n ds` is semisimple (`KFiniteDual.isSemisimpleModule`, from the first two
clauses of `IsRealGKModule`), and its blocks are finite-dimensional
(`finiteDimensional_block`, from `realStandardAdmissible`).

1. Write `w = ∑_c proj c w` over finitely many blocks (`exists_finset_proj`). Some component
   `proj c w` is not in `N`, since otherwise `w ∈ N`.
2. Block projections preserve `N` (`proj_mem_of_mem`). In the finite-dimensional block `c`,
   choose a functional `φ` that vanishes on `N ∩ block` and is nonzero at `proj c w`
   (`Submodule.exists_dual_map_eq_bot_of_notMem`). Put `ℓ = φ ∘ projTo c`. It is an
   `O(n)`-finite functional (`isFiniteVector_comp_projTo`) with `ℓ(N) = 0` and `ℓ(w) ≠ 0`.
3. `representedSub ds ds'` consists of `O(n)`-finite functionals and separates points by
   hypothesis. So it contains every `O(n)`-finite functional (`KFiniteDual.mem_of_separating`),
   in particular `ℓ = pairing (·) ψ` for some `ψ`. This `ψ` has the required properties.
