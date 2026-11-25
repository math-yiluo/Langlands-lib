# Lattices spanned by a normal basis

`Langlands/GaloisCohomology/Local/Arithmetic/NormalLattice.lean`, namespace `Langlands.GaloisCohomology.Local`.

For a finite Galois extension `L/K` of nonarchimedean local fields and a normal basis element
`θ`, the `𝒪[K]`-lattices `normalLattice π θ s = πˢ · Σ_σ 𝒪[K] σ(θ)` are stable under `Gal(L/K)`,
open, and form a neighbourhood basis of `0`; there is a normal basis element with all conjugates
integral. These lattices are free `𝒪[K][Gal(L/K)]`-modules of rank one and are used to compute
the units of `L` as a Galois module (`EulerCharacteristic/Units.lean`).

## Declarations

- `normalLattice π θ s` (a Mathlib `Submodule.span`), `mem_normalLattice_iff`,
  `smul_sum_mem_normalLattice`, `coeff_injective` (coefficients in the normal basis are unique),
  `normalLattice_antitone`, `pow_smul_mem_normalLattice`.
- `algEquiv_smul_sum`, `algEquiv_mem_normalLattice`: Galois stability.
- `mem_integer_of_mem_normalLattice`; `exists_pow_mul_mem_integer`,
  `exists_pow_smul_mem_normalLattice`, `exists_pow_smul_mul_mem_normalLattice`,
  `mul_mem_normalLattice`, `mul_mem_normalLattice_succ`.
- Completeness: `smodEq_iff_pow_dvd`, `exists_limit_of_pow_dvd`, `eq_zero_of_forall_pow_dvd`,
  `eq_zero_of_forall_mem_normalLattice`, `exists_limit_normalLattice`, `exists_inv_one_add`,
  `exists_unit_one_add`.
- `exists_normalBasis_integer hπ`: a normal basis element with integral conjugates;
  `isOpen_normalLattice`: the lattices are open.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/LocalFields/NormalLattice.lean`, with the names
unchanged. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J.-P. Serre, *Galois Cohomology*, chapter II, §5.7, proof of Lemma 5 (the normal basis theorem
  applied to the principal units; for `p`-adic fields), p. 101.
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §3, proof of
  Theorem (7.3.2) (a normal basis of the extension), p. 394.
