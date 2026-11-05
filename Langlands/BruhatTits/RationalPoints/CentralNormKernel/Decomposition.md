# Spectral decomposition of a finite commutative algebra over an algebraically closed field

Author: Worker 1532.

Namespace: `Langlands.BruhatTits.RationalPoints.CentralNormKernel`. Internal helper for the
proof of `CentralNormKernelCompactnessStatement` (see
[CentralNormKernelCompactnessProof](../CentralNormKernelCompactnessProof.md)). This is standard
commutative algebra (the structure of Artinian rings), stated in the form the proof uses.

## Existence

`exists_spectralDecomposition K B`: let `K` be an algebraically closed field and `B` a
commutative `K`-algebra that is finite as a `K`-module. Then there are `r : ℕ`, elements
`e : Fin r → B` and `K`-algebra maps `χ : Fin r → (B →ₐ[K] K)` such that

- `e` is a complete family of orthogonal idempotents (`CompleteOrthogonalIdempotents e`);
- every `e i` is nonzero;
- for every `i` and `x : B`, `(x - χ i x) * e i` is nilpotent.

Proof. `B` is Artinian (`IsArtinianRing.of_finite`). Mathlib's
`IsArtinianRing.quotNilradicalEquivPi` identifies `B ⧸ nilradical B` with the product of the
fields `B ⧸ m` over the maximal ideals `m`. The idempotents `Pi.single m 1` of the product are
lifted to `B` along the quotient map, whose kernel is the nilradical, by
`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`. Each field `B ⧸ m` is finite over `K`,
so `algebraMap K (B ⧸ m)` is bijective (`IsAlgClosed.algebraMap_bijective_of_isIntegral`); `χ m`
is reduction modulo `m` followed by the inverse of this bijection. The lifted idempotent at `m`
maps to `Pi.single m 1`, which is nonzero. Finally `(x - χ m x) e_m` maps to zero in every factor
`B ⧸ m'`: for `m' ≠ m` because the idempotent vanishes there, and for `m' = m` by the definition
of `χ m`. Hence it lies in the nilradical. The index type is reindexed by `Fin r`.

## The structure `SpectralData`

`SpectralData K B` bundles `r`, `e`, `χ` and the three properties above.
`nonempty_spectralData` packages the existence theorem. For `D : SpectralData K B` the module
defines and proves, for any field `K` and commutative `K`-algebra `B`:

- `D.diag t = ∑ i, t i • e i` for `t : Fin r → K`; `diag_mul_e`, `diag_mul` (`diag t * diag t' =
  diag (t * t')`), `diag_const`, `diag_one`, and `isUnit_diag` when all `t i ≠ 0`.
- `D.semisimplePart x = D.diag (fun i => χ i x)`; `sub_semisimplePart` and
  `isNilpotent_sub_semisimplePart`: `x - semisimplePart x` is a sum of the nilpotents
  `(x - χ i x) e i` in a commutative ring, hence nilpotent.
- `isUnit_sub_algebraMap`: if `χ i x ≠ μ` for all `i`, then `x - μ` is a unit, being a unit
  `diag (χ · x - μ)` plus a commuting nilpotent.
- `χ_ne_zero_of_isUnit`, `χ_eq_one_of_isNilpotent` (if `x - 1` is nilpotent then `χ i x = 1`).
- `D.block x i = x * e i + (1 - e i)`, with `block_sub_mul_e` and `isUnit_block_sub` (for
  `μ ≠ χ i x` and `μ ≠ 1`); `isUnit_idempotent_combination` is the elementary fact that
  `a e + b (1 - e)` is a unit for an idempotent `e` and nonzero scalars.

Matrix consequences, for an injective `K`-algebra map `ψ : B →ₐ[K] Matrix n n K`:

- `isNilpotent_of_map`: nilpotence reflects along `ψ`.
- `exists_eq_of_isRoot`: every root `c` of the characteristic polynomial of `ψ x` equals some
  `χ i x` (otherwise `ψ x - c` is a unit, so `c` is not in the spectrum).
- `isRoot_charpoly_χ`: every `χ i x` is a root of the characteristic polynomial of `ψ x`. If
  `ψ x - χ i x` were a unit, then `ψ (e i)` would be nilpotent, being a commuting unit multiple
  of the nilpotent `ψ ((x - χ i x) e i)`; an idempotent nilpotent is zero, contradicting
  `e i ≠ 0` and injectivity.
- `det_block` (for `K` algebraically closed): `det (ψ (block x i)) = χ i x ^ a` for some
  `1 ≤ a ≤ card n`. Every eigenvalue of `ψ (block x i)` is `χ i x` or `1`, by
  `isUnit_block_sub`; the determinant is the product of the eigenvalues
  (`Matrix.det_eq_prod_roots_charpoly`, `multiset_prod_eq_pow_count` from
  `GroupScheme.Derived.CentralIntersection.LinearAlgebra`). If `χ i x ≠ 1`, it is an eigenvalue
  by the same nilpotence argument as above, so the exponent is positive; if `χ i x = 1`, take
  `a = 1` (here `n` is nonempty because `e i ≠ 0`).
