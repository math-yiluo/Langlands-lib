# The torsion-hyperplane count from four published geometric statements

Lean module: `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundAssembly`,
namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`.

Author: Worker 3523.

## Role and provenance

This module is the conditional assembly for task `a76410a4-bece-4011-b3f8-7d87460be52c`
(Task 3523). That task proves the published
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`.
It concerns an algebraically closed field `K`, a datum `a` with `0 < g`, `0 < d`, `0 < n` and
`(n : K) ≠ 0`, and a closed immersion `i` of the abelian variety into `ℙᵐ_K` over `Spec K`
with `i^* 𝒪(1) ≅ M`, where `M = a.cubicBundle`. Assume that no nonzero linear form vanishes
on the whole image of `i`. Then for every nonzero linear form `f`, at most
`6^g · d · g! · n^(2g-2)` of the `n`-torsion `K`-sections have their point on the hyperplane
`f = 0`.

The source is Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd edition (1994),
proof of Proposition 7.7, printed pp.138–139 (PDF pp.151–152). Definition 7.5 and the
discussion after it, printed pp.130–131 (PDF pp.143–144), give the Hilbert polynomial
`6^g · d · T^g` of the cubic embedding. The source is registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.

The Library module `TorsionHyperplaneBezoutReduction` proves
`cubicTorsionHyperplaneBound_of_symmetricPullback`. That theorem derives the target from two
premises:

- `hB`, the published `Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement`;
- `hA`, the equation `(lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g).coeff g =
  6^g * d` for every datum `a` over an algebraically closed field with `0 < g` and `0 < d`.

This module derives `hA` from three more published statements. So the target follows from
four published statements. Each has its own proof task, and none has a published proof yet:

| Premise | Published statement | Proof task |
| --- | --- | --- |
| `hB` | `Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement` | `4db6f774-722f-405b-aeaa-8ab052f17c14` (Task 537) |
| `hS` | `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement` | `981f6bcb-41de-4a08-83b8-48b6eec2b236` (Task 3649) |
| `hI` | `Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement` | `c430e7e4-f317-40b4-8a98-6a3180453c97` (Task 3607) |
| `hC` | `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement` | `baec6a6d-fe08-417e-95fd-fb8e2291cb1d` (Task 3488) |

All four are used unchanged at the universe `u` of the target. This module does not prove
the target statement and does not assert any premise. When the four proofs are in the
Library, the target follows by applying `cubicTorsionHyperplaneBoundReduction` to them.

What the premises say:

- `hB`: on an abelian variety over a field, if a line bundle `L` satisfies `[-1]^* L ≅ L`,
  then `[n]^* L ≅ L^(n·n)` for every `n > 0`.
- `hS`: for an ample `H` on a `g`-dimensional abelian variety over an algebraically closed
  field, an inverse `N` of `H`, `k ≥ 1` and an inverse `Nk` of `H^k`,
  `χ(H^k) · χ(Nk) = k^(2g) · χ(H) · χ(N)`.
- `hI`: on such an abelian variety, if `N ⊗ M ≅ 𝒪`, then `χ(M) = (-1)^g · χ(N)`.
- `hC`: for a datum `a` over an algebraically closed field with `0 < d`,
  `Hⁱ(A, a.cubicBundle) = 0` for `i > 0` and `dim_K H⁰(A, a.cubicBundle) = 6^g · d`.

Here `χ` is the Library's `eulerCharacteristic` of the structure morphism, and `L^k` is
`tensorPow L.obj k`.

## Declarations

- `Datum.lineBundle_hasFiniteCohomology a L`: every line bundle `L` on the abelian variety of
  a datum `a` over a field has finite cohomology. This is the Library theorem
  `smoothProperLineBundleFiniteCohomology`, since the structure morphism is smooth and proper.
- `Datum.cubicBundle_eulerCharacteristic_tensorPow_sq hS hI a k hk hM hMk`: under `hS`, `hI`
  and `IsAlgClosed K`, `χ(M^k)^2 = k^(2g) · χ(M)^2` for `M = a.cubicBundle` and `k > 0`.
- `Datum.cubicBundle_eulerPolynomial_coeff_of_fibreInputs hS hI hC hd a`: under `hS`, `hI`,
  `hC`, `IsAlgClosed K` and `0 < d`, the degree-`g` coefficient of
  `lineBundleEulerPolynomial a.abelian.X.hom a.cubicBundle g` is `6^g · d`. This is the
  premise `hA` above.
- `cubicTorsionHyperplaneBound_of_fibreInputs hB hS hI hC`: the target
  `CubicTorsionHyperplaneBoundStatement.{u}` from the four premises.
- `CubicTorsionHyperplaneBoundReductionStatement`: the proposition
  `FieldSymmetricMultiplicationPullbackStatement → AlgClosedFieldAmpleEulerInverseScalingStatement →
  AlgClosedFieldEulerInverseSymmetryStatement → CubicFibreCohomologyStatement →
  CubicTorsionHyperplaneBoundStatement`, all at universe `u`. It is internal: it records
  exactly what this module proves, so the reduction can be reviewed as a statement before the
  premises are proved. It is not the target statement.
- `cubicTorsionHyperplaneBoundReduction`: proves the reduction statement. It is
  `cubicTorsionHyperplaneBound_of_fibreInputs`.

## Proofs

Throughout, `a` is a datum over `K`, `A = a.abelian`, and `M = a.cubicBundle`.
`a.dimension` says that `A` has relative dimension `g`, and `a.cubicBundle_isAmple` (Library,
unconditional) says that `M` is ample.

### `Datum.cubicBundle_eulerCharacteristic_tensorPow_sq`

Let `k > 0`. Every line bundle has an inverse: by `LineBundle.exists_tensorObj_iso_structureSheaf`
choose `N` with `M ⊗ N ≅ 𝒪` and `Nk` with `M^k ⊗ Nk ≅ 𝒪` (`M^k` is a line bundle by
`tensorPow_isLocallyFreeRankOne`). Both have finite cohomology by
`Datum.lineBundle_hasFiniteCohomology`. Write `x = χ(M^k)` and `y = χ(M)`. Then:

1. `hS` with `H = M` gives `x · χ(Nk) = k^(2g) · (y · χ(N))`.
2. `hI` with the pair `(M, N)` gives `χ(N) = (-1)^g · y`.
3. `hI` with the pair `(M^k, Nk)` gives `χ(Nk) = (-1)^g · x`.
4. `(-1)^g · (-1)^g = 1`.

Substituting 2 and 3 into 1 and multiplying by `(-1)^g` gives `x^2 = k^(2g) · y^2`. In Lean
this is one `linear_combination` of the four equations.

### `Datum.cubicBundle_eulerPolynomial_coeff_of_fibreInputs`

1. `A.X.left` is Noetherian and separated (`field_isNoetherian`, `field_isSeparated`), and its
   topological Krull dimension is at most `g` (`field_topologicalKrullDim a.dimension`).
2. `hC` gives the vanishing of `Hⁱ(A, M)` for `i > 0` and `dim_K H⁰(A, M) = 6^g · d`. The
   last part of `eulerCharacteristicBasic` (Euler characteristic of a module with no higher
   cohomology) then gives `χ(M) = 6^g · d`.
3. Apply the Library theorem `lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq`
   with `c = 6^g · d`. Its first hypothesis, `χ(M^k)^2 = c^2 · k^(2g)` for `k > 0`, follows
   from `Datum.cubicBundle_eulerCharacteristic_tensorPow_sq` and step 2. Its second
   hypothesis, `χ(M^1) ≥ 0`, follows from step 2 and the isomorphism `M^1 ≅ M`
   (`tensorPowOneIso`, `eulerCharacteristic_eq_of_iso`).
4. The theorem gives that the degree-`g` coefficient is `6^g · d`, as an integer, which is the
   claim after a cast.

### `cubicTorsionHyperplaneBound_of_fibreInputs`

Apply `cubicTorsionHyperplaneBound_of_symmetricPullback hB`. Its premise `hA` is supplied, for
each datum with `0 < d`, by `Datum.cubicBundle_eulerPolynomial_coeff_of_fibreInputs hS hI hC`.
The hypothesis `0 < g` of `hA` is not needed.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
