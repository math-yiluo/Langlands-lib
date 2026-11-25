# Exact degree-six tensor-cube nonsplitting target

`Langlands.CentralSimple.centralDivisionDegreeSixTensorCubeNonSplit` proves
the unchanged published proposition
`Langlands.CentralSimple.CentralDivisionDegreeSixTensorCubeNonSplitStatement.{u}`,
imported from `Langlands.Algebra.CentralSimple.CentralDivisionTensorCubeStatement`,
for every universe parameter `u`. Its type is exactly that proposition. For
every field `k` and every finite-dimensional central division algebra `D/k`
with `Module.finrank k D = 36`, both in `Type u`, the actual algebra
`(D ⊗[k] D) ⊗[k] D` is not `k`-algebra isomorphic to
`Matrix (Fin n) (Fin n) k` for any positive `n`. No restriction is placed on
the characteristic.

## Proof

The proof introduces the field, the algebra and its instances, the dimension
hypothesis `hdim`, the matrix size `n` and its positivity hypothesis. It then
applies `Langlands.CentralSimple.centralDivision_degree_six_tensorCube_not_split hdim n`
from `Langlands.Algebra.CentralDivisionTensorCubeNonSplit`. That theorem gives
the stronger conclusion for every natural matrix size `m`, so the positivity
hypothesis is not used. Only the standard axioms `propext`, `Classical.choice`
and `Quot.sound` are used.

The supporting theorem and its helper modules are
`CentralDivisionTensorCubeNonSplit`, `SylowTwoOddSplitting`,
`FixedFieldScalarDefect`, `TensorCubeScalarDefect` and
`DivisionSplittingDegree`, all under `Langlands/Algebra/`, each with its own
Markdown. They build on the published modules `ScalarTwoCocycleTorsion`,
`ScalarTwoCocycleLifts`, `MatrixGaloisCocycle`, `MatrixSplitDefect`,
`MatrixGaloisSplitting`, `SplittingChartGaloisAction`,
`TensorProductSplittingCharts` and `CentralSimple.FiniteGaloisSplitting`.
The argument runs as follows:

1. Choose the published actual finite Galois splitting field `L/k` of `D` with
   its matrix chart `L ⊗[k] D ≃ₐ[L] Matrix (Fin 6) (Fin 6) L`. Dimension 36
   forces size six.
2. By counting dimensions, a hypothetical splitting of the tensor cube has size
   216. Reindex it to the product index `(Fin 6 × Fin 6) × Fin 6`.
3. Compare the tensor and Kronecker charts (`TensorCubeScalarDefect`). This
   yields a scalar cochain that trivializes the cube of the chart's scalar
   two-cocycle defect.
4. Restrict to a Sylow two-subgroup of the Galois group (`SylowTwoOddSplitting`).
   The explicit group-order product cochain and a Bezout identity
   (`ScalarTwoCocycleTorsion`, `FixedFieldScalarDefect`) trivialize the
   restricted defect. This gives an actual matrix splitting of `D` over the
   subgroup's fixed field, which has odd degree over `k`.
5. An actual splitting field of a degree-six division algebra has degree
   divisible by six (`DivisionSplittingDegree`). This contradicts step 4.

The route specializes the Sylow fixed-field argument for the prime support of
index and exponent in Gille and Szamuely, *Central Simple Algebras and Galois
Cohomology* (2006), Proposition 4.5.8, Lemma 4.5.14 and Proposition 4.5.13,
printed pages 103–105 (registered source
`gille-szamuely-central-simple-algebras-galois-cohomology-2006`). The general
index–exponent theorem and the Brauer group law are not assumed.

## Scope

This file proves only the arithmetic proposition. It neither constructs the
Tits obstruction of an E6 or E7 group nor compares it with this tensor cube.
The import closure contains no E6/E7 centre-movement statement, no local
rank-one classification and no local Kneser–Tits result. The published target
pair and its imports are unchanged.
