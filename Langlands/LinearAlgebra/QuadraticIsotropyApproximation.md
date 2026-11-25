# Weak approximation reduces diagonal quadratic isotropy by one variable

The proof follows the higher-dimensional step of Voight,
*Quaternion Algebras*, Theorem 26.8.24, printed p. 451. It decomposes a
diagonal form into its first two coordinates and its tail. The premise
on the tail supplies isotropy outside a finite set of finite places.

At each place in this finite set and at each archimedean place, choose
a nonzero value of the binary part whose addition as a line to the
tail gives an isotropic form. If the tail is anisotropic, the original
isotropic vector gives this value unless its tail coordinates are all
zero. In that case the binary part is isotropic and represents any
value, by the quadratic addition identity along an isotropic vector.
If the tail is isotropic, any nonzero binary value works.

Each completion has an open neighborhood of \(1\) consisting of
squares. At a finite place this follows by solving
\(s^2+s+(1-z)/4=0\) by Hensel's lemma for \(z\) sufficiently close to
\(1\), so \(z=(2s+1)^2\). At real and complex places use real square roots
of positive numbers and algebraic closure of the complex numbers.
The computed binary value therefore remains in the required square class
on an open set of pairs. Weak approximation, applied to the two
coordinates, chooses one global pair satisfying all these local
conditions. The new form is locally isotropic everywhere, and a
nonzero zero of the new form maps to a nonzero zero of the original form
by replacing its first coordinate with its multiple of that global
pair.

`Langlands.QuadraticIsotropy.DiagonalIsotropyRankReductionStatement.{u}`
expresses this step for any nonempty tail. The two coefficients of the
binary part must be nonzero. The premise for the shorter form applies
when the added line has nonzero coefficient, and the tail coefficients
are fixed throughout. `Langlands.QuadraticIsotropy.diagonal_isotropic_of_tail_cofinite`
proves the statement.

Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
The proposition isolates the weak approximation step of Theorem 26.8.24.

## Dependency check

The Lean type-and-value closure of `diagonal_isotropic_of_tail_cofinite`
contains 61,522 constants, including the 134 project declarations below.
It contains none of the three excluded group-cohomology statements or
the corresponding proof prefixes.

<details>
<summary>Lean declaration closure</summary>

```text
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_1
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_2
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_3
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_4
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_5
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap._proof_6
Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap_coe
Langlands.Global.AdelicFunctoriality.FiniteExtension.continuous_completionMap
Langlands.Global.AdelicFunctoriality.FiniteExtension.instAlgebraAdicCompletionRingOfIntegers_langlands
Langlands.Global.AdelicFunctoriality.FiniteExtension.instContinuousSMulAdicCompletionRingOfIntegers_langlands
Langlands.Global.AdelicFunctoriality.FiniteExtension.instIsScalarTowerAdicCompletionRingOfIntegers_langlands
Langlands.Global.AdelicFunctoriality.FiniteExtension.local_finite
Langlands.Global.AdelicFunctoriality.denseRange_algebraMap_mixedAbv
Langlands.Global.AdelicFunctoriality.exists_algebraMap_mem_open
Langlands.Global.AdelicFunctoriality.exists_algebraMap_mem_open.match_1_1
Langlands.Global.AdelicFunctoriality.finiteAdicAbv_isEquiv_iff
Langlands.Global.AdelicFunctoriality.finiteAdicAbv_isEquiv_iff._simp_1_1
Langlands.Global.AdelicFunctoriality.finiteAdicAbv_isEquiv_iff._simp_1_2
Langlands.Global.AdelicFunctoriality.finiteAdicAbv_isNontrivial
Langlands.Global.AdelicFunctoriality.finiteAdicAbv_not_isEquiv_infinitePlace
Langlands.Global.AdelicFunctoriality.finiteWithAbsEmbedding
Langlands.Global.AdelicFunctoriality.finiteWithAbsEmbedding._proof_1
Langlands.Global.AdelicFunctoriality.finiteWithAbsEmbedding_denseRange
Langlands.Global.AdelicFunctoriality.finiteWithAbsEmbedding_isometry
Langlands.Global.AdelicFunctoriality.mixedAbv
Langlands.Global.AdelicFunctoriality.mixedAbv._proof_1
Langlands.Global.AdelicFunctoriality.mixedAbv_isNontrivial
Langlands.Global.AdelicFunctoriality.mixedAbv_pairwise_not_isEquiv
Langlands.Global.CompletionPadic.completion_isModuleTopology
Langlands.Global.CompletionPadic.completion_topology_eq
Langlands.Global.CompletionPadic.continuous_padicMap
Langlands.Global.CompletionPadic.liesOver_rationalPlace
Langlands.Global.CompletionPadic.norm_lt_one_iff_tendsto_pow
Langlands.Global.CompletionPadic.padicAlgebra
Langlands.Global.CompletionPadic.padicField
Langlands.Global.CompletionPadic.padicFinite
Langlands.Global.CompletionPadic.padicMap
Langlands.Global.CompletionPadic.padicMap._proof_1
Langlands.Global.CompletionPadic.padicMap._proof_2
Langlands.Global.CompletionPadic.rationalPlace
Langlands.Global.CompletionPadic.rationalPlace._proof_1
Langlands.Global.CompletionPadic.residuePrime
Langlands.Global.CompletionPadic.residuePrime_fact
Langlands.Global.CompletionPadic.topologicalData
Langlands.Global.CompletionPadic.topologicalData._proof_1
Langlands.Global.CompletionPadic.topologicalData._proof_2
Langlands.Global.CompletionPadic.topologicalData._proof_3
Langlands.Global.CompletionPadic.topologicalData._proof_4
Langlands.Global.CompletionPadic.topologicalData._proof_5
Langlands.Global.CompletionPadic.topologicalData_vle
Langlands.Global.CompletionPadic.valued_isEquiv
Langlands.Global.CompletionPadic.valued_lt_one_iff
Langlands.Global.FiniteCompletion
Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField
Langlands.Global.FiniteCompletion.topologicalData_valuativeRel_eq
Langlands.Global.FiniteCompletion.valuativeRel
Langlands.Global.FinitePlace
Langlands.Global.InfinitePlace
Langlands.Global.Place
Langlands.Global.placeCompletion
Langlands.Global.placeCompletion._proof_1
Langlands.Global.placeCompletion.isField
Langlands.Global.placeCompletion.isField.match_1_1
Langlands.Global.placeCompletion.isTopologicalRing
Langlands.Global.placeCompletion.isTopologicalRing._proof_1
Langlands.Global.placeCompletion.isTopologicalRing._proof_2
Langlands.Global.placeCompletion.isTopologicalRing.match_3
Langlands.Global.placeCompletion.match_1
Langlands.Global.placeCompletion.t2Space
Langlands.Global.placeCompletion.t2Space._proof_1
Langlands.Global.placeCompletion.t2Space._proof_2
Langlands.Global.placeCompletion.topologicalSpace
Langlands.Global.placeCompletion.topologicalSpace._aux_1
Langlands.Global.placeCompletion.topologicalSpace._aux_6
Langlands.Global.placeCompletion.topologicalSpace._proof_10
Langlands.Global.placeCompletion.topologicalSpace._proof_3
Langlands.Global.placeCompletion.topologicalSpace._proof_4
Langlands.Global.placeCompletion.topologicalSpace._proof_5
Langlands.Global.placeCompletion.topologicalSpace._proof_8
Langlands.Global.placeCompletion.topologicalSpace._proof_9
Langlands.LocalQuadraticAnisotropic.exists_root_sq_add_self_add
Langlands.PadicField
Langlands.PadicField.Carrier
Langlands.PadicField.TopologicalData
Langlands.PadicField.TopologicalData.localField
Langlands.PadicField.TopologicalData.mk
Langlands.PadicField.TopologicalData.moduleTopology
Langlands.PadicField.TopologicalData.topology
Langlands.PadicField.TopologicalData.valuativeExtension
Langlands.PadicField.TopologicalData.valuativeRel
Langlands.PadicField.algebra
Langlands.PadicField.canonicalNorm
Langlands.PadicField.canonicalNormedAlgebra
Langlands.PadicField.canonicalNormedField
Langlands.PadicField.canonicalNormedField._proof_1
Langlands.PadicField.canonicalTopologicalData
Langlands.PadicField.canonicalTopologicalData._proof_1
Langlands.PadicField.canonicalTopologicalData._proof_2
Langlands.PadicField.canonicalTopologicalData._proof_3
Langlands.PadicField.canonicalTopologicalData._proof_4
Langlands.PadicField.canonicalTopologicalData._simp_2
Langlands.PadicField.canonicalTopologicalData._simp_3
Langlands.PadicField.canonicalTopologicalData_topology
Langlands.PadicField.canonicalTopologicalData_vle
Langlands.PadicField.canonicalTopology
Langlands.PadicField.canonicalValuation
Langlands.PadicField.canonicalValuation._proof_1
Langlands.PadicField.canonicalValuation_coe
Langlands.PadicField.canonicalValuativeRel
Langlands.PadicField.field
Langlands.PadicField.finiteDimensional
Langlands.PadicField.mk
Langlands.QuadraticIsotropy.DiagonalIsotropyRankReductionStatement
Langlands.QuadraticIsotropy.DiagonalIsotropyRankReductionStatement._proof_1
Langlands.QuadraticIsotropy.DiagonalIsotropyRankReductionStatement._proof_2
Langlands.QuadraticIsotropy.DiagonalIsotropyRankReductionStatement._proof_3
Langlands.QuadraticIsotropy.diagonal_isotropic_of_tail_cofinite
Langlands.QuadraticIsotropy.weightedSumSquares_cons
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.binaryValue
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.binaryValue.eq_1
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.binary_represents_of_isotropic
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.common_nonzero_value
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.cons_eq_zero
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.exists_open_rectangle
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.exists_open_reduced_isotropy
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.exists_pair_mem_open
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.finiteCompletion_square_neighborhood
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.infiniteCompletion_square_neighborhood
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.isotropic_cons_of_isotropic
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.isotropic_of_reduced_isotropy
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.placeCompletion_square_neighborhood
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.weightedSumSquares_two_cons
_private.Langlands.LinearAlgebra.QuadraticIsotropyApproximation.0.Langlands.QuadraticIsotropy.zero_of_zero_cons
```

</details>
