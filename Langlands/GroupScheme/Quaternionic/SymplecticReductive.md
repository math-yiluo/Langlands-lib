# The quaternionic symplectic groups are connected reductive

This module proves `FirstKindInvolution.isConnectedReductive_symplecticGroup`. Let `D` be a
central division algebra of dimension `4` over a field `K` (a quaternion division algebra). Let
`σ` be an involution of the first kind of `D` whose symmetric elements form a `3`-dimensional
space. In characteristic not two this says that `σ` is orthogonal. In characteristic two the
condition does not determine the type of `σ`, and the theorem uses only the condition itself.
Let `H ∈ M_n(D)` (`n` nonempty) be an invertible trace-valued
`σ`-antihermitian Gram matrix (`σ.IsAntihermitian H`). Then the group scheme
`σ.symplecticGroup H` of `Quaternionic.GroupSchemes` is connected reductive over `K`, in the
sense of the Library's `IsConnectedReductive`. This is the special unitary group of `h`, the
kernel of the reduced norm on the unitary group `U(h)`. There is no assumption on the
characteristic or on the Witt index of `H`.

This is the classical statement that `SU(D, h)` is a `K`-form of `Sp_{2n}`. It is type `C_n`
in Tits's classification (*Classification of algebraic semisimple groups*, 1966, Table II),
whose condition on the involution is `dim D^σ = d(d+1)/2`, here `3`.
The proof here is self-contained over the Library.

## Proof

The proof splits `D`. It identifies the base change of `σ.symplecticGroup H` to the splitting
field with the split symplectic group `SymplecticMatrix.groupScheme`. It then uses that this
group is connected reductive (`SymplecticMatrix.isConnectedReductive`) and that connected
reductivity descends along field extensions (the Library's
`IsConnectedReductive.of_fieldExtension`, together with `IsConnectedReductive.of_iso`).

1. **Splitting field.** `L` is the Library's finite Galois splitting field
   `CentralSimple.finiteGaloisSplittingField K D`, with the chart
   `CentralSimple.finiteGaloisSplittingChart K D` reindexed to `2 × 2` matrices.
   `reducedDegree_eq_two` gives reduced degree `2` from dimension `4`.
2. **Alternating Gram matrix.** By `Quaternionic.SplittingMatrix`, the split Gram matrix
   `C = splitGram e σ H` over `L` satisfies `Cᵀ = -C` and has zero diagonal. This holds in every
   characteristic, because the dimension-`3` hypothesis makes the matrix `S` of the transported
   involution symmetric (`involutionMatrix_transpose`), and `H` is trace-valued. It is invertible because `H` is. Darboux
   (`SymplecticMatrix.exists_mul_mul_transpose_eq_J`) gives rectangular `P`, `P'` with
   `P P' = 1`, `P' P = 1` and `P C Pᵀ = J`.
3. **Points.** For a scheme `T` over `Spec L`, let `R = Γ(T, ⊤)`, with its `K`- and
   `L`-algebra structures (`restrictedSections`, with the local instances
   `restrictedSectionsAlgebra` and `restrictedSectionsScalarTower`, copied from the Library's
   `Shimura.AlgebraInvolution.SchemeModel`). A point `x` of the base change gives a unit
   `unitPoint x` of `R ⊗[K] M_n(D)`, through
   * the pullback adjunction (`GroupScheme.baseChangePointsEquiv`),
   * the inclusions `symplecticGroupι` and `unitaryGroupι`, and
   * `FiniteAlgebraUnits.pointsEquiv`.

   This unit is unitary (`unitPoint_unitary`, from `mem_range_unitaryGroupι_iff`).
   Conversely, a unitary unit of reduced norm one comes from a point (`exists_unitPoint_eq`):
   lift it through the closed inclusion, use `CentralSimpleUnits.reducedNormHom_points` for
   the norm condition, and lift into the kernel with `kernelPointsEquiv`.
4. **Darboux matrices.** For every commutative `L`-algebra `R`, `darbouxMatrix e P P' R u` is
   `P Φ(u) P'`, with `Φ = matrixChartR e R`. It is multiplicative and injective, and natural in
   `R`. It is symplectic exactly when `u` is unitary (`darbouxMatrix_mem_iff`). Every
   symplectic matrix `g` arises from a unitary unit of reduced norm one
   (`exists_darbouxMatrix_eq`). The unit is `Φ⁻¹(P' g P)`. Its reduced norm is
   `det (P' g P) = det g = 1`, by `reducedNorm_eq_det_matrixChartR`,
   `det_mul_mul_of_mul_eq_one` and Mathlib's `SymplecticGroup.det_eq_one`. The sizes of the
   index types agree by `card_eq_of_mul_eq_one`, a rank argument.
5. **Isomorphism.** `splitPointsHom` (`x ↦ P Φ(unitPoint x) P'`) is a bijective
   homomorphism on points (`splitPointsHom_bijective`), natural in `T`
   (`splitPointsEquiv_naturality`). The Library's `isoOfPointModels` then gives
   `splittingIso : σ.baseChangeSymplecticGroup H ≅ SymplecticMatrix.groupScheme (Fin k) L`.
6. **Conclusion.** `SymplecticMatrix.isConnectedReductive (Fin k) L`, then
   `IsConnectedReductive.of_iso` and `IsConnectedReductive.of_fieldExtension`.

## Provenance

The identification of the special unitary group of an antihermitian form over a quaternion
algebra with an involution satisfying `dim D^σ = 3` as a form of `Sp_{2n}` is classical (Tits
1966, Table II, type `C_n`). The proof was written for this module from the Library's group-scheme
infrastructure. It uses the following earlier modules: `SymplecticMatrix.Basic`, `Smooth`,
`Generation`, `Reductive` and `Darboux`, and `Quaternionic.SplittingChart` and
`Quaternionic.SplittingMatrix`.
