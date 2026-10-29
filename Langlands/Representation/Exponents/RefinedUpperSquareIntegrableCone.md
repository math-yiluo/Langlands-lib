# Strict blockwise cones for upper exponents of square-integrable product Levis

Author: Worker 953.

This module proves, in the namespace
`Langlands.Exponents.RefinedUpperSquareIntegrableCone`, that a real part of a
generalized eigencharacter of an upper normalized refined Jacquet module of a
square-integrable product-Levi representation lies in the open positive root
cone separately inside every original block. It supplies the upper analytic
input of the proof of
`Langlands.Exponents.RefinedOppositeSquareIntegrableConeStatement`.

## Setting and hypotheses

Fix a prime `p`, `F : PadicField.{uF} p`, `T : F.TopologicalData`, a block
shape `C : GeneralLinear.BlockShape n` and a representation
`σ : Representation ℂ (C.Levi F.Carrier) V` on `V : Type uV`. The field universe
`uF` and the carrier universe `uV` are independent. With `T.topology` and
`T.leviTopologicalGroup C` installed, the theorems below quantify one arbitrary
Borel measurable-space structure on the actual full central quotient

```lean
C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)
```

one arbitrary measure `μ` with `μ.IsHaarMeasure`, and assume only
`IsSquareIntegrableModCenter σ μ`. That predicate supplies admissibility, a
unitary character of the full centre, and square-integrable descended matrix
coefficients. No irreducibility is assumed.

For a refinement `D : Geometric.BlockRefinement C` and
`ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ`, the occurrence hypothesis
is the existing common-power predicate

```lean
IsGeneralizedEigencharacter
  ((T.normalizedRefinedJacquet C D σ).comp
    ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
      ((C.flatten D).blockScalarLevi F.Carrier))) ψ
```

on the actual upper normalized refined Jacquet module, pulled back along the
exact flattened scalar map. Real parts are supplied: `x` satisfies
`T.IsRealPartOf ψ x`. No open-kernel hypothesis is needed.

For an original block `j` write `xⱼ(l) = x (C.flattenBlockEquiv D ⟨j, l⟩)` for
`l : Fin (D j).length`.

## Declarations

- `norm_eq_one_of_mem_center`: if a nested tuple `c` of fine scalars is weakly
  contracting in every original block, its block scalars form an element of
  the centre of `C.Levi F.Carrier`, and its refined modulus is `1`, then
  `‖ψ (flatScalars C D c)‖ = 1`. The proof applies the Library theorem
  `ProductLeviNecessity.exists_eigen_coefficient` with the whole group as
  neighbourhood to obtain `ℓ` and `v` with `ℓ v ≠ 0` and
  `ℓ (σ(g) v) = λ · ℓ v`, where `g` is the block-scalar element and
  `λ = compressionEigenvalue T C D ψ c`. Because `g` is central, the unitary
  central character `χ` of the square-integrability hypothesis gives
  `σ(g) v = χ(g) v`, so `χ(g) = λ`. The refined modulus is `1`, so
  `λ = ψ (flatScalars C D c)`, and `‖χ(g)‖ = 1`. This is the argument of the
  Library theorem `Langlands.ProductLeviNecessity.norm_le_one_of_mem_center`
  (module
  `Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof`),
  with the unitary central character taken from `IsSquareIntegrableModCenter`
  instead of temperedness.
- `testSet_nonempty`, `testSet_compl_nonempty`: for `0 < k < (D j).length`, the
  set `ProductLeviNecessity.testSet C D j k` of positions of block `j` lying in
  fine blocks of index below `k` and its complement are nonempty. They contain
  the first entry of fine block `0` and of fine block `k` respectively; each fine
  block has positive size.
- `norm_testScalars`: for the test tuple `testScalars T C D j k e`, which is
  `ϖ ^ e` on the fine blocks of index below `k` of block `j` and `1` elsewhere,

  ```text
  ‖ψ(flatScalars C D (testScalars T C D j k e))‖ = q ^ (-e · partialSum xⱼ k),
  ```

  where `q = T.residueCardinality`. This combines
  `PadicField.TopologicalData.isRealPartOf_iff_pairing` with the Library identity
  `ProductLeviNecessity.sum_centreHMap_testScalars`.
- `partialSum_pos`: for every `j` and every `0 < k < (D j).length`,
  `0 < partialSum xⱼ k`. The tuple `testScalars T C D j k 1` is weakly
  contracting (`testScalars_isWeaklyContracting`). Its block-`j` scalar is the
  diagonal matrix with `ϖ` exactly on `testSet C D j k`
  (`testScalars_blockScalar_same`), and its refined modulus is
  `q ^ (-(|S| · |Sᶜ|))` for that set `S` (`testScalars_refinedLeviModulus`).
  Both `S` and `Sᶜ` are nonempty. The Library theorem
  `ProductLeviSquareIntegrable.norm_lt_one_of_diagonal` therefore gives
  `‖ψ(…)‖ < 1`. By `norm_testScalars` with `e = 1`, `q ^ (-partialSum xⱼ k) < 1`,
  and since `q > 1` this means `partialSum xⱼ k > 0`.
- `blockSum_eq_zero`: for every `j`, `∑ l, xⱼ(l) = 0`. The full-block tuple
  `testScalars T C D j (D j).length 1` is weakly contracting
  (`testScalars_full_isWeaklyContracting`), central in the original Levi
  (`testScalars_full_mem_center`; its block-`j` component is the scalar `ϖ`), and
  has refined modulus `1` (`testScalars_full_refinedLeviModulus`). So
  `norm_eq_one_of_mem_center` gives norm `1`. The partial sum at the full length
  is the whole block sum, and `norm_testScalars` gives `q ^ (-∑ l, xⱼ(l)) = 1`.
  Injectivity of `t ↦ q ^ t` (`Real.rpow_right_inj`) gives the zero sum. Each
  original block uses its own central direction, so every block gets its own
  zero sum, not only one sum over all flattened indices.
- `isPositiveRootCone`: for every `j`,

  ```lean
  Exponents.IsPositiveRootCone
    (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩))
  ```

  that is, `∑ l, xⱼ(l) = 0` and `0 < partialSum xⱼ k` for every
  `0 < k < (D j).length`. It pairs `blockSum_eq_zero` with `partialSum_pos`. For
  a one-piece refinement of block `j` there is no proper prefix, and the zero sum
  forces the single coordinate to vanish.

These are scalar real-part coordinates; no fine-size multipliers occur.

## Provenance

This is an internal derivation from proved Library theorems; it adds no new
analytic criterion. The strict inequality comes from
`Langlands.ProductLeviSquareIntegrable.norm_lt_one_of_diagonal`. The central
directions use `Langlands.ProductLeviNecessity.exists_eigen_coefficient` and the
unitary central character contained in `IsSquareIntegrableModCenter`. The test
tuples and their weak contraction, centrality, modulus and pairing identities are
the Library's `ProductLeviNecessity` declarations listed above. The mathematical
motivation is the strict exponent criterion of Casselman, *Introduction to the
theory of admissible representations of p-adic reductive groups* (1995),
Theorem 4.4.6, p.45. This module does not formalize that theorem; it
specializes the Library's own product-Levi analytic bounds to scalar real-part
coordinates.
