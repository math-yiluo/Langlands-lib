# Orbit products over a simple relative root fiber from the split product statement

Module `Langlands.GroupScheme.Rational.SimpleRootFiberProducts`, namespaces
`Langlands.GroupScheme.LinkedRootParametrization`, `Langlands.GroupScheme.SplitPinning` and
`Langlands.GroupScheme.SimpleRootFiber`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b), SL2 half.

## Purpose

The field coordinates `upperRootEquiv` / `lowerRootEquiv` of `OrthogonalOrbitRootCoordinates`,
and the records `positiveCoordinates` / `negativeCoordinates` built from them, take four
product hypotheses over the splitting field `K`:

- `hprodp`: every point of the root group of `a_K` (for `S_K → G_K`) is an orbit product
  `orbitXp c` over the fiber `O`;
- `huniqp`: such a product determines `c` on `O`;
- `hprodm`, `huniqm`: the same for `-a_K` with `orbitXm`.

This module derives all four from the published proposition
`Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement`, taken as a hypothesis
`hProd`, for the pinning `fiberPinning` and fiber `O = fiberSet a` of `SimpleRootFiberPinning`.
Here `a` is a simple relative root with `2 • a` not a relative root. The proof of the product
statement is Task 7010 (12fc0626-2b9d-44d7-b394-a63d76739556); it is not assumed here.

## Contents

- `LinkedRootParametrization.exists_xmPoint_eq`: every rational point of the negative root
  group is `x₋(c)`, from `LocalSplitCell.exists_rootPoint_eq` and the representation by
  `negative`. This is the negative analogue of the Library's `exists_xpPoint_eq`.
- `LinkedRootParametrization.xpPoint_injective`, `xmPoint_injective`: the root maps are
  injective on rational points. Their scheme maps are monomorphisms, and `gpt_injective` and
  `secMap` handle the coordinate.
- `SplitPinning.orbitXp_eq_prod_ofFn`, `orbitXm_eq_prod_ofFn`: for any enumeration
  `e : O ≃ Fin n`, the orbit product (a `noncommProd` over `O`) is the ordered list product
  `(List.ofFn fun r => x_{e⁻¹ r}(c (e⁻¹ r))).prod`. Proof: `Finset.noncommProd_congr` and
  `Finset.noncommProd_toFinset`, with `univ_eq_toFinset_ofFn`.
- `fiberRootEnum`: the roots of the members of `O`, enumerated along `Fintype.equivFin`. It is
  injective (`fiberRootEnum_injective`).
- `mem_range_fiberRootEnum_iff`: the fiber roots are exactly the roots `χ` of `T_K` with
  `f_K ≫ χ = m • a_K` for some `m > 0`. Such a `χ` restricts to `m • a`, so `m = 1` by
  `eq_one_of_restrictCharacter_eq_nsmul` (this uses `HasRelativeRootSystem` and that `2 • a`
  is not a relative root). Then `χ` lies in the fiber by `exists_mem_fiberSet`.
- `mem_range_neg_fiberRootEnum_iff`: the same for the negatives of the fiber roots and `-a`,
  using `IsRootDatumOf.neg_mem_roots`.
- `baseChange_ne_zero_of_simple`: `a_K ≠ 0`.
- `fiberProduct_pos`, `fiberProduct_neg`: `hProd` applied to `K`, `G_K`, `S_K`, `T_K`, `j_K`,
  `f_K`, `±a_K` and the enumerations above.
- `fiber_hprodp`, `fiber_hprodm`: a point of the root group of `±a_K` is a list product of
  absolute root points, each of the form `x_±(c_r)`. Gathering the coordinates on `O` and
  using `orbitX±_eq_prod_ofFn` gives the orbit product.
- `fiber_huniqp`, `fiber_huniqm`: equal orbit products are equal list products of root points.
  The uniqueness clause of `hProd` identifies the factors, and injectivity of `x_±` gives the
  coordinates.

The hypotheses are exactly the arguments `hprodp`, `huniqp`, `hprodm`, `huniqm` of
`SimpleRootFiber.positiveCoordinates` / `negativeCoordinates` (module
`SimpleRootFiberCoordinates`) and of `SplitPinning.upperRootEquiv` / `lowerRootEquiv`.

## Provenance

Internal glue. The product decomposition itself is the published statement
`SplitRelativeRootGroupProductStatement` (Borel–Tits 1965, proof of Théorème 3.17; see its
Markdown), used here only as the hypothesis `hProd`. Everything else is proved in Lean from
Library results: `LocalSplitCell.exists_rootPoint_eq`,
`LinkedRootParametrization.exists_xpPoint_eq`, `xpPoint_mem`, `xmPoint_mem`,
`Finset.noncommProd_toFinset`, and the fiber API of `SimpleRootFiberPinning`.
