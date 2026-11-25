# Isotypy at a complex place of an irreducible realization with a given parameter

Module `Langlands.Global.RankinSelberg.ComplexPlaceIsotypic`, namespace
`Langlands.Automorphic.OperatorRealization`. It is a step towards the bridge premise of the
conditional reduction `complexPlaceFunctionalEquationReduction` (complex-place Rankin–Selberg
functional equation). Provenance: internal.

Let `S` be an operator realization of `GL_n` over a number field `F`, `w` a complex place and
`ds` a list of complex characters (`ComplexCharacterData`). Write `I(ds)` for the
`U(n)`-finite functions of the complex standard module of `ds` (Library
`complexStandardKFinite n ds`).

## Definitions

- `IsComplexPlaceMap S w ds A`, for a `ℂ`-linear map `A : I(ds) → S`: for every `k ∈ U(n)`
  and `f ∈ I(ds)`, the right translate of `f` by `k` lies in `I(ds)` and `A` maps it to the
  compact action of `k` at `w` on `A f`; for every real direction `X ∈ 𝔤𝔩_n(ℂ)` and
  `f ∈ I(ds)`, the right derivative of `f` along `X` lies in `I(ds)` and `A` maps it to the
  Lie action of `1 ⊗ X` at `w` on `A f`. These are exactly the clauses of the Library's
  `HasComplexPlaceParameter`, without the injectivity and the length condition: `A` is a
  `(𝔤, K)`-map at `w`.
- `complexPlaceIsotypic S w ds`: the sum (supremum of submodules) of the images of all
  `(𝔤, K)`-maps at `w` from `I(ds)` to `S`.

## Results

- `apply_mem_complexPlaceIsotypic`: `A f` lies in the sum for every `(𝔤, K)`-map `A`.
- `complexPlaceIsotypic_stable`: a linear endomorphism maps the sum into itself if it maps
  every `A f` into it (the sum is the supremum of the images).
- `IsComplexPlaceMap.comp`: if `P` commutes with the compact and Lie actions at `w`, then
  `P ∘ A` is again a `(𝔤, K)`-map at `w`.
- `IsComplexPlaceMap.compact_mem_range`: the compact action at `w` of `l ∈ U(n)` maps `A f`
  into the image of `A`. The element `l` of the unitary group is viewed as an element of
  `U(n) ⊆ GL_n(ℂ)` through `Unitary.toUnits`, and the first clause applies.
- `IsComplexPlaceMap.lie_mem_range`: the Lie action at `w` of `Y ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` maps
  `A f` into the image of `A`. By induction on tensors: `z ⊗ X = z • (1 ⊗ X)`, and the second
  clause applies to `1 ⊗ X`.
- `complexPlaceIsotypic_isComplexPlaceCommutantStable`: the sum satisfies
  `IsComplexPlaceCommutantStable` (module `ComplexPlaceStableOperator`), by the three
  previous items.
- `complexPlaceIsotypic_eq_top`: **if `S` is irreducible and has the parameter `ds` at `w`
  (`HasComplexPlaceParameter`), the sum is all of `S`.** By
  `IsComplexPlaceCommutantStable.eq_bot_or_eq_top` the sum is `⊥` or `⊤`. It is not `⊥`: the
  parameter gives an injective `(𝔤, K)`-map `A`, and `I(ds)` is nonzero when `ds` has length
  `n` (Library `Archimedean.complexStandardNontrivial`), so some `A f ≠ 0` lies in the sum.

No irreducibility of `I(ds)` and no tensor product theorem is used: the irreducibility of `S`
under its whole operator algebra suffices.
