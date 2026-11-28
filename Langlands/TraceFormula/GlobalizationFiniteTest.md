# Finite adelic tensor tests with prescribed local factors

For a finite set `S` of finite places of a number field `K` and locally constant compactly
supported functions `F_v` on `GL_n(K_v)`, `finiteTest K n S F` is the finite adelic test

`y ↦ ∏_{v ∈ S} F_v(y_v) · 1_{∏_{v ∉ S} GL_n(𝒪_v)}(y^S)`,

built through the Library's splitting `FiniteAdelicGL.splitAtPlaces` and the
characteristic function `awayCharacteristic`. Locally constancy is checked factor by factor
(`isLocallyConstant_finsetProd`); compact support comes from the compact product of the local
supports and the compact away integral subgroup. `finiteTest_apply` and
`adelicTestTensor_finiteTest` give its values and those of its tensor `a ⊗ finiteTest S F` with
an archimedean kernel `a`.

## Cuspidality and support

* `finiteTest_localSlice`: restricted to one place `v ∈ S` after two-sided translation, the
  finite test is a constant times a two-sided translate of `F_v`.
* `finiteTest_twoBlock_vanishing`: if `F_v` has vanishing constant terms
  (`BaseChange.HasVanishingConstantTerms`) for some `v ∈ S`, then the finite test integrates to
  zero along every two-sided translate of every two-block unipotent radical at `v`. The proof
  combines the slice formula with `generalLinearCuspFormLocalVanishing`.
* `adelicTestTensor_finiteTest_twoBlock_vanishing`: the same vanishing for the adelic tensor
  `a ⊗ finiteTest S F`, since the finite unipotent elements have trivial archimedean component.
  This is the hypothesis of `generalLinearRadicalIntegralVanishing`.
* `finiteComponent_mem_tsupport`: on the closed support of the tensor, the component at each
  `v ∈ S` lies in the closed support of `F_v`.

## Group-scheme points

`fullTest K n S F a` is the tensor on the adelic points of the group scheme `GL_n`, through
`GeneralLinearGroupPoints.adelicHomeomorph`. `fullTestExterior` is its part away from three
places `v₀, v₁, v₂ ∈ S`. `fullTest_eq_threePlaceTensor` writes the full test as
`threePlaceTensor` of the three local factors (composed with `localMatrixHomeomorph`) and the
exterior part, and `fullTestExterior_mul_finitePlacePointInclusion` shows that the exterior
part is invariant under right translation by points at the three places.
`finitePlacePointInclusion_eq_ofPlace` identifies the two insertions of a local point.
