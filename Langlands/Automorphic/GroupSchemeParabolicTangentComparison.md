# The complexified archimedean tangent Lie algebra as a scalar extension

For a number field `F` and an affine group scheme `G` over `F`, smooth of relative dimension `d`,
the module `Langlands.Automorphic.GroupSchemeParabolicTangentComparison` identifies the complex
Lie algebra `AdelicComplexLieAlgebra F G hsmooth = ℂ ⊗_ℝ Lie(G(F ⊗ ℝ))` of
`Langlands.Automorphic.GroupSchemeParabolicTangentStatement` with the scalar extension
`ℂ ⊗_ℚ Lie(G)` of the algebraic Lie algebra of `G` viewed over `ℚ`, compatibly with the
complexified differentials `complexPointDifferential` of homomorphisms.

## Main declarations

- `RationalTangentLie F G`: the dual-number Lie algebra `Additive (lieKernel G F)` viewed as a
  Lie algebra over `ℚ` (`RestrictScalars ℚ F _`), with the scoped bracket of
  `Langlands.GroupScheme.Lie.FieldAlgebraLie`.
- `tangentAddHom`, `complexTangentAddHom`, `complexTangentMap`: the `ℂ`-linear map
  `Θ : ℂ ⊗_ℚ RationalTangentLie F G → AdelicComplexLieAlgebra F G hsmooth`,
  `Θ(z ⊗ x) = z ⊗ τ(x)`, where `τ` is `tangentVector` of
  `Langlands.Global.InfiniteAdelicTangentComplexification`. It is well defined because `τ` is
  additive and `τ(q x) = q τ(x)` for rational `q` (`TensorProduct.liftAddHom`), and `ℂ`-linear by
  construction on pure tensors (`complexTangentMap_tmul`).
- `complexTangentMap_lie`: `Θ` preserves brackets: on pure tensors both sides are
  `(z w) ⊗ τ⁅x, y⁆ = (z w) ⊗ ⁅τ x, τ y⁆` (`LieAlgebra.ExtendScalars.bracket_tmul`,
  `tangentVector_lie`).
- `complexTangentMap_surjective`: for each `z`, the real span of the `τ(x)` is the whole tangent
  space (`span_range_tangentVector`), so every `z ⊗ Y` lies in the image of `Θ`.
- `finite_rationalTangentLie`, `finrank_rationalTangentLie`, `finrank_complexTangent`: both sides
  have complex dimension `d · [F : ℚ]` (`finrank_smoothModel`, `finrank_lieKernel_of_smooth`).
- `complexTangentMap_injective`: a surjective linear map between spaces of the same finite
  dimension is injective.
- `complexTangentEquiv`: **the isomorphism of complex Lie algebras
  `ℂ ⊗_ℚ RationalTangentLie F G ≃ₗ⁅ℂ⁆ AdelicComplexLieAlgebra F G hsmooth`** built from `Θ`.
- `rationalTargetMap f`, `rationalTargetMap_apply`: the tangent map `Lie.targetMapLinear f F` of a
  homomorphism `f : H → G`, viewed over `ℚ`.
- `complexPointDifferential_complexTangentMap`: **naturality**,
  `complexPointDifferential F hH hG f (Θ_H t) = Θ_G ((rationalTargetMap F f).baseChange ℂ t)`;
  on pure tensors this is `tangentVector_naturality`.
