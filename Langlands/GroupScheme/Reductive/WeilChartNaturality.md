# Naturality of the canonical coefficient isomorphisms in the test algebra

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the third step of the
proof of `AffineWeilPairSingleChartDescentStatement`. The module
`Langlands.GroupScheme.Reductive.WeilChartAlgebra` builds canonical isomorphisms
`chartAlgEquiv f₁ f₂ : T ⊗[A', f₂] C ≃ₐ[T] T ⊗[A', f₁] C` between chart coefficient algebras,
and proves the identity and cocycle conditions. This module proves that they are natural in the
test algebra `T`. As a consequence, they form a descent datum in the sense of
`Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement`.

## Setting

As in `WeilChartAlgebra`: a chart `P : G_{A'} ≅ AffineWeil.groupScheme A' C H` with `C` finite,
projective and étale over `A'`, `H` reductive with almost simple geometric fibres, and factor
rigidity `hR`. Let `χ : T ⟶ T₁` be a map of `A`-algebras.

## Content

- `coeffMap χ f : T ⊗[A', f] C → T₁ ⊗[A', χ ∘ f] C` is `Algebra.TensorProduct.map` of `χ`, viewed
  as a map of `A'`-algebras, and of the identity of `C`. This is the map in the naturality
  hypothesis of `FiniteEtaleChartDescentStatement`.
- `resT χ X` regards a `T₁`-algebra `X` as a `T`-algebra through `χ`. `resTestHom χ X` is the
  identity of `X`, as a map of `A`-algebras between the two `A`-structures on `X`, which agree.
- `coeffTensorMap χ f X : (T ⊗[A', f] C) ⊗[T] X → (T₁ ⊗[A', χ ∘ f] C) ⊗[T₁] X` is defined
  through the cancellation isomorphisms `cancelEquiv`. It sends `b ⊗ x` to `coeffMap χ f b ⊗ x`
  (`coeffTensorMap_tmul`). Every element `b ⊗ 1` of the target is in its image
  (`exists_coeffTensorMap_eq`).
- `coeffAlgHom χ f X ψ` is the composite of an algebra map `ψ` out of `T₁ ⊗[A', χ ∘ f] C`
  with `coeffMap`, as a map of `T`-algebras. It is compatible with the multiplication maps of
  graph idempotents (`graphMul_coeffTensorMap`). Hence `coeffTensorMap` sends a graph idempotent of
  `coeffAlgHom χ f X ψ` to a graph idempotent of `ψ` (`isGraphIdempotent_coeffTensorMap`).
- `algHom_eq_of_graphMul_eq_one`: if `e` is a graph idempotent of `φ` and the multiplication map
  of `ψ` sends `e` to `1`, then `φ = ψ`. This is the argument of
  `GraphIdempotent.IsGraphIdempotent.algHom_eq`, with a weaker hypothesis on `ψ`.
- `chartIdemMap_coeffTensorMap`: the transfer of idempotents for the chart maps `χ ∘ f₁`,
  `χ ∘ f₂` over `T₁` agrees, through `coeffTensorMap`, with the transfer for `f₁`, `f₂` over
  `T`. The proof applies `chartTransfer_map'` to `resTestHom χ X`.
- `coeffAlgHom_comp_chartAlgEquiv`: for every algebra map `ψ` out of `T₁ ⊗[A', χ ∘ f₁] C`,
  `coeffAlgHom χ f₁ X ψ ∘ chartAlgEquiv f₁ f₂ = coeffAlgHom χ f₂ X (ψ ∘ chartAlgEquiv (χ ∘ f₁) (χ ∘ f₂))`.
  The proof takes a graph idempotent `δ` of `coeffAlgHom χ f₁ X ψ` over `T`. The defining property
  of `chartAlgEquiv` over `T` and over `T₁`, applied to `δ` and to its image under `coeffTensorMap`,
  together with `chartIdemMap_coeffTensorMap`, gives the equality by
  `algHom_eq_of_graphMul_eq_one`.
- `chartAlgEquiv_coeffMap` (**naturality**): for all `x ∈ T ⊗[A', f₂] C`,
  `chartAlgEquiv (χ ∘ f₁) (χ ∘ f₂) (coeffMap χ f₂ x) = coeffMap χ f₁ (chartAlgEquiv f₁ f₂ x)`.
  This is the previous item with `ψ` the identity.
- `exists_chartDescent hK hsurj`: suppose `A → A'` is étale with `Spec A' → Spec A` surjective,
  and `hK` is a proof of `FiniteEtaleChartDescentStatement`. Then there are a finite, projective,
  étale `A`-algebra `B` and an `A'`-algebra isomorphism `e : A' ⊗[A] B ≃ₐ[A'] C` such that every
  `chartAlgEquiv f₁ f₂` sends `1 ⊗ e (1 ⊗ b)` to `1 ⊗ e (1 ⊗ b)`. The proof applies `hK` to
  `θ T f₁ f₂ := chartAlgEquiv f₁ f₂`, with `chartAlgEquiv_self`, `chartAlgEquiv_trans` and
  `chartAlgEquiv_coeffMap` as the three hypotheses.

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
canonical isomorphisms between Weil pairs on overlaps of an étale cover form a descent datum.
Its coefficient-algebra part descends to the finite étale algebra `B`. This module supplies the
naturality condition of that descent datum and applies the descent statement to it.
