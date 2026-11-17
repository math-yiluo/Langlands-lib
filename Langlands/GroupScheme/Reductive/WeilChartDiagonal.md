# The diagonal idempotent of a descended coefficient algebra through a chart

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the fourth step of the
proof of `AffineWeilPairSingleChartDescentStatement`. Descent of the coefficient algebra
(`exists_chartDescent` in `Langlands.GroupScheme.Reductive.WeilChartNaturality`) produces a finite
étale `A`-algebra `B` and an isomorphism `e : A' ⊗[A] B ≃ₐ[A'] C`. For a test algebra with a
`B`-structure, this module builds the idempotent of `C ⊗[A', f] T` that describes the `B`-factor
of `G`. It then proves that the corresponding chart factor projection does not depend on the
chart map `f`.

## Setting

`A → A'` and `A' → C` are ring maps, `B` is an `A`-algebra and `e : A' ⊗[A] B ≃ₐ[A'] C`. The group
data are as in `WeilChartTransfer`: a chart `P : G_{A'} ≅ AffineWeil.groupScheme A' C H`, factor
rigidity `hR`, and `H` reductive with almost simple geometric fibres. `T` is an `A`-algebra.

## The diagonal idempotent

- `diagMap e φ f : C →ₐ[A'] T`, for `φ : B →ₐ[A] T` and a chart map `f : A' →ₐ[A] T`, sends
  `e (a ⊗ b)` to `f a * φ b` (`diagMap_tmul`). Here `T` is an `A'`-algebra through `f`
  (`chartAlgebra_isScalarTower` gives the scalar tower `A → A' → T`).
- `diagIdem e φ f ∈ C ⊗[A', f] T` is a chosen graph idempotent of `diagMap e φ f`, in the sense of
  `Langlands.Algebra.GraphIdempotent.IsGraphIdempotent` (`diagIdem_spec`). It exists because
  `C` is étale over `A'`.
- Naturality: `diagMap_map` and `diagIdem_map` show that both are compatible with a map
  `χ : T ⟶ T₁`, for the data `χ ∘ φ` and `χ ∘ f`. Graph idempotents are unique, so this needs no
  choice.

## Graph idempotents and the cancellation isomorphism

For a `T`-algebra `X` and a `T`-algebra map `ρ : T ⊗[A', f] C → X`, `coeffRestrict f X ρ` is the
`A'`-algebra map `c ↦ ρ (1 ⊗ c)` from `C` to `X`. The cancellation isomorphism `cancelEquiv`
(from `WeilChartAlgebra`) intertwines the multiplication maps (`graphMul_cancelEquiv`). It sends a
graph idempotent of `ρ` to a graph idempotent of `coeffRestrict f X ρ`
(`isGraphIdempotent_cancelEquiv`).

## Chart independence

Assume the invariance produced by descent: for chart maps `f₁ f₂ : A' → T`,
`chartAlgEquiv f₁ f₂` fixes `1 ⊗ e (1 ⊗ b)` for every `b ∈ B` (hypothesis `hinv`, written with
`coeffTmul f t c = t ⊗ c`).

- `selfAlg T` is `T` as an algebra over itself. `selfHom T` is the identity of `T`, as a map of
  `A`-algebras from `testA (selfAlg T)` to `T`. The two `A`-structures agree, but not
  syntactically. `IsChartComp χ g f` abbreviates `f = χ ∘ g`, and `isChartComp_selfHom` relates
  the chart maps.
- `coeffPoint e φ f : T ⊗[A', f] C →ₐ[T] T` is the `T`-linear extension of `diagMap e φ f`.
  `coeffPoint_comp_chartAlgEquiv`: under `hinv`,
  `coeffPoint e φ f₁ ∘ chartAlgEquiv f₁ f₂ = coeffPoint e φ f₂`. Both sides are `T`-linear and
  agree on the elements `1 ⊗ e (a ⊗ b) = f₂ a · (1 ⊗ e (1 ⊗ b))`.
- `lTensor_cancelEquiv_eq_diagIdem`: after cancellation and transport along `selfHom T`, a graph
  idempotent of `coeffPoint e φ f` becomes `diagIdem e φ f`.
- `chartTransfer_diagIdem` (**chart independence**): under `hinv`, the chart transfer from `f₁`
  to `f₂` sends `diagIdem e φ f₁` to `diagIdem e φ f₂`. The proof takes graph idempotents `δᵢ` of
  `coeffPoint e φ fᵢ` over the test algebra `selfAlg T`. The defining property of
  `chartAlgEquiv` and `coeffPoint_comp_chartAlgEquiv` show that the transfer of idempotents
  `chartIdemMap f₁ f₂` sends `δ₁` to `δ₂`. Cancellation and `chartTransfer_map'` along
  `selfHom T` translate this into the claim.
- `chartFactor_diagIdem`: consequently the chart factor projections of `diagIdem e φ f₁` through
  `f₁` and of `diagIdem e φ f₂` through `f₂` are equal endomorphisms of the group functor of `G`
  over `T`.

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
descended group `G'` over `B` is the factor of `G_B` cut out by the diagonal of `B`. The
idempotent `diagIdem` is that diagonal factor, seen through a chart. Chart independence is the
compatibility that lets the factor projection descend from `A'`-algebras to all algebras.
