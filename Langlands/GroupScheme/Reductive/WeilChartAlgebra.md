# The canonical algebra isomorphisms between chart coefficient algebras

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the second step of
the proof of `AffineWeilPairSingleChartDescentStatement`. It turns the chart transfer of
idempotents (module `Langlands.GroupScheme.Reductive.WeilChartTransfer`) into canonical
algebra isomorphisms between chart coefficient algebras. It uses the algebra recovery
`WeilFactor.IdemTransfer` (module `Langlands.GroupScheme.Reductive.WeilFactorIdemTransfer`).
The isomorphisms satisfy the identity and cocycle conditions of a descent datum.

## Setting

As in `WeilChartTransfer`: a chart `P : G_{A'} ≅ AffineWeil.groupScheme A' C H` with `C` finite,
projective and étale over `A'`, `H` reductive with almost simple geometric fibres, and
factor rigidity `hR`. Let `T` be an `A`-algebra.

## Content

- `chartMap'` and `chartTransfer_map'`: naturality of the chart transfer along `χ : T ⟶ T₁`,
  for chart maps on `T₁` that are only propositionally equal to `χ ∘ fₖ`. The proof substitutes
  the equalities and applies `chartTransfer_map`.
- `ChartCoeff C f` is the coefficient algebra `T ⊗[A', f] C` of a chart map
  `f : A' →ₐ[A] T`, as a `T`-algebra (through the left factor). It is finite, projective and étale
  over `T`. It is a separate definition so that its instances are indexed by `f`.
- For a `T`-algebra `X`, `testA X` is `X` regarded as an `A`-algebra. `chartX f X` is the
  chart map `A' → X` (composite of `f` with `T → X`), and `testHom χ` is the `A`-algebra map
  underlying a map of `T`-algebras (`chartX_testHom` relates the chart maps).
  `cancelEquiv f X : ChartCoeff C f ⊗[T] X ≃+* C ⊗[A', chartX f X] X` is the cancellation of
  `T`, built from Mathlib's `Algebra.TensorProduct.comm` and
  `Algebra.TensorProduct.cancelBaseChange`. It sends `(t ⊗ c) ⊗ x` to `c ⊗ (t·x)`
  (`cancelEquiv_tmul`) and is natural in `X` (`cancelEquiv_lT`).
- `chartIdemMap f₁ f₂ X` conjugates the chart transfer at the test algebra `X` (with chart maps
  `chartX fₖ X`) by `cancelEquiv`. It maps idempotents to idempotents, is natural in `X`, is
  multiplicative on idempotents and sends `0` to `0`. It satisfies `chartIdemMap_trans` and
  `chartIdemMap_self`, so the maps for `(f₁, f₂)` and `(f₂, f₁)` are mutually inverse.
- `chartIdemTransfer f₁ f₂ : WeilFactor.IdemTransfer T (ChartCoeff C f₁) (ChartCoeff C f₂)`
  packages these maps.
- `chartAlgEquiv f₁ f₂ : ChartCoeff C f₂ ≃ₐ[T] ChartCoeff C f₁` is the canonical coefficient
  isomorphism, `IdemTransfer.algEquiv` of `chartIdemTransfer f₁ f₂`. It is
  characterized by the transfer of graph idempotents.
- `chartAlgEquiv_self`: the canonical isomorphism of a chart map with itself is the identity.
- `chartAlgEquiv_trans`: for three chart maps,
  `(chartAlgEquiv f₂ f₃).trans (chartAlgEquiv f₁ f₂) = chartAlgEquiv f₁ f₃`, the cocycle
  condition. Both follow from the uniqueness `IdemTransfer.algEquiv_unique` together with the
  corresponding properties of the chart transfer.

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
uniqueness of Weil pairs provides canonical isomorphisms on overlaps of an étale cover. These are
the coefficient-algebra part of those isomorphisms. Here they are obtained from factor rigidity,
through idempotents and the recovery of an algebra isomorphism from a transfer of
idempotents.
