# Natural multiplicative bijections of idempotents and the algebra isomorphisms they induce

Module `Langlands.GroupScheme.Reductive.WeilFactorIdemTransfer`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports [`WeilFactorCanonical`](WeilFactorCanonical.md),
and through it the graph-idempotent machinery of
[`WeilFactorAlgebraRecovery`](WeilFactorAlgebraRecovery.md).

## Purpose and provenance

Provenance: derived/internal. The algebra part of the uniqueness argument in
[`WeilFactorAlgebraRecovery`](WeilFactorAlgebraRecovery.md) only uses formal properties of
the transfer of idempotents. Here those properties become a structure `IdemTransfer`, so that
transfers built in other ways (for example, comparing two presentations in an étale-descent
argument, as `chartIdemTransfer` in `WeilChartAlgebra` does) also induce algebra isomorphisms. The underlying
mathematical fact: for finite étale `A`-algebras `B` and `B''`, a family of bijections
`Idem(B ⊗_A X) ≅ Idem(B'' ⊗_A X)` that is natural in `X`, multiplicative and sends `0` to `0`
comes from a unique `A`-algebra isomorphism `B'' ≅ B`.

## Declarations

`A B B'' B''' : Type u`, with `A`-algebras `B`, `B''`, `B'''`. Test algebras `X` range over
`CommAlgCat (CommRingCat.of A)`, and `lT χ` is the base change map along `χ : X ⟶ Y`.

- `IdemTransfer A B B''` (structure). Maps `map X : B ⊗[A] X → B'' ⊗[A] X` and
  `inv X : B'' ⊗[A] X → B ⊗[A] X` that preserve idempotents (`map_idem`, `inv_idem`), are
  natural on idempotents (`map_lT`, `inv_lT`), are multiplicative on idempotents (`map_mul`,
  `inv_mul`: `map (f * e) = map f * map e`), send `0` to `0` (`map_zero`, `inv_zero`), and are
  inverse on idempotents (`inv_map`, `map_inv`).
- `IdemTransfer.symm`, `IdemTransfer.refl`, `IdemTransfer.trans`: inverse, identity and
  composite transfers.
- `map_ne_zero`, `isMinimalIdem_map`: transfers preserve nonvanishing idempotents and the
  minimality property `IsMinimalIdem`.
- `IdemTransfer.IsAlgEquiv τ α` (a `Prop`): for every `X`, every `φ : B →ₐ[A] X` and every
  graph idempotent `e` of `φ`, `τ.map X e` is the graph idempotent of `φ ∘ α`.
- `exists_algHom`, `exists_algEquiv` (`B`, `B''` finite, projective and étale): some
  `α : B'' ≃ₐ[A] B` has this property. `α` is the algebra map whose graph idempotent is the
  transfer of the diagonal idempotent of `B ⊗_A B`; the same construction for `τ.symm` gives
  its inverse.
- `IdemTransfer.algEquiv τ : B'' ≃ₐ[A] B` (definition, chosen) and `algEquiv_spec`.
- `IsAlgEquiv.eq`, `algEquiv_unique`: the property determines `α`.
- `algEquiv_refl`: `(IdemTransfer.refl A B).algEquiv = AlgEquiv.refl`.
- `algEquiv_trans`: `(τ₁.trans τ₂).algEquiv = τ₂.algEquiv.trans τ₁.algEquiv`.
- `idemTransfer hR hred hsimple hred'' hsimple'' Φ`: the transfer along an isomorphism `Φ` of
  Weil restrictions (from [`WeilFactorTransfer`](WeilFactorTransfer.md)) as an `IdemTransfer`.
  `idemTransfer_algEquiv` says its algebra isomorphism is `weilAlgEquiv Φ`.

## Scope

Compatibility of `algEquiv` with a change of base ring `A → A₁` is not proved here.
