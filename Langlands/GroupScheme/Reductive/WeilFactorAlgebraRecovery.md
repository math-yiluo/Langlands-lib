# Recovering the étale algebra of a Weil restriction from its factor projections

Worker 47.

Module `Langlands.GroupScheme.Reductive.WeilFactorAlgebraRecovery`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports [`WeilFactorTransfer`](WeilFactorTransfer.md)
and [`Algebra.EtaleGraphIdempotent`](../../Algebra/EtaleGraphIdempotent.md).

## Provenance

Provenance: derived/internal. The algebra maps `B → T` correspond to the graph idempotents
of `B ⊗_A T`. These can be described using only multiplication of idempotents, base change and
nonvanishing: they are the idempotents that are nonzero over every nonzero `T`-algebra and
minimal with this property, over every `T`-algebra. That description is preserved by the
transfer of idempotents, and a Yoneda-type argument recovers an isomorphism `B'' ≃ B`. This
plays the role of the bijection `α : I ≃ J` of factors in the proof of Conrad's
Proposition 6.4.4.

## Declarations

- `lT χ`: the map `B ⊗ T → B ⊗ T₁` induced by `χ : T ⟶ T₁` in `CommAlgCat A`. `lT_apply`
  identifies it with `Algebra.TensorProduct.map (AlgHom.id A B) χ.hom`.
- `IsMinimalIdem e` (structure, for `e ∈ B ⊗ T`): `e` is idempotent; `lT χ e ≠ 0` for every
  `χ : T ⟶ T₁` with `T₁` nontrivial; and for every `χ : T ⟶ T₁`, an idempotent `f` with
  `f · lT χ e = f` whose images over all nontrivial `T₁`-algebras are nonzero equals `lT χ e`.
- `isMinimalIdem_of_isGraphIdempotent`: graph idempotents are minimal
  (`IsGraphIdempotent.map`, `ne_zero`, `eq_of_le`).
- `IsMinimalIdem.exists_isGraphIdempotent` (`B` finite, projective, formally unramified and
  essentially of finite type): minimal idempotents are graph idempotents
  (`exists_isGraphIdempotent_of_minimal`, tested on `T₁ = (B ⊗ T)/(1 - e)` and `T₁ = T/m`).
- `transfer_transfer_symm`, `transfer_ne_zero`, `isMinimalIdem_transfer`: transfer along an
  isomorphism `Φ` of Weil restrictions preserves minimality. These assume the rigidity
  statement and reductivity with almost simple geometric fibres on both sides.
- `exists_algHom_transfer`: there is `α : B'' →ₐ[A] B` such that the transfer of the graph
  idempotent of any `φ : B →ₐ[A] T` is the graph idempotent of `φ ∘ α`. Here `α` is the algebra
  map whose graph idempotent is the transfer of the diagonal idempotent of `B ⊗_A B`.
- `exists_algEquiv_transfer`: `α` is an isomorphism `B'' ≃ₐ[A] B`. Applying the same
  construction to `Φ.symm` gives `α'`. Then `α ∘ α'` and `α' ∘ α` have the same graph
  idempotents as the identities, so they are the identities.
