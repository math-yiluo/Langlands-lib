# Pullback on Ext-defined cohomology of abelian sheaves

Author: Worker 217.

This internal construction supplies the sheaf-cohomology map needed for naturality of square-zero Picard obstructions. It uses only Mathlib constructions and does not assert any comparison with Picard pullback or relative module cohomology.

For a continuous map `f : X ⟶ Y` of topological spaces in universe `u`, let `P = TopCat.Sheaf.pullback AddCommGrpCat f` and `Q = TopCat.Sheaf.pushforward AddCommGrpCat f`. Mathlib's `Sheaf.H A n` is `Extⁿ(ℤ_Y, A)`, with the lifted integer constant sheaf and Ext universe `u`.

## Definitions

`pullback_preservesFiniteLimits` exposes exactness of inverse image. The proof uses Mathlib's representable flatness of the inverse-image functor on opens and `Functor.sheafPullbackConstruction.preservesFiniteLimits`, supplying the forgetful functor's reflection of limits explicitly. Inverse image preserves colimits as a left adjoint. `pullback_additive` follows from preservation of binary products.

`constantPullbackIso f` is the natural isomorphism `constantSheaf Y ⋙ P ≅ constantSheaf X`. Both sides are left adjoints to the same global-sections functor: the first adjunction is the composite of the constant-sheaf adjunction on `Y` and the inverse-image/direct-image adjunction. Uniqueness of left adjoints defines the displayed isomorphism, including its normalization.

For `a : P.obj A ⟶ B`, `pullbackMap f a n : Hⁿ(Y,A) →+ Hⁿ(X,B)` sends `x` to the Yoneda product

```text
[ℤ_X → P(ℤ_Y)] · P(x) · [a].
```

The first arrow is the inverse of `constantPullbackIso f` evaluated at the lifted integers. The middle operation is Mathlib's `Ext.mapExactFunctor`; the degree-zero outer factors are `Ext.mk₀`. Bilinearity and additivity of these operations prove that the map is an additive homomorphism.

`pushforwardMap f k n` is the same construction for a coefficient map `k : A ⟶ Q.obj B`, using its adjoint `P.obj A ⟶ B` under `TopCat.Sheaf.pullbackPushforwardAdjunction`.

## Implemented compatibility proofs

`pullbackMap_naturality_right` states covariance in `B`: replacing `a` by `a ≫ b` is postcomposition of the cohomology map by `Sheaf.H.map b`. `pullbackMap_naturality_left` states covariance in `A`: first applying `Sheaf.H.map a` equals using the coefficient arrow `P.map a ≫ b`. Both follow from `Ext.mk₀_comp_mk₀`, exact-functor compatibility with composition, and associativity of Ext products.

For short exact complexes `S` on `Y` and `T` on `X`, and a morphism `a : S.map P ⟶ T`, `pullbackMap_δ` states, for `n + 1 = m`,

```text
pullbackMap f a.τ₁ m (δ_S x) = δ_T (pullbackMap f a.τ₃ n x).
```

The proof writes the connecting maps as multiplication by the extension classes, applies `Ext.mapExactFunctor_extClass`, uses `ShortComplex.ShortExact.extClass_naturality` for `a`, and reassociates the products. No exactness assumption on direct image is used.

## Provenance and scope

These are internal API definitions and formal consequences of Mathlib's existing sheaf inverse image, adjunctions, constant sheaves, and Yoneda Ext operations. They are not a transcription of a separately cited proposition. They provide the boundary-compatible map in the expected proof route of `SquareZeroObstructionMorphismNaturalityStatement`. Identifying its degree-one unit-coefficient map with Picard pullback, and its module-coefficient map with `relativeCohomologyPullback`, remain separate obligations.
