# Group-likes from algebra homomorphisms out of the convolution dual

Module: `Langlands.RingTheory.Coalgebra.ConvolutionDualGroupLike`
(namespace `Langlands.CoalgebraDescent`).

This module contains helper lemmas for the proof of
`Langlands.CoalgebraDescent.SeparablyClosedGroupLikeSpanningStatement` (task
`d4ae678f-2afe-41e5-acf7-700af9077a9a`). It covers the finite-dimensional splitting
step only: once the convolution dual of a finite-dimensional coalgebra is known to be
a product of copies of the base field (or commutative and formally unramified over a
separably closed field), its group-like elements span the coalgebra. It defines
nothing new; all structures are Mathlib's.

## Setting

Throughout, `k` is a field and `D` is a `k`-module with Mathlib's `Coalgebra k D`.
The convolution dual is Mathlib's `WithConv (D →ₗ[k] k)` with the `Ring` and
`Algebra k` instances `LinearMap.convRing` and `LinearMap.convAlgebra` from
`Mathlib.RingTheory.Coalgebra.Convolution`: the product is
`(f * g) c = mul' k k (map f g (comul c))` and the unit is
`Algebra.linearMap k k ∘ₗ counit`. Commutativity (`LinearMap.convCommRing`) is
available under `Coalgebra.IsCocomm k D` and is used in the formally unramified
splitting step and its final corollary.

## Declarations

- `tensor_eq_of_forall_dual` (needs `FiniteDimensional k D`, no coalgebra structure):
  if `mul' k k (map φ ψ t) = mul' k k (map φ ψ t')` for all `φ ψ : Module.Dual k D`,
  then `t = t'` in `D ⊗[k] D`.
- `exists_isGroupLikeElem_of_algHom` (needs `FiniteDimensional k D`): every
  `χ : WithConv (D →ₗ[k] k) →ₐ[k] k` is evaluation at a group-like element:
  there is `d : D` with `IsGroupLikeElem k d` and `χ (toConv φ) = φ d` for all
  `φ : D →ₗ[k] k`.
- `span_isGroupLikeElem_eq_top_of_algHom_separating` (needs `FiniteDimensional k D`):
  if every element of the convolution dual killed by all `k`-algebra homomorphisms to
  `k` is zero, then `Submodule.span k {d : D | IsGroupLikeElem k d} = ⊤`.
- `span_isGroupLikeElem_eq_top_of_algEquiv_pi` (needs `FiniteDimensional k D`): the same
  conclusion from any `k`-algebra equivalence
  `WithConv (D →ₗ[k] k) ≃ₐ[k] (ι → k)`, for an arbitrary index type `ι`.
- `span_isGroupLikeElem_eq_top_of_formallyUnramified` (needs `IsSepClosed k`,
  `FiniteDimensional k D`, `Coalgebra.IsCocomm k D` and
  `Algebra.FormallyUnramified k (WithConv (D →ₗ[k] k))`): the same conclusion. A
  `FormallyEtale` hypothesis also suffices, since Mathlib derives `FormallyUnramified`
  from it by instance.
- `formallyUnramified_of_tensorProduct_algEquiv_pi` (no coalgebra): for a commutative
  `k`-algebra `A`, a field `K` with `[Algebra k K]`, a finite index type `ι` and a
  `K`-algebra equivalence `K ⊗[k] A ≃ₐ[K] (ι → K)`, the algebra `A` is
  `Algebra.FormallyUnramified` over `k`. No finiteness of `A` is needed.
- `span_isGroupLikeElem_eq_top_of_tensorProduct_algEquiv_pi` (needs `IsSepClosed k`,
  `FiniteDimensional k D`, `Coalgebra.IsCocomm k D`): given a field `K` over `k`, a
  finite `ι` and `K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] (ι → K)`, the group-like elements
  span `D`.

## Proofs

**Separation in `D ⊗ D`.** By `Module.forall_dual_apply_eq_zero_iff` it suffices that
every `θ : Module.Dual k (D ⊗[k] D)` kills `t - t'`. Since `D` is finite dimensional,
`TensorProduct.dualDistribEquiv k D D` is a linear equivalence
`Dual D ⊗ Dual D ≃ Dual (D ⊗ D)`, so `θ` is the image of some `x`. Induction on `x`
(`TensorProduct.inductionOn`) reduces to `x = φ ⊗ₜ ψ`, whose image equals
`mul' k k ∘ₗ map φ ψ` (checked on pure tensors, up to `mul_comm`); the hypothesis then
gives the claim. Sums follow by additivity.

**Algebra homomorphisms are group-likes.** Compose `χ` with
`(WithConv.linearEquiv k (D →ₗ[k] k)).symm` to get `ℓ : Dual k (Dual k D)`, and let
`d := (Module.evalEquiv k D).symm ℓ`; `Module.apply_evalEquiv_symm_apply` gives
`φ d = χ (toConv φ)`. The convolution unit is `toConv counit` (`LinearMap.convOne_def`;
`Algebra.linearMap k k ∘ₗ counit = counit` by `congr`), so `counit d = χ 1 = 1`. For
`φ ψ`, multiplicativity of `χ` and `LinearMap.convMul_apply` give
`mul' k k (map φ ψ (comul d)) = φ d * ψ d = mul' k k (map φ ψ (d ⊗ₜ d))`, so
`comul d = d ⊗ₜ d` by the separation lemma.

**Spanning from separating homomorphisms.** If the span `W` of the group-likes were
not `⊤`, `Submodule.exists_dual_map_eq_bot_of_lt_top` (quotients of vector spaces are
projective) gives a nonzero `φ : Dual k D` with `W.map φ = ⊥`. For every algebra
homomorphism `χ`, the previous lemma writes `χ (toConv φ) = φ d` with `d` group-like,
hence in `W`, so `χ (toConv φ) = 0`. The separation hypothesis forces `toConv φ = 0`,
i.e. `φ = 0`, a contradiction.

**Product of copies of `k`.** For `e : WithConv (D →ₗ[k] k) ≃ₐ[k] (ι → k)`, the
coordinate homomorphisms `(Pi.evalAlgHom k _ i).comp e.toAlgHom` separate points
because `e` is injective.

**Formally unramified case.** The convolution dual is finite over `k`
(`Module.Finite.equiv` along `WithConv.linearEquiv`), hence essentially of finite type
by instance. Mathlib's `Algebra.FormallyEtale.of_formallyUnramified_of_field` makes it
formally étale, and `Algebra.FormallyEtale.equivPiOfIsSepClosed` gives
`WithConv (D →ₗ[k] k) ≃ₐ[k] (PrimeSpectrum _ → k)`; apply the previous lemma.

**Descent of formal unramifiedness.** `ι → K` is formally unramified over `K` by
Mathlib's instance for finite products (`Mathlib.RingTheory.Unramified.Pi`) and
`K` over itself; `Algebra.FormallyUnramified.of_equiv e.symm` transports this to
`K ⊗[k] A`. The field `K` is a nontrivial free, hence faithfully flat, `k`-module, so
`Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat`
(`Mathlib.RingTheory.Etale.Descent`) gives `FormallyUnramified k A`. The final
corollary combines this (with `A` the commutative convolution dual) with the formally
unramified case.

## Provenance

This is the coetale-to-group-like step of Milne, *Algebraic Groups* (2017), registered
ID `milne-2017-algebraic-groups`, Theorem 12.18 (c) ⇒ (d) (printed pp. 236–238), stated
here for an arbitrary finite-dimensional coalgebra with its Mathlib convolution dual
instead of a coordinate coalgebra. The implemented route (algebra homomorphisms to `k`
correspond to group-likes via double duality; separable closedness splits the étale
dual) follows the same idea; the Lean statements are internal helper lemmas.
