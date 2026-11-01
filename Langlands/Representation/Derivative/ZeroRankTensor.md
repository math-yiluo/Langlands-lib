# Derivatives of tensor products with an inert factor

Author: Worker 969.

This module provides ingredients for the rank-zero cases of BZ77 4.14(b) and (c);
the actual comparison of the right mixed product with a tensor product and the
filtration assembly are not part of it. Let `X` be a smooth
representation of a group `G`, and let `A` be a complex vector space with no
`G`-action. (In the uses below, `A` carries a representation of another group `K`,
but that action is forgotten.) Write `X ⊗ A` for the representation in which `G`
acts on the first factor only. The module proves the following:

1. Character localization of the first factor commutes with `⊗ A`:
   `(X ⊗ A)_{U,θ} ≅ X_{U,θ} ⊗ A`, by `[v ⊗ a] ↦ [v] ⊗ a`. The iso is compatible
   with the descended action and with any later restriction and twist.
2. So the published functors `Φ⁻` and `Ψ⁻`, their iterates, the mirabolic
   derivative `Ψ⁻ ∘ (Φ⁻)^k`, the order-indexed mirabolic derivative, the `GL`
   restriction and rank casts, and the `k`-th `GL` derivative all commute with
   `· ⊗ A`. Each commutation is a natural isomorphism of functors on pairs `(X, A)`.
3. The published normalized binary product `A × B` with `B` a representation of
   `GL_0` is naturally isomorphic to `A ⊗ ULift B`, with `GL_a` acting on `A` only.

The module adds no hypotheses and asserts no proposition. Everything in it is a
definition: a linear equivalence, a functor, or a natural isomorphism, with its
naturality proved in the Lean code.

## Provenance

The content is internal to the formalization (derived). It consists of
ingredients that this formalization uses for the boundary case, where one factor
has rank zero, of Corollary 4.14(b) and (c) of BZ77
(`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`; printed p.458,
PDF p.19). There the source derives 4.14 from 4.13 (same page) and does not discuss
the rank-zero boundary separately. The general fact behind items 1 and 2, that the
localization functors `r_{U,θ}` commute with `π ↦ π ⊗ τ` for a representation `τ`
of another group, is stated in BZ77 Proposition 1.9(g) (printed p.445, PDF p.6),
where it is said to be directly verifiable. The proofs here are direct: every
isomorphism is `[v ⊗ a] ↦ [v] ⊗ a` or the identity, and it is checked on pure
tensors.

The bifunctor `tensorFunctor` has two carrier universes. The published functor
`Langlands.Derivative.PartialTensor.firstFactorFunctor` (in
`Langlands.Representation.Derivative.PartialDerivativeTensorStatement`) has the same
objects and morphisms, but it requires both groups to lie in one universe and both
carriers in one universe. This module neither imports nor uses it.

## Declarations

All declarations are in namespace `Langlands.Derivative.ZeroRankTensor`.

### Localization of the first tensor factor

Throughout, `ρ` is a complex representation of a group `G` on `V`, `U ≤ G` is a
subgroup with a character `θ : U →* ℂˣ`, and `W` is a complex vector space.
`BinaryTensor.firstFactor ρ W` is the published representation `g ↦ ρ g ⊗ id_W`
on `V ⊗ W`. `Jacquet.Localization.Coinvariants ρ U θ` is the published
`(U, θ)`-coinvariant quotient `V / ⟨ρ u v - θ u • v⟩`.

- `coinvariantsTensorForward ρ U θ W`: the linear map
  `(V ⊗ W)_{U,θ} → V_{U,θ} ⊗ W`, `[v ⊗ w] ↦ [v] ⊗ w`. It is the descent of
  `mk ⊗ id`, which is well defined because `[ρ u v] ⊗ w = θ u • ([v] ⊗ w)`.
- `coinvariantsTensorBackward ρ U θ W`: the linear map
  `V_{U,θ} ⊗ W → (V ⊗ W)_{U,θ}`, `[v] ⊗ w ↦ [v ⊗ w]`. It is the bilinear lift of
  the descent of `v ↦ (w ↦ [v ⊗ w])`.
- `coinvariantsTensorEquiv ρ U θ W`: the linear equivalence built from these two
  maps. Both composites are the identity on generators (`rfl` after
  `TensorProduct.ext'` and the localization `hom_ext`).
- `coinvariantsTensorEquiv_mk`: `[v ⊗ w] ↦ [v] ⊗ w` (`rfl`, a simp lemma).

### Tensoring with an inert factor

Here `G` and `K` are topological groups, and `SmoothRep.{0, u, v} ℂ G` is the
published category of smooth complex representations of `G` on carriers in
universe `v`.

- `tensorObj G K (X, A)`: the smooth representation of `G` on `X ⊗ A` in which
  `G` acts by `X` on the first factor and trivially on the second. The `K`-action
  on `A` is forgotten. Smoothness is the published
  `BinaryTensor.isSmooth_firstFactor`.
- `tensorFunctor G K : SmoothRep G × SmoothRep K ⥤ SmoothRep G`, the bifunctor
  `(X, A) ↦ X ⊗ A`. On morphisms `(f, h)` it is the published
  `BinaryTensor.firstFactorMap f h`, i.e. `f ⊗ h` on the carriers. Functoriality is
  the published `firstFactorMap_id` and `firstFactorMap_comp`. The carriers of `X`
  and `A` may lie in different universes `uV` and `uW`; the value lies in
  `max uV uW`.
- `tensorFunctor_obj` and `tensorFunctor_map`: the object and morphism formulas
  (`rfl`).
- `smoothRep_hom_ext`: two morphisms of smooth representations are equal if their
  underlying linear maps are. This restates the published
  `MixedProductTensor.smoothRep_hom_ext` with a hypothesis on linear maps.

### Localization functors commute with the inert factor

Take a subgroup `U ≤ G` with a character `θ`, a subgroup `M` of the normalizer of
`U` that preserves `θ` (`hθ`), a continuous homomorphism `e : H →* M`, and a
character `χ : H →* ℂˣ` with open kernel.

- `localizationFunctor U θ M hMU hθ e he χ hχ`: the composite of the published
  functors `Jacquet.Localization.smoothFunctor U θ M hMU hθ` (`(U, θ)`-localization
  as a smooth `M`-representation), `Mirabolic.continuousPullbackFunctor e he`
  (restriction along `e`), and `SmoothRep.twistFunctor χ hχ` (`h ↦ χ(h) • ·`). The
  published `Φ⁻` and `Ψ⁻` are both of this form.
- `localizationTensorEquiv … (X, A)`: the component
  `L(X ⊗ A) ≃ L(X) ⊗ A` as an equivalence of representations of `H`. Its linear
  map is `coinvariantsTensorEquiv`. Equivariance for `h ∈ H` reduces on generators
  to `χ(h) • [e(h) v ⊗ a] ↦ (χ(h) • [e(h) v]) ⊗ a`.
- `localizationTensorIso …`: the natural isomorphism
  `tensorFunctor G K ⋙ L ≅ (L.prod 𝟭) ⋙ tensorFunctor H K` with these components.
  Naturality is checked on generators `[v ⊗ a]`.
- `pullbackTensorIso K e he`: restriction along a continuous homomorphism
  `e : H →* G` commutes with `tensorFunctor`. The two sides agree on objects and
  morphisms, so every component is the identity.

### Pasting

- `prodCommIsoComp α β`: given squares
  `α : T₁ ⋙ M ≅ (L.prod 𝟭) ⋙ T₂` and `β : T₂ ⋙ M' ≅ (L'.prod 𝟭) ⋙ T₃`, the pasted
  square `T₁ ⋙ M ⋙ M' ≅ ((L ⋙ L').prod 𝟭) ⋙ T₃`. It is built from associators
  and whiskerings only.

### Minus functors and derivatives

In this section `F` is a `p`-adic field with topological data `T`, `ψ` is a unitary
additive character, and `K` is any topological group. The functors on the left of
each isomorphism are the published ones from `Langlands.Representation.Mirabolic`
and `Langlands.Representation.Derivative.Iteration`/`Homogeneity`.

Notation. As in BZ77 §3.1 (printed p.450), `P_m` is the mirabolic subgroup of
`GL_m`. The Library group `mirabolic n` is the mirabolic subgroup of `GL_(n+1)`,
so `mirabolic n = P_(n+1)`. Below, every group is written with its Lean index
followed by its BZ77 name, e.g. `mirabolic n = P_(n+1)`.

- `phiMinusTensorIso K T ψ n`:
  `tensorFunctor (mirabolic (n+1)) K ⋙ Φ⁻ ≅ (Φ⁻.prod 𝟭) ⋙ tensorFunctor (mirabolic n) K`,
  where `Φ⁻ = Mirabolic.phiMinus T ψ n` goes from `mirabolic (n+1) = P_(n+2)` to
  `mirabolic n = P_(n+1)`. This is
  `localizationTensorIso` at the published data of `Mirabolic.phiMinus`: the
  radical with character `mirabolicTheta ψ n`, the successor subgroup with
  `successorContinuousEquiv`, and the twist `phiMinusCharacter`.
- `psiMinusTensorIso K T n`: the same for `Mirabolic.psiMinus T n`, from
  `mirabolic n = P_(n+1)` to `GL_n`: the radical with the trivial character, the
  Levi subgroup with `leviContinuousEquiv`, and the twist `psiMinusCharacter`.
- `phiMinusIterateTensorIso K T ψ n k`: the same for the iterate
  `phiMinusIterate T ψ n k` from `mirabolic (n+k) = P_(n+k+1)` to
  `mirabolic n = P_(n+1)`. Defined by recursion on `k`:
  the identity for `k = 0`, and `prodCommIsoComp` of the one-step square at rank
  `n + k` with the square for `k`.
- `mirabolicDerivativeTensorIso K T ψ n k`: the same for
  `mirabolicDerivative T ψ n k = phiMinusIterate T ψ n k ⋙ Ψ⁻`, from
  `mirabolic (n+k) = P_(n+k+1)` to `GL_n`, by pasting the previous two squares.
- `mirabolicRankCastTensorIso K T h` and `generalLinearRankCastTensorIso K T h`:
  the mirabolic and `GL` rank casts along `h : a = b` commute with
  `tensorFunctor`. After `subst h`, both sides are the same functor.
- `mirabolicDerivativeOfOrderTensorIso K T ψ N k hk`: the same for the
  order-indexed `mirabolicDerivativeOfOrder T ψ N k hk`
  (`0 < k ≤ N + 1`, from `mirabolic N = P_(N+1)` to `GL_(N+1-k)`). For example,
  `N = 0, k = 1` is the derivative from `mirabolic 0 = P_1` to `GL_0`. This pastes
  the rank-cast
  square along `mirabolic_rank_eq_of_order hk` with
  `mirabolicDerivativeTensorIso` at `(N + 1 - k, k - 1)`.
- `generalLinearRestrictionTensorIso K T n`: the restriction
  `generalLinearRestriction T n` from `GL_(n+1)` to `mirabolic n = P_(n+1)` commutes with
  `tensorFunctor`. This is `pullbackTensorIso` along the subgroup inclusion.
- `generalLinearDerivativePositiveTensorIso K T ψ n k`: the same for
  `generalLinearDerivativePositive T ψ n k` from `GL_(n+k+1)` to `GL_n`: the
  restriction to `mirabolic (n+k) = P_(n+k+1)` followed by the mirabolic derivative.
  It pastes the two previous squares.
- `generalLinearDerivativeTensorIso K T ψ N k hk`: the same for the published
  `k`-th `GL` derivative `generalLinearDerivative T ψ N k hk` (`k ≤ N`, from
  `GL_N` to `GL_(N-k)`). For `k = 0` the derivative is the identity functor and
  the square is the identity. For `k + 1` the square pastes the rank cast along
  `rank_eq_of_succ_le hk` with the positive-order square at `(N - (k+1), k)`.

### The binary product with a `GL_0` factor

- `binaryRightZeroEquiv T a (A, B)`: for `A` on `GL_a` and `B` on `GL_0`, an
  equivalence of `GL_a`-representations between the published normalized product
  `(T.binaryNormalizedProductFunctor a 0).obj (A, B)` and
  `tensorObj (A, ULift B)`. Here `ULift B` is `MixedProductTensor.liftFunctor`,
  which moves the carrier of `B` into universe `max uV uF`, so that both sides
  have carriers in the universe of the product. The equivalence is the published
  `T.binaryRightZeroTensorEquiv rfl (A, B)` onto the `b = 0` model `A ⊗ B`,
  followed by `id ⊗ ULift.up`. In the published model, `GL_(a+0)` acts on `A`
  through the reindexing `GL_(a+0) ≅ GL_a`. Since `a + 0 = a` holds by definition,
  this reindexing is definitionally the identity, so equivariance holds by `rfl`
  on pure tensors.
- `binaryRightZeroIso T a`: the natural isomorphism
  `T.binaryNormalizedProductFunctor a 0 ≅ (𝟭.prod liftFunctor) ⋙ tensorFunctor (GL_a) (GL_0)`
  with these components. Naturality comes from the published
  `binaryRightZeroTensorEquiv_naturality`, transported along `id ⊗ ULift.up`.

## Imports

The project imports are the published modules
`Langlands.Representation.Derivative.Homogeneity` (derivative functors, rank
casts, restriction) and `Langlands.Representation.Mirabolic.MixedProducts`
(lifting functor, smooth-hom extensionality, binary products). They supply
definitions only, and no proposition of theirs is used as a hypothesis.
