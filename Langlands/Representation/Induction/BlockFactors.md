# Normalized induction of block factors `i(σ_1, …, σ_r)`

Author: Worker 23.

This module constructs the representation `i(σ_1, …, σ_r)` of `GL_n(F)`. The
inputs are representations `σ_i` of the diagonal blocks `GL_{n_i}(F)` of an
ordered block shape `B` with `n = n_1 + ⋯ + n_r`. The construction has two
steps, and each step is a published construction:

1. The actual block Levi `B.Levi F = ∏_i GL_{n_i}(F)` of `Group/GL/Blocks` acts
   on the tensor product `σ_1 ⊗ ⋯ ⊗ σ_r`, each block on its own factor. This is
   the published external tensor product `FiniteTensor.external` of
   `Tensor/Finite`, on the algebraic tensor product `PiTensorProduct ℂ V`.
2. Normalized parabolic induction from the standard upper block parabolic
   `B.parabolic F` is applied to this Levi representation, using the published
   `normalizedInducedOf` and `normalizedParabolicInduced` of
   `Induction/Parabolic`.

No new induction or tensor primitive is introduced. All definitions unfold to
these published ones by `rfl`.

## Block tensor product

Here `F` is any commutative ring.

- `B.blockTensor σ` is an abbreviation for `FiniteTensor.external σ`. It is the
  representation of `B.Levi F` on `PiTensorProduct ℂ V` in which
  `m = (m_1, …, m_r)` acts by `σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)`.
- `blockTensor_tprod` records the action on pure tensors:
  `m · (v_1 ⊗ ⋯ ⊗ v_r) = σ_1(m_1) v_1 ⊗ ⋯ ⊗ σ_r(m_r) v_r`.

## Generic layer

Here `F` is a commutative ring with a topology making it a topological ring. The
normalizing Levi character is supplied as data,
`χ : Induction.SmoothCharacter ℂ (B.Levi F)`, as in `Induction/Parabolic`.

- `B.productInducedOf χ σ` is `B.normalizedInducedOf χ (B.blockTensor σ)`
  (`productInducedOf_eq`).
- `productInducedOf_covariant` states the defining covariance. For `p` in the
  parabolic with Levi part `m = B.leviProjection F p`, and every `g`,
  `f(p g) = χ(m) • (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f g)`.
- `productInducedOf_apply` states the action by right translation:
  `(g · f)(x) = f(x g)`. Both lemmas hold by definition.
- `isSmooth_productInducedOf` proves the result smooth.
- `productInducedOfMap χ f` sends a family of block intertwiners
  `f_i : σ_i → τ_i` to the induced intertwiner. It is the published
  `normalizedInducedOfMap` of the tensor product map `FiniteTensor.externalMap f`,
  so it acts on functions by postcomposition with `f_1 ⊗ ⋯ ⊗ f_r`
  (`productInducedOfMap_apply`). Identity and composition laws are proved
  (`productInducedOfMap_id`, `productInducedOfMap_comp`).
- `productInductionFunctorOf B χ` is the composite of the published functors
  `FiniteTensor.externalFunctor` and `B.normalizedInductionFunctorOf χ`. It goes
  from the product category `∀ i, SmoothRep ℂ (GL_{n_i}(F))` of families of
  smooth block representations to `SmoothRep ℂ (GL_n(F))`.
  `productInductionFunctorOf_obj` identifies its representations with
  `productInducedOf`.

The generic layer is a derived generalization: it needs only a topological
commutative ring and an open-kernel character. It is instantiated below for
every p-adic field.

## p-adic layer

For a p-adic field `F : PadicField p` with a supplied realization `T` (its
topology, valuation and local-field structure):

- `T.normalizedProductInduced B σ` is `T.normalizedParabolicInduced B
  (B.blockTensor σ)` (`normalizedProductInduced_eq`). Its normalizing character
  is the published `T.leviHalfCharacter B`, the positive square root of the
  explicit block modulus `δ_P` of `Group/GL/BlockModulus`. The type displays
  the inducing parabolic representation as
  `twist (T.parabolicHalfModulus B) ((B.blockTensor σ) ∘ m)`.
- `normalizedProductInduced_covariant` states the normalization with the
  explicit square root:
  `f(p x) = sqrt(δ_P(m)) • (σ_1(m_1) ⊗ ⋯ ⊗ σ_r(m_r)) (f x)`,
  with `m` the Levi part of `p`.
- `isSmooth_normalizedProductInduced`, `normalizedProductInducedMap` (with
  `_id` and `_comp`), `normalizedProductCompactInduced`,
  `normalizedProductCompactInclusion` and `normalizedProductInductionFunctor`
  (with `_obj`) specialize the generic layer and the p-adic constructions of
  `Induction/Parabolic`.
- `PadicField.canonicalNormalizedProductInduced` and
  `canonicalNormalizedProductInductionFunctor` use the accepted canonical
  realization, so every algebraic `PadicField.{u} p` with prime `p` is covered
  in its own field universe.

The topological-ring structure of `F.Carrier` is obtained from the
realization's topology, valuation and local-field instances. This is the same
private derivation as in `Induction/Parabolic`.

## Relation to other modules

The published `Whittaker/InducedStatement` writes the unnormalized induced
representation inline as `Induction.smoothInduced (B.parabolic F.Carrier)
((FiniteTensor.external π).comp (B.leviProjection F.Carrier))`. The present
module uses the same block tensor `FiniteTensor.external`, and then the
normalized induction of `Induction/Parabolic`. That statement is not changed.

## Universes and scope

The coefficient field is `ℂ`. The block factors share one carrier universe
`uV`; the field universe `uF` is independent. The tensor product lies in
`Type uV`, and the induced carrier lies in `Type (max uF uV)`. The factors may
be arbitrary representations: no irreducibility, smoothness, admissibility,
topology or finite dimension is imposed on them for the construction. Henniart
uses irreducible smooth `π_i`; this module enlarges the domain to all
representations, and the functor takes smooth ones. Every ordered positive
block shape is allowed, so every rank `n ≥ 1` and every number of blocks is
covered.

## Source correspondence

- Henniart (2002), section 2.5, printed pages 594--595 / PDF pages 8--9: "Si
  π1,...,πr sont des représentations lisses irréductibles respectivement de
  GLn1(F),...,GLnr(F), nous notons i(π1,...,πr) la représentation de GLn(F),
  n = n1+···+nr, obtenue par induction parabolique normalisée: nous utilisons
  le sous-groupe parabolique de GLn(F) formé des matrices triangulaires
  supérieures par blocs, les blocs diagonaux étant de tailles successives
  n1,...,nr le long de la diagonale descendante." This is
  `normalizedProductInduced` with `B` the shape `(n_1, …, n_r)`: the first
  block is the top-left one, and `B.parabolic` is upper block-triangular. Henniart
  remarks that `i(π_1, …, π_r)` is smooth, not necessarily irreducible, and of
  finite length. Smoothness is proved here. Finite length is not claimed.
- Zelevinsky (1980), section 1.5, printed page 171 / PDF page 8: for an ordered
  partition `α = (n_1, …, n_r)` the tensor product functor
  `Alg G_{n_1} × ⋯ × Alg G_{n_r} → Alg G_α`, `(ρ_1, …, ρ_r) ↦ ρ_1 ⊗ ⋯ ⊗ ρ_r`,
  with `G_α = G_{n_1} × ⋯ × G_{n_r}` embedded block-diagonally (section 1.1,
  printed page 170). This is `blockTensor` and `FiniteTensor.externalFunctor`.
  Section 1.7, printed page 173 / PDF page 10, writes the product
  `ρ_1 × ρ_2 = i_{(n),(k,l)}(ρ_1 ⊗ ρ_2)` and
  `(ρ_1 × ρ_2) × ρ_3 = i_{(n),(k,l,m)}(ρ_1 ⊗ ρ_2 ⊗ ρ_3)` in the Grothendieck
  group. Only the representation `i_{G,M}(ρ_1 ⊗ ⋯ ⊗ ρ_r)` is constructed here,
  not the ring structure or associativity.
- Bernstein--Zelevinsky (1977), sections 1.8, 2.2 and 2.3, printed pages 444
  and 446: the normalized functors `I_{U,1}` and `i_{G,M}` and the block-diagonal
  standard subgroups `G_α` of `GL(n, F)`. The conventions, and the relation
  between the smooth and compact variants, are as recorded in
  `Induction/Parabolic.md`. In particular, the source's `mod_U` is replaced by
  the explicit block formula, and its identification with the Haar module is a
  separate theorem obligation that is not assumed.

The originals were read at these pages. Registered sources:

- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`,
  section 2.5, pages 594--595.
- `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  sections 1.1, 1.5 and 1.7, pages 170--173.
- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  sections 1.8 and 2.1--2.3, pages 444 and 446.

## Not claimed

This pair proves only the intrinsic construction obligations: covariance, right
translation, smoothness, map laws and functoriality. It does not claim
irreducibility, finite length, admissibility, exactness, associativity
(`i(i(σ_1, σ_2), σ_3) ≅ i(σ_1, σ_2, σ_3)`), compatibility with contragredients
or twists, or the equality of the smooth and compactly supported variants.
Those are separate theorem obligations.
