# The binary normalized product in all ranks

Author: Worker 837.

This module constructs the binary normalized product `A × B` of smooth complex
representations `A` of `GL_a(F)` and `B` of `GL_b(F)`, for every pair of ranks
`a b : ℕ`, including rank zero. The principal declaration is

```
Langlands.PadicField.TopologicalData.binaryNormalizedProductFunctor.{uF, uV} T a b :
  letI := T.topology
  (SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) ⥤
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier)
```

for every prime `p`, every `p`-adic field `F : PadicField.{uF} p` and every
topological datum `T : F.TopologicalData`. It is a functor on the product
category: objects are pairs `(A, B)` of smooth representations, and morphisms
are pairs `(f₁, f₂)` of intertwining maps. The input carrier universe `uV` is
independent of the field universe `uF`. The output carriers lie in
`max uF uV`, the universe of the induced function spaces. The inputs are
arbitrary smooth representations. They need not be finite-dimensional,
admissible, of finite length or irreducible.

The definition splits into three cases.

- `a = 0`: the lift of `A ⊗ B`. `GL_{a+b}(F)` acts through the rank cast to
  `GL_b(F)` on the second factor, and trivially on the first factor.
- `a ≠ 0` and `b = 0`: the lift of `A ⊗ B`. `GL_{a+b}(F)` acts through the rank
  cast to `GL_a(F)` on the first factor, and trivially on the second factor.
- `0 < a` and `0 < b`: the published upper-block normalized product
  `T.normalizedProductInductionFunctor` of `Induction/BlockFactors` on the
  published binary shape `GeneralLinear.BlockShape.binary a b`.

A rank-zero carrier is never dropped or replaced by `ℂ`. It stays a tensor
factor, on which the trivial group `GL_0(F)` necessarily acts trivially. When
both ranks are zero the `a = 0` branch applies; the result is `A ⊗ B` with
trivial action (`binaryZeroZeroTensorEquiv`). The module modifies no existing
Library module. Its only new hypotheses are the case hypotheses on the ranks
(`a = 0`, `0 < a`, and so on), which are arguments of the case declarations.

## Rank-zero general linear groups

These declarations are in the namespace `Langlands.GeneralLinear`.

- `subsingleton_of_rank_eq_zero hn`: if `n = 0`, then `GL_n(R)` has at most one
  element, because a `0 × 0` matrix has no entries.
- `representation_apply_of_rank_eq_zero hn ρ g`: if `n = 0`, then every
  representation `ρ` of `GL_n(R)` satisfies `ρ g = 1`.

## A vanishing external tensor product

`FiniteTensor.externalMap_eq_zero_of_eq_zero f i₀ h`: if one member `f i₀` of a
family of intertwiners is zero, then the external tensor product
`FiniteTensor.externalMap f` of `Tensor/Finite` is zero. Every pure tensor goes
to a pure tensor with a zero coordinate.

## Tensor products with one acting factor

These declarations are in the namespace `Langlands.BinaryTensor`. Here `G` is a
group and all modules are complex vector spaces.

- `secondFactor V σ` is the representation `1 ⊗ σ` of `G` on `V ⊗ W`:
  `g (v ⊗ w) = v ⊗ σ(g) w` (`secondFactor_apply`, `secondFactor_tmul`). It is
  `Representation.tprod` of the trivial representation on `V` and `σ`.
- `firstFactor ρ W` is the representation `ρ ⊗ 1` of `G` on `V ⊗ W`:
  `g (v ⊗ w) = ρ(g) v ⊗ w` (`firstFactor_apply`, `firstFactor_tmul`).
- `secondFactorMap f g`, for a linear map `f : V → V'` and an intertwiner
  `g : σ → σ'`, is the intertwiner `f ⊗ g` from `secondFactor V σ` to
  `secondFactor V' σ'`. `secondFactorMap_tmul` and
  `secondFactorMap_toLinearMap` give its values. `secondFactorMap_id` and
  `secondFactorMap_comp` are the functor laws. `secondFactorMap_zero_left` and
  `secondFactorMap_zero_right` say that `f ⊗ g` is zero if `f = 0` or `g = 0`.
- `firstFactorMap f g`, for an intertwiner `f : ρ → ρ'` and a linear map
  `g : W → W'`, is the intertwiner `f ⊗ g` from `firstFactor ρ W` to
  `firstFactor ρ' W'`, with the corresponding lemmas `firstFactorMap_tmul`,
  `_toLinearMap`, `_id`, `_comp`, `_zero_left` and `_zero_right`.

### Pullbacks and universe lifts

- `compMap f φ` and `compEquiv e φ` pull an intertwiner and an intertwining
  equivalence back along a group homomorphism `φ : H →* G`. The underlying
  linear maps are unchanged (`compMap_apply`, `compEquiv_apply`).
- `lift ρ` is the representation on `ULift V` obtained by conjugating `ρ` with
  `ULift.up`: `lift ρ g v = up (ρ g (down v))` (`lift_apply`). The target
  universe is an explicit parameter.
- `liftEquiv ρ : ρ.Equiv (lift ρ)` is the cross-universe intertwining
  equivalence with forward map `ULift.up` and inverse `ULift.down`
  (`liftEquiv_apply`, `liftEquiv_symm_apply`).
- `liftMap f` is the intertwiner `up ∘ f ∘ down` between the lifts
  (`liftMap_apply`).

The library module `Category/UniverseLift` provides a similar lift, but its
import closure contains classification modules. This module therefore defines
its own lift from `ULift.moduleEquiv`.

### The tensor unit

- `secondFactorUnitEquiv σ` is the intertwining equivalence from
  `secondFactor (ULift ℂ) σ` to `σ`, `c ⊗ w ↦ (down c) • w`
  (`secondFactorUnitEquiv_tmul`). `secondFactorUnitEquiv_naturality` says it
  commutes with `id ⊗ g` and `g` for every intertwiner `g : σ → σ'`.
- `firstFactorUnitEquiv ρ` is the intertwining equivalence from
  `firstFactor ρ (ULift ℂ)` to `ρ`, `v ⊗ c ↦ (down c) • v`
  (`firstFactorUnitEquiv_tmul`). `firstFactorUnitEquiv_naturality` says it
  commutes with `f ⊗ id` and `f`.

### The rank-zero tensor models

Here `R` is a commutative ring. The rank casts use the published
entry-preserving reindex `GeneralLinear.reindex (finCongr h)` of
`Group/GL/RankReindex`.

- `rankZeroLeft ha V σ`, for `ha : a = 0` and a representation `σ` of
  `GL_b(R)` on `W`, is the representation of `GL_{a+b}(R)` on `V ⊗ W` given by
  `secondFactor V σ` composed with the reindex `GL_{a+b}(R) ≃* GL_b(R)` along
  `a + b = b`. `rankZeroLeft_tmul` gives the action on pure tensors:
  `g (v ⊗ w) = v ⊗ σ(reindex g) w`.
- `rankZeroRight hb ρ W`, for `hb : b = 0` and a representation `ρ` of
  `GL_a(R)` on `V`, is the representation of `GL_{a+b}(R)` on `V ⊗ W` given by
  `firstFactor ρ W` composed with the reindex along `a + b = a`
  (`rankZeroRight_tmul`).
- `rankZeroLeftMap ha f g` is the intertwiner `up ∘ (f ⊗ g) ∘ down` between
  the lifts of the `a = 0` models. It is `liftMap` of `compMap` of
  `secondFactorMap f g`. `rankZeroLeftMap_apply` gives its values;
  `rankZeroLeftMap_id` and `rankZeroLeftMap_comp` are the functor laws;
  `rankZeroLeftMap_zero_left` and `rankZeroLeftMap_zero_right` say that it is
  zero if `f = 0` or `g = 0`.
- `rankZeroRightMap hb f g` is the same construction for the `b = 0` models,
  with the corresponding lemmas.

The lift target universe in these maps is the universe of `R`. In the p-adic
layer `R = F.Carrier`, so the lifted models lie in `max uF uV`, the universe of
the positive-rank product.

### Smoothness

For a topological group `G`:

- `isSmooth_secondFactor` and `isSmooth_firstFactor`: if the acting factor is
  smooth, then so is the tensor representation. A pure tensor `v ⊗ w` is fixed
  by every open subgroup fixing the acting coordinate, and smooth vectors are
  closed under addition.
- `isSmooth_lift`: the lift of a smooth representation is smooth. It is the
  image of `liftEquiv`, a surjective intertwiner.
- `isSmooth_trivial`: a trivial representation is smooth, with `⊤` as the
  open fixing subgroup.

## The p-adic layer

The remaining declarations are in the namespace
`Langlands.PadicField.TopologicalData`. Here `T` is a topological datum on the
`p`-adic field `F`, and every statement uses the topology `T.topology`. The
input category is `SmoothRep.{0, uF, uV} ℂ (GL_a(F)) ×
SmoothRep.{0, uF, uV} ℂ (GL_b(F))`.

`normalizedProductInducedMap_eq_zero B f h`: for any published block shape `B`,
if the external tensor product of the intertwiner family `f` is zero, then the
published `T.normalizedProductInducedMap B f` is zero.

### Positive ranks

Here `ha : 0 < a` and `hb : 0 < b`.

- `binaryPairFamilyFunctor ha hb` is the functor from pairs to dependent
  families indexed by the blocks `Fin 2` of `BlockShape.binary a b ha hb`. It
  is `Functor.pi'` of the projections: block `0` gets `A` and block `1` gets
  `B` (`binaryPairFamilyFunctor_obj_zero`, `_obj_one`). On morphisms, block
  `0` gets `f₁` and block `1` gets `f₂` (`_map_zero`, `_map_one`). All four
  hold by definition.
- `binaryPositiveProductFunctor ha hb` is `binaryPairFamilyFunctor ha hb ⋙
  T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)`. It
  reuses the published normalized product without modification.
  - `binaryPositiveProductFunctor_obj`: the representation of `(A, B)` is the
    published `T.normalizedProductInduced (BlockShape.binary a b ha hb)` of the
    family `(A, B)`. It acts on smooth functions
    `f : GL_{a+b}(F) → A ⊗ B` from the published normalized induction.
  - `binaryPositiveProductFunctor_map`: the map of `(f₁, f₂)` is the published
    `T.normalizedProductInducedMap` of the family `(f₁, f₂)`. It applies the
    external tensor product `f₁ ⊗ f₂` pointwise.
  - `binaryPositiveProductFunctor_apply`: the group acts by right translation,
    `(g · f)(x) = f(x g)`.
  - `binaryPositiveProductFunctor_covariant`: for `g` in the upper block
    parabolic `P` of the binary shape, with Levi part `m = (m₀, m₁)`,
    `f(g x) = sqrt(δ_P(m)) • (A(m₀) ⊗ B(m₁)) (f x)`. Here `δ_P` is the
    published `T.leviModulus`, and the square root is taken in `ℝ≥0`. This is
    the published `normalizedProductInduced_covariant` on the binary shape, so
    the normalization is the published positive square root
    (`T.leviHalfCharacter`, `T.parabolicHalfModulus`).

The functor laws in the positive case are those of the published
`normalizedProductInductionFunctor` and of `Functor.pi'`.

### Rank-zero tensor models

- `binaryLeftZeroTensorObj ha X` is the smooth representation
  `lift (rankZeroLeft ha X.1 X.2)` of `GL_{a+b}(F)`, for `ha : a = 0`. Its
  carrier is `ULift (X.1 ⊗ X.2)` in `max uF uV`. It is smooth by
  `isSmooth_secondFactor`, by `isSmooth_comp` along the continuous reindex
  (`continuous_reindex_finCongr`), and by `isSmooth_lift`.
- `binaryLeftZeroTensorFunctor ha` is the bifunctor with these objects. The
  map of `(f₁, f₂)` is `rankZeroLeftMap ha f₁ f₂`, which is `up ∘ (f₁ ⊗ f₂) ∘
  down`. The functor laws come from `rankZeroLeftMap_id` and
  `rankZeroLeftMap_comp`. `binaryLeftZeroTensorFunctor_obj`, `_map` and
  `_map_apply` record the representation, the map and its values; all three
  hold by definition.
- `binaryRightZeroTensorObj hb X`, `binaryRightZeroTensorFunctor hb` and their
  `_obj`, `_map` and `_map_apply` lemmas are the same construction for
  `hb : b = 0`, with `rankZeroRight`, `isSmooth_firstFactor` and
  `rankZeroRightMap`.

### The product in all ranks

- `binaryNormalizedProductFunctor a b` is defined as `if ha : a = 0 then
  binaryLeftZeroTensorFunctor ha else if hb : b = 0 then
  binaryRightZeroTensorFunctor hb else binaryPositiveProductFunctor`. In the
  last branch the positivity proofs are `Nat.pos_of_ne_zero` of the two
  negated hypotheses.
- Literal case equations hold by definition:
  `binaryNormalizedProductFunctor_zero_left b` (the case `0, b`),
  `binaryNormalizedProductFunctor_succ_zero a` (the case `a + 1, 0`) and
  `binaryNormalizedProductFunctor_succ_succ a b` (the case `a + 1, b + 1`).
- Hypothesis-based case equations hold for ranks given only by hypotheses,
  such as `n - n`: `binaryNormalizedProductFunctor_of_left_eq_zero` (from
  `a = 0`), `binaryNormalizedProductFunctor_of_right_eq_zero` (from `a ≠ 0` and
  `b = 0`) and `binaryNormalizedProductFunctor_of_pos` (from `0 < a` and
  `0 < b`).
- `binaryNormalizedProductLeftZeroIso`, `binaryNormalizedProductRightZeroIso`
  and `binaryNormalizedProductPositiveIso` are the natural isomorphisms
  `eqToIso` of the three hypothesis-based equations. They identify the
  product with the tensor model or with the positive product. In particular,
  `binaryNormalizedProductPositiveIso ha hb` is the natural isomorphism to the
  published positive-block product.

### Explicit tensor-model equivalences

Each equivalence is a `Representation.Equiv` from the representation of the
product of `X = (A, B)` to a tensor model on the unlifted carrier `A ⊗ B`.
Each naturality lemma states that, for every morphism `f = (f₁, f₂)` from `X`
to `Y`, the equivalence at `Y` applied to the image of `v` under the product
of `f` equals `(f₁ ⊗ f₂)` applied to the equivalence at `X` of `v`.

- `binaryLeftZeroTensorEquiv ha X`, for `ha : a = 0`, has target
  `rankZeroLeft ha A B`. Its forward map is the component at `X` of
  `binaryNormalizedProductLeftZeroIso ha`, followed by `ULift.down`. For a
  literal `0, b`, the case equation is `rfl`. Its naturality is
  `binaryLeftZeroTensorEquiv_naturality`. It is the naturality square of
  `binaryNormalizedProductLeftZeroIso`, evaluated at `v` and followed by
  `ULift.down`; the map of the tensor model is `up ∘ (f₁ ⊗ f₂) ∘ down` by
  definition.
- `binaryZeroZeroTensorEquiv ha hb X`, for `a = 0` and `b = 0`, has target the
  trivial representation of `GL_{a+b}(F)` on `A ⊗ B`. It is
  `binaryLeftZeroTensorEquiv` followed by the identity linear map, which
  intertwines because every representation of `GL_0` is trivial. Its naturality
  is `binaryZeroZeroTensorEquiv_naturality`.
- `binaryRightZeroTensorEquiv hb X`, for `hb : b = 0`, has target
  `rankZeroRight hb A B`. If `a ≠ 0`, its forward map is the component of
  `binaryNormalizedProductRightZeroIso` followed by `ULift.down`. If also
  `a = 0`, it is `binaryZeroZeroTensorEquiv` followed by the identity linear
  map. Its naturality is `binaryRightZeroTensorEquiv_naturality`, proved in
  both cases.

### The unit

- `binaryProductUnit` is the smooth representation of `GL_0(F)` on
  `ULift.{uV} ℂ` with the trivial action (`binaryProductUnit_representation`).
  It is one-dimensional (`finrank_binaryProductUnit`). The lift `ULift.{uV}`
  puts it in the input universe `uV`.
- `binaryProductLeftUnitEquiv B` is an intertwining equivalence from
  `1 × B` to `lift (B ∘ reindex)`. The reindex is the rank cast
  `GL_{0+b}(F) ≃* GL_b(F)` along `Nat.zero_add b`, and the lift is to the
  output universe `max uF uV`. It is `binaryLeftZeroTensorEquiv rfl`, then the
  pulled-back `secondFactorUnitEquiv` (`c ⊗ w ↦ (down c) • w`), then
  `liftEquiv` (`ULift.up`). `binaryProductLeftUnitEquiv_naturality` says that,
  for every `f : B ⟶ B'`, the equivalence at `B'` applied to the image of `v`
  under the product of `(𝟙, f)` is `up (f (down (e_B v)))`.
- `binaryProductRightUnitEquiv A` and `binaryProductRightUnitEquiv_naturality`
  are the same construction for `A × 1`. They use `binaryRightZeroTensorEquiv
  rfl`, the rank cast along `Nat.add_zero a` and `firstFactorUnitEquiv`.

These unit equivalences are linear equivalences of the underlying spaces that
intertwine the actions. They are not equalities of objects.

### Zero maps and zero objects

- `binaryLeftZeroTensorFunctor_map_eq_zero`,
  `binaryRightZeroTensorFunctor_map_eq_zero` and
  `binaryPositiveProductFunctor_map_eq_zero` say that each of the three case
  functors sends a morphism `(f₁, f₂)` with `f₁ = 0` or `f₂ = 0` to zero. The
  positive case uses `FiniteTensor.externalMap_eq_zero_of_eq_zero` and
  `normalizedProductInducedMap_eq_zero`.
- `binaryNormalizedProductFunctor_map_eq_zero`: the product of a pair of maps
  with one zero member is zero, in all ranks. The proof transfers the three
  case lemmas along the case isomorphisms.
- `isZero_binaryNormalizedProductFunctor_obj`: if `A` or `B` is a zero object,
  then the product of `(A, B)` is a zero object, in all ranks. The identity of
  the product is the image of the identity pair, and that pair has a zero
  member.

## Universes and scope

The coefficient field is `ℂ`, and the coefficient universe of `SmoothRep` is
`0`. The field universe `uF` and the input carrier universe `uV` are
independent universe parameters of the principal declaration. Every branch
lands in `SmoothRep.{0, uF, max uF uV}`. The positive branch lands there
because the published induced carrier lies in `max uF uV`. The zero-rank
branches land there because their tensor carrier, in `uV`, is lifted by
`ULift.{uF}`.

This module proves only the construction, its case identifications, the
explicit tensor-model and unit equivalences with their naturality, the functor
laws, and the zero-map and zero-object laws. It proves no associativity or
commutativity of the product, no exactness, no compatibility with derivatives,
no filtration, and no irreducibility or finite-length statement. The unit
equivalences are not shown to satisfy any coherence law of a monoidal
structure.

## Imports

The direct project imports are `Group/GL/MirabolicOppositeIntersection` (for
`BlockShape.binary`), `Group/GL/RankReindex` (for the continuity of the rank
casts), `Induction/BlockFactors` (for the normalized product) and
`Smooth/Transfer/SubquotientProof` (for `isSmooth_of_surjective`). The
transitive project import closure consists of 32 modules in the `Group/GL`,
`LocalField`, `Representation/Category/Basic`, `Representation/Smooth`,
`Representation/Induction` (`Definitions`, `Parabolic`, `BlockFactors`),
`Representation/Tensor/Finite`, `Representation/Jacquet/PositiveCharacter` and
`Representation/Twist` layers. It contains no derivative, adjunction, duality,
pairing, segment, socle or classification module.

## Source correspondence

The original source is Bernstein–Zelevinsky (1977), registered as
`bernstein-zelevinsky-1977-induced-i` (SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`). No
erratum for it was found in the central library or the project notes.

- Section 1.8, printed page 444 (PDF page 5), defines the normalized induction
  `I_{U,θ}(ρ)`. Its functions satisfy
  `f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))`, and `G` acts by right
  translation, `f ↦ (g' ↦ f(g' g))`. The positive branch uses the published normalized
  induction with `θ = 1`, the upper block unipotent radical and the explicit
  block modulus. The conventions and their relation to the source's `mod_U`
  are those recorded in `Induction/Parabolic.md` and
  `Induction/BlockFactors.md`. The right-translation action is
  `binaryPositiveProductFunctor_apply`, and the covariance is
  `binaryPositiveProductFunctor_covariant`.
- Section 4.1, printed page 454 (PDF page 15): for a partition
  `(n_1, …, n_r)` of `n` and `ρ_i ∈ Alg G_{n_i}`, "Denote by
  `ρ_1 × ... × ρ_r ∈ Alg G` the representation `i_{G,M}(ρ_1 ⊗ ... ⊗ ρ_r)`,
  where `M = G_{n_1} × ... × G_{n_r}` is a standard subgroup of `G`". For
  `r = 2` and positive `a` and `b`, this is `binaryPositiveProductFunctor`.
- Section 4.12, case (I), printed pages 456–458 (PDF pages 17–19), defines the
  product functor `Alg G_k × Alg G_m → Alg G_n`, `(ρ, τ) ↦ ρ × τ`, with
  `n = k + m`. It factors as `Alg M_1 × Alg M_2 → Alg M → Alg G` with
  `M = G_k × G_m`, then `i_{U,ε}` with `U` the upper block unipotent subgroup
  and `ε = 1`. Printed page 458 notes that "the definition (I) coincides with
  the one given in 4.1". The present module packages the positive case in the same way:
  a bifunctor on the product category, factored through the dependent block
  family and the published block tensor and normalized induction.
- Sections 4.3–4.6, printed pages 454–455 (PDF pages 15–16), use rank zero. For
  `π ∈ Alg G_n` the derivatives `π^(k)` lie in `Alg G_{n−k}` for
  `k = 0, 1, …, n`, so `π^(n)` is a representation of `G_0`. Theorem 4.4 says
  that `π^(n) = 1` is one-dimensional for irreducible cuspidal `π`. Lemma 4.5
  says that `(ρ × ω)^(k)` is glued from `ρ^(i) × ω^(k−i)`, and the
  representation ring `R = ⊕ R_n` runs over `n = 0, 1, …`. These products can
  have a factor in `Alg G_0`.

The extension to rank zero is an internal derived construction. The printed
definition in section 4.1 uses partitions with positive parts, which is why the
published `BlockShape` requires positive blocks. The source does not spell
out the product with a `G_0` factor. The module implements the convention
implicit in sections 4.3–4.6: `G_0` is the trivial group, a representation of
`G_0` is a vector space, and a product with a rank-zero factor is the tensor
product with that factor's carrier. This matches section 1.8's remark on
printed page 445 that if `MU = G`, then `I_{U,θ}(ρ)` "acts on the same space as
`ρ`". The module does not claim that the printed positive-partition definition
already contains this extension. The pair-category packaging, the explicit
universe lifts and the rank casts are also internal. The one-dimensional unit
is the trivial representation `1` of `G_0`, as in Theorem 4.4.
