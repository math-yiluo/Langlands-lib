# Derivatives of left mixed products with a `GL_0` factor

Module `Langlands.Representation.Derivative.LeftMixedProductZeroRank`, namespace
`Langlands.Derivative.LeftMixedProductZeroRank`.

This module constructs the `GL` rank `k = 0` case of item 1 of
`Langlands.Derivative.LeftMixedProductDerivative` (BZ77 Corollary 4.14(a)), for an
arbitrary smooth representation `A` of `GL_0`, not only the unit. It is an ingredient
for the proof task `7e19f753` (BZ77 4.14(a) in all `GL` ranks). It does not prove the
positive-rank case, the vanishing clause `LeftMixedProductDerivativeVanishing`, or the
target theorem itself. For `k = 0` the vanishing clause has no instances, because
`r + 1 < i ≤ 0 + r + 1` is impossible.

Notation: `mirabolic r` is the source's `P_(r+1)` (the Library has no `P_0`). `T` is
the topological data of the `p`-adic field `F`, `ψ` a unitary additive character, and
every representation is a `SmoothRep.{0, uF, uV} ℂ _`. The field universe `uF` and the
carrier universe `uV` stay independent, and the output carrier universe is
`max uF uV`.

## Main result

`leftMixedProductZeroRankIso T ψ r i hi`, for `r i : ℕ` and
`hi : 0 < i ∧ i ≤ r + 1`, is a natural isomorphism of functors on
`SmoothRep ℂ (GeneralLinear 0 F) × SmoothRep ℂ (mirabolic r F)`:

```
T.leftMixedProductFunctor 0 r ⋙
    mirabolicDerivativeOfOrder T ψ (0 + r) i ⟨hi.1, _⟩ ⋙
      generalLinearRankCast T (0 + r + 1 - i = 0 + (r + 1 - i))
  ≅ (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ r i hi) ⋙
      T.binaryNormalizedProductFunctor 0 (r + 1 - i)
```

(Lean lines 297–318). This type is exactly the `k = 0` instance of the isomorphism in
`LeftMixedProductDerivativeIso F T` (`MixedProductDerivativeStatement.lean`, lines
42–51): the same published left mixed product, order-`i` mirabolic derivative,
`GL` rank cast and binary normalized product, at the same universes. A private
development file checked this: for `h : LeftMixedProductDerivativeIso F T`,
`h ψ 0 r i hi = ⟨leftMixedProductZeroRankIso T ψ r i hi⟩` holds by `rfl`. That check
is not part of this candidate. Every order `1 ≤ i ≤ r + 1` is covered, including
`i = 1`, the top order `i = r + 1` (where the derivative lives on `GL_0`), and `r = 0`.

In words: for every `A` on `GL_0` and `B` on `P_(r+1)`, the order-`i` derivative of
`A × B`, after the rank cast `GL_(0+r+1-i) = GL_(0+(r+1-i))`, is naturally
`A × B^{(i)}`, in both variables at once.

## Construction

The isomorphism is a composite of five steps.

### 1. `A × B` as a tensor product (Lean lines 31–110)

For `k = 0`, the inducing subgroup `leftSubgroup 0 r` is the whole group
`P_(0+r+1)` (`mem_leftSubgroup_zero`), and the inducing character is trivial
(`leftCharacter_zero_left`). Also, `GL_0` has a single element, so
`leftProjection` sends every `g` to `(1, leftUnitProjection r g)`, and `A` is acted on
trivially. The carrier of `A` is still an arbitrary vector space.

- `leftZeroInput T r` is the functor
  `(A, B) ↦ (B ∘ leftUnitProjection r, ULift.{uF} A)`: a swap of factors, followed by
  the pullback `MixedProductTensor.pullbackFunctor (leftUnitProjection r)` on `B` and
  `MixedProductTensor.liftFunctor` on `A`.
- `leftZeroModel T r` is `leftZeroInput T r` followed by Worker 969's
  `ZeroRankTensor.tensorFunctor` on `P_(0+r+1)` and `GL_0`. On objects it is
  `(B ∘ leftUnitProjection r) ⊗ ULift A`, with `P_(0+r+1)` acting on the first factor
  only.
- `swapLift A B : A ⊗ B ≃ B ⊗ ULift A` sends `a ⊗ b` to `b ⊗ ULift.up a`.
- `leftZeroEquiv T r X` is the equivariant linear equivalence obtained by composing
  three maps:
  - `Induction.compactInducedTopEquiv`, which evaluates a function at `1` (the
    subgroup is the whole group);
  - `MixedProductTensor.compEquiv` of `twistOneEquiv` (twisting by the trivial
    character);
  - `swapLift`.

  The intertwining condition reduces to the fact that the `GL_0` component of
  `leftProjection` is `1`, which holds because a `0 × 0` matrix has no entries.
  `leftZeroEquiv_apply` records the component formula:
  `f ↦ swapLift (T.leftMixedEval X f 1)`.
- `leftZeroIso T r : T.leftMixedProductFunctor 0 r ≅ leftZeroModel T r` collects
  these components. Naturality in `(A, B)` is checked on pure tensors of
  `f(1) ∈ A ⊗ B`.

This step generalizes the Library pattern `leftMixedProductUnitEquiv` /
`leftMixedProductUnitIso` (`Mirabolic/MixedProducts`) from the unit to an
arbitrary `A`.

### 2. The binary product with a `GL_0` factor as a tensor product (Lean lines 114–168)

- `rightZeroInput T m` is `(A, Y) ↦ (Y ∘ reindex (finCongr (0 + m = m)), ULift A)`.
- `rightZeroModel T m` is `rightZeroInput T m` followed by `tensorFunctor` on
  `GL_(0+m)` and `GL_0`.
- `rightZeroEquiv T m X` composes the published `T.binaryLeftZeroTensorEquiv rfl X`
  (`Induction/BinaryProduct`) with `swapLift`. The published equivalence identifies
  `T.binaryNormalizedProductFunctor 0 m` (which is
  `binaryLeftZeroTensorFunctor rfl`) with `rankZeroLeft`: `A ⊗ Y`, where `GL_(0+m)`
  acts on `Y` through `reindex (finCongr (0 + m = m))`.
- `rightZeroIso T m : T.binaryNormalizedProductFunctor 0 m ≅ rightZeroModel T m`.
  Naturality comes from the published `binaryLeftZeroTensorEquiv_naturality`,
  followed by the swap.

### 3. Rank casts (Lean lines 172–245)

- `prodCompProdIso` and `prodCompSwapIso` are identity isomorphisms between
  products of functors composed with products or with `Prod.swap`. They are stated
  for abstract functors so that the later steps never unfold the rank-cast
  transports.
- `pullbackIdIso φ hφ h` says that pulling back along a homomorphism `φ` with
  `φ g = g` for all `g` is the identity functor. Its components are identity maps.
- `generalLinearRankCastPullbackIso T h` says that the published `generalLinearRankCast T h`
  (the `Eq.rec` transport along `h : a = b`) is isomorphic to the pullback along the
  entry-preserving `reindex (finCongr h.symm)`. It is proved by `subst h` and
  `pullbackIdIso`.
- `leftUnitProjection_entry` says that `leftUnitProjection r` reads the matrix
  entries of `g ∈ P_(0+r+1)` at the indices `Fin.cast (r + 1 = 0 + r + 1)`. It
  rewrites the Library `leftUnitProjection_apply`, with
  `leftIndex 0 r (Sum.inr c) = Fin.cast _ c`.
- `pullbackDerivativeCastIso T ψ hN φ hφc hφ i hi hi' h₁` handles a homomorphism
  `φ : mirabolic N → mirabolic r` that reads entries at the cast indices, where
  `hN : N = r`. It gives

  ```
  pullback φ ⋙ mirabolicDerivativeOfOrder T ψ N i _ ⋙ generalLinearRankCast T h₁
    ≅ mirabolicDerivativeOfOrder T ψ r i hi ⋙ pullback (reindex (finCongr (0 + (r+1-i) = r+1-i)))
  ```

  with `h₁ : N + 1 - i = 0 + (r + 1 - i)`. After `subst hN`, `φ` is pointwise the
  identity, so its pullback is removed by `pullbackIdIso`. The rank cast is then
  replaced by a reindex pullback using `generalLinearRankCastPullbackIso`.

### 4. The derivative commutes with the inert factor (Lean lines 249–295)

- `tensorDerivativeCastIso T ψ r i hi` pastes Worker 969's
  `mirabolicDerivativeOfOrderTensorIso` (the order-`i` mirabolic derivative commutes
  with `tensorFunctor`) and `generalLinearRankCastTensorIso` (so does the `GL` rank
  cast) with `ZeroRankTensor.prodCommIsoComp`. The result is that the cast
  order-`i` derivative of `X ⊗ ULift A` is naturally (cast derivative of `X`)
  `⊗ ULift A`.
- `inputDerivativeIso T ψ r i hi` identifies the two input functors:
  `leftZeroInput T r` followed by (cast order-`i` derivative) `× 𝟭`, and
  `𝟭 × mirabolicDerivativeOfOrder T ψ r i hi` followed by
  `rightZeroInput T (r + 1 - i)`. On the `B` component it is
  `pullbackDerivativeCastIso` with `φ = leftUnitProjection r`, `hN = Nat.zero_add r`
  and `hφ = leftUnitProjection_entry r`. On the `A` component it is the identity.
  The two components are combined with `NatIso.prod`, and the swap is moved across
  with `prodCompSwapIso`.

### 5. Assembly (Lean lines 297–318)

`leftMixedProductZeroRankIso` is the composite

```
A × B  ──leftZeroIso──▶  (B ∘ π) ⊗ ULift A
       ──tensorDerivativeCastIso──▶  D(B ∘ π) ⊗ ULift A
       ──inputDerivativeIso──▶  (D(B) ∘ reindex) ⊗ ULift A
       ──rightZeroIso⁻¹──▶  A × D(B)   (binary product on GL_0 × GL_(r+1-i))
```

Here `π = leftUnitProjection r` and `D` is the cast order-`i` derivative. The steps
are joined by functor associators and whiskering. On a vector `f` of `A × B`, the
first step is `f ↦ swapLift (f(1))`. The middle steps are the canonical maps
`[v ⊗ a] ↦ [v] ⊗ a` of `ZeroRankTensor`, which come from the localization, pullback
and twist commutations, together with identity maps from the rank-cast
substitutions. The last step is the inverse of
`swapLift ∘ binaryLeftZeroTensorEquiv rfl`.

## Provenance

BZ77 (`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`) states Corollary
4.14(a) on printed p.458 (PDF p.19), for the mixed products of §4.12(II), printed
p.457 (PDF p.18), and derives it from Proposition 4.13(b). The source does not treat
the `GL_0` factor separately. With its convention `P_0 = 0`, the case `k = 0` is
degenerate there. The construction here is an internal argument and does not
reproduce a source passage. The only literature input is the commutation of the
localization functors `r_{U,θ}` with tensoring by a representation of another group,
BZ77 Proposition 1.9(g) (printed p.445, PDF p.6). Worker 969's `ZeroRankTensor` module
proves this commutation in Lean. Everything else is a canonical identification
(evaluation at `1`, the trivial twist, the swap `a ⊗ b ↦ b ⊗ ULift.up a`, and identity
maps after substituting rank equalities). This construction uses no part of
Proposition 4.13(b) and no proof of
`Langlands.Derivative.MirabolicProductMinusCompatibilityStatement`. Following the
task's suggested route (step 4), it replaces the coinvariant computation by the
tensor-commutation isomorphisms of `ZeroRankTensor`.

## Dependencies and independence audit

Direct imports:

- `Langlands.Representation.Derivative.ZeroRankTensor` (Worker 969, published in
  the Library), from which this module uses `tensorFunctor`, `prodCommIsoComp`,
  `mirabolicDerivativeOfOrderTensorIso` and `generalLinearRankCastTensorIso`;
- `Langlands.Group.GL.RankReindex`, from which this module uses
  `continuous_reindex_finCongr`.

Other published declarations used are `T.leftMixedProductFunctor`,
`T.leftMixedEval`, `leftSubgroup`, `mem_leftSubgroup_zero`, `leftProjection`,
`leftUnitProjection`, `leftUnitProjection_apply`, `continuous_leftUnitProjection`,
`leftIndex`, `T.leftCharacter`, `leftCharacter_zero_left`,
`isSmooth_leftInducingRepresentation`, `Induction.compactInducedTopEquiv`,
`MixedProductTensor.{compEquiv, twistOneEquiv, pullbackFunctor, liftFunctor,
liftMap, smoothRep_hom_ext}` (`Mirabolic/MixedProducts`),
`T.binaryNormalizedProductFunctor`, `T.binaryLeftZeroTensorEquiv` and
`binaryLeftZeroTensorEquiv_naturality` (`Induction/BinaryProduct`),
`mirabolicDerivativeOfOrder` (`Derivative/Homogeneity`) and `generalLinearRankCast`.

The complete project import closure has 75 modules: this module and the 74-module
closure of `ZeroRankTensor` (including `ZeroRankTensor` itself), which already
contains `Group.GL.RankReindex`. The closure lies in
`Group.GL.*`, `LocalField.*`, `HarmonicAnalysis.Basic`,
`Topology.{CompactNormCharacter, Nonarchimedean.Subgroup}` and the representation
layers `Category`, `Smooth`, `Twist`, `Tensor.{Finite, OneFactor}`,
`MatrixCoefficient`, `Jacquet.{Coinvariants, Localization, PositiveCharacter,
SmoothTwist}`, `Induction.{Definitions, Parabolic, BlockFactors, BinaryProduct}`,
`Mirabolic.MixedProducts`, `Dual.Definitions`, `Whittaker.{Algebraic, GeneralLinear}`
and `Derivative.{MirabolicCharacter, MirabolicMinus, Iteration, Homogeneity}`. The
closure was checked against both exclusion sets of the task context, condition by
condition:

- It contains no module and no declaration for any of the following: segment
  derivatives, segment existence or classification, Jacquet formulas, socle or head
  existence, the special-head criterion, multisegment, square-integrable or regular
  exhaustion, tempered uniqueness, `GenericSegmentProductUniqueness`, the
  two-supercuspidal statements, or Leibniz filtrations.
- It contains no homogeneity theorem of Ze80 5.3 or Ze80 6.2.
  `Derivative.Homogeneity` only contains definitions and elementary lemmas: the rank
  cast `mirabolicRankCast`, `mirabolicDerivativeOfOrder`, the level, the predicates
  `IsHomogeneous` and `IsGeneralLinearHomogeneous`, and carrier-vanishing lemmas.
  This module uses only `mirabolicDerivativeOfOrder` from it.
- It contains no minus exactness (task `b65bc667`).
- It contains no `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`.
  The two Whittaker modules supply lower character and coefficient constructions
  only.
- It does not use the consumers `RestrictedProductLevel`,
  `SegmentSocleProductHomogeneityInduction` or `SegmentSocleProductCaseTwo`.

The review of `ZeroRankTensor` (Reviewer 6107) audited the same closure, which it
counted as 73 modules besides `ZeroRankTensor` itself, with the same result. No hypothesis, proposition-valued premise or theorem-valued input is
introduced. The construction is data (natural isomorphisms) and uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
