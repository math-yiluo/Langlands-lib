# The right mixed-product derivative filtration with a `GL_0` factor

Author: Worker 969.

This module proves the `k = 0` case of BZ77 Corollary 4.14(b) in the form of the
published statement
`Langlands.Derivative.RightMixedProductDerivativeFiltrationStatement`: the case in
which the general linear factor `A` is a representation of `GL_0`.

Notation. As in BZ77 §3.1 (printed p.450), `P_m` is the mirabolic subgroup of
`GL_m`. The Library group `mirabolic n` is the mirabolic subgroup of `GL_(n+1)`,
so `mirabolic n = P_(n+1)`. Below, groups are written with their Lean index
followed by their BZ77 name.

The theorem `Langlands.Derivative.rightMixedProductDerivativeFiltration_zero`
states, for topological data `T`, a unitary additive character `ψ`, `r d : ℕ` and
`hd : 0 < d ∧ d ≤ (0 + r) + 1`:

```
∃ e : Fin (rightMixedDerivativeIndices 0 r d).card ≃ RightMixedDerivativeIndex 0 r d,
  IsGluedFrom (rightMixedDerivativeSource T ψ 0 r d hd)
    (fun i => rightMixedDerivativePiece T ψ 0 r d (e i))
```

This is exactly the body of the published statement at `k = 0`, for every `ψ`, `r`,
`d` and `hd`. Here `rightMixedDerivativeSource T ψ 0 r d hd` is the published
order-`d` derivative of the right mixed product `B × A` (a representation of
`mirabolic (0 + r) = P_(r+1)`), viewed in `Rep`, and the pieces are the published
grades `B^(j) × A^(t)` for the feasible pairs `(j, t)`. The module adds no
hypotheses. It proves no other case of the statement.

## Mathematical content

Let `B` be a smooth representation of `mirabolic r = P_(r+1)` and `A` one of `GL_0`.
For `k = 0` the inducing subgroup of `B × A` is the whole group
`mirabolic (0 + r)`, the character `χ_R` is trivial, and `GL_0` is trivial. So
evaluation at `1` identifies `B × A` with `B ⊗ A`, on which `mirabolic (0 + r)` acts
on `B` through `rightUnitProjection r`, which is the rank cast
`mirabolic (0 + r) = mirabolic r`. The derivative of `B ⊗ A` is `B^(d) ⊗ A`, because
derivatives commute with tensoring by a factor on which the group acts trivially
(module `Langlands.Representation.Derivative.ZeroRankTensor`). On the other side, the only
feasible pair is `(d, 0)` (published `rightMixedDerivativeIndices_zero_gl`), and its
grade `B^(d) × A^(0)` is `B^(d) ⊗ A` too, by `ZeroRankTensor.binaryRightZeroIso`
and `A^(0) = A`. Hence the derivative is isomorphic to its
unique grade, and the one-step filtration `0 ⊆ (B × A)^(d)` glues it.

## Provenance

Derived. BZ77 (`bernstein-zelevinsky-1977-induced-i`, content SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), Corollary
4.14(b) (printed p.458, PDF p.19) states that `(τ × ρ)^(i)` is glued from
`τ^(j) × ρ^(i-j)` for `j = 1, …, i`, and derives it from 4.14(a) and 4.13(c) on the
same page. The source does not treat the case where `ρ` is a representation of
`GL_0` separately. The argument here is internal to the formalization: it is the
direct identification above, and it does not follow the source's route through
4.13(c). The commutation of localization with a tensor factor that it uses is BZ77
Proposition 1.9(g) (printed p.445, PDF p.6), formalized in the `ZeroRankTensor`
module.

## Declarations

Unless stated otherwise, declarations are in namespace
`Langlands.Derivative.RightMixedZeroRank`.

### One-step filtrations

These are generic, for functors `M : C ⥤ Rep R G`.

- `botSubfunctor M` and `topSubfunctor M`: the subfunctors `0` and `M` of `M`.
- `oneStepFiltration M : RepFunctorFiltration M 1`: the filtration `0 ⊆ M`, with
  step `0` equal to `botSubfunctor M` and step `1` equal to `topSubfunctor M`.
- `oneStepGradedIso M`: its only graded piece `M / 0` is isomorphic to `M`. This is
  the published `RepSubfunctor.quotientNatIsoOfSurjective` applied to the
  inclusion of the top subfunctor, whose kernel is `0` and which is surjective.
- `isGluedFrom_of_iso hn a`: if `hn : n = 1` and `M` is isomorphic to `pieces i`
  for every `i : Fin n` (given as `Nonempty` isomorphisms), then
  `IsGluedFrom M pieces`. The permutation is the identity and the filtration is
  `oneStepFiltration M`.

### The rank cast

- `castHom h : mirabolic b R →* mirabolic a R` for `h : a = b`: the identity
  `P_(b+1) → P_(a+1)` after `subst h`. `castHom_apply` gives its matrix entries
  (`Fin.cast` of the indices), and `continuous_castHom` gives continuity.
- `rightIndex_zero_inl_val r i`: the published block index `rightIndex 0 r` sends
  `Sum.inl i` to an index with the same value.
- `rightUnitProjection_eq_castHom r`: the published `rightUnitProjection r`, the
  mirabolic block of the case (III) projection for `k = 0`, equals
  `castHom (Nat.zero_add r).symm : mirabolic (0 + r) → mirabolic r`. It is checked
  entrywise.
- `pullbackCastIso T h φ hφ heq`: if `φ = castHom h`, restriction along `φ` is
  isomorphic to the published smooth rank transport `mirabolicRankCast T h`
  (identity components after `subst`).
- `rankCastDerivativeIso T ψ h d ha hb h'`: the order-`d` mirabolic derivative
  commutes with the rank casts:
  `mirabolicRankCast T h ⋙ mirabolicDerivativeOfOrder T ψ b d hb ≅
  mirabolicDerivativeOfOrder T ψ a d ha ⋙ generalLinearRankCast T h'`. After
  `subst h` both casts are identities, and the iso is made of unitors.

### The product `B × A` with `A` on `GL_0`

- `rightMixedProductZeroEquiv T r (B, A)`: for `B` on `mirabolic r` and `A` on
  `GL_0`, an equivalence of representations of `mirabolic (0 + r)` between
  `(T.rightMixedProductFunctor 0 r).obj (B, A)` and
  `tensorObj (φ^* B, ULift A)`. Here `φ^* B` is the restriction of `B` along
  `rightUnitProjection r`, and `ULift A` is `MixedProductTensor.liftFunctor`,
  which moves the carrier of `A` to universe `max uV uF`. The equivalence is the
  composite of the published `Induction.compactInducedTopEquiv` (evaluation at
  `1`, since `rightSubgroup 0 r` is the whole group, `mem_rightSubgroup_zero`),
  the published removal of the trivial twist `MixedProductTensor.twistOneEquiv`
  (by `rightCharacter_zero_left`), and `id ⊗ ULift.up`. Equivariance of the last
  step uses that `GL_0` acts trivially (published
  `representation_apply_of_rank_eq_zero`).
- `rightMixedProductZeroIso T r`: the natural isomorphism
  `T.rightMixedProductFunctor 0 r ≅ (φ^*.prod liftFunctor) ⋙ tensorFunctor (mirabolic (0 + r)) (GL_0)`
  with these components. Naturality is checked on the value at `1`
  (`rightMixedEval`), where both sides are `f ⊗ g` on pure tensors.

### Pasting

Two generic pasting constructions for natural isomorphisms of functors on product
categories. They contain only associators, whiskerings, `NatIso.prod` and unitors.

- `sourcePaste α β γ`: from `α : S ≅ P.prod Q ⋙ T₁`,
  `β : T₁ ⋙ M ≅ L.prod 𝟭 ⋙ T₂` and `γ : P ⋙ L ≅ L₂`, the iso
  `S ⋙ M ≅ L₂.prod Q ⋙ T₂`.
- `piecePaste α β δ`: from `α : B ≅ 𝟭.prod Q ⋙ T₁`,
  `β : T₁ ⋙ M ≅ L.prod 𝟭 ⋙ T₂` and `δ : D₂ ⋙ Q ≅ Q'`, the iso
  `(D₁.prod D₂ ⋙ B) ⋙ M ≅ (D₁ ⋙ L).prod Q' ⋙ T₂`.

### Source and grade

- `sourceIso T ψ r d hd hd' h'`: the derivative of `B × A`,
  `T.rightMixedProductFunctor 0 r ⋙ mirabolicDerivativeOfOrder T ψ (0 + r) d hd`, is
  isomorphic to
  `(mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h').prod liftFunctor ⋙ tensorFunctor (GL_((0+r)+1-d)) (GL_0)`,
  i.e. `(B, A) ↦ cast(B^(d)) ⊗ ULift A`. It is `sourcePaste` of
  `rightMixedProductZeroIso`, `ZeroRankTensor.mirabolicDerivativeOfOrderTensorIso`
  and `pullbackCastIso` followed by `rankCastDerivativeIso`.
- `pieceIso T ψ r d N hd' h0 h`: the grade
  `((mirabolicDerivativeOfOrder T ψ r d hd').prod (generalLinearDerivative T ψ 0 0 h0) ⋙ T.binaryNormalizedProductFunctor (r + 1 - d) 0) ⋙ generalLinearRankCast T h`
  is isomorphic to
  `(mirabolicDerivativeOfOrder T ψ r d hd' ⋙ generalLinearRankCast T h).prod liftFunctor ⋙ tensorFunctor (GL_N) (GL_0)`.
  It is `piecePaste` of `ZeroRankTensor.binaryRightZeroIso`,
  `ZeroRankTensor.generalLinearRankCastTensorIso`, and the left unitor, since the published
  zeroth derivative `generalLinearDerivative T ψ 0 0 h0` is the identity functor
  by definition.
- `nonempty_sourceIso_piece T ψ r d hd x`: for every feasible index `x`,
  `rightMixedDerivativeSource T ψ 0 r d hd ≅ rightMixedDerivativePiece T ψ 0 r d x`.
  The proof shows `x = (d, 0)` from the membership condition, then composes
  `sourceIso`, the inverse of `pieceIso` (both whiskered by `SmoothRep.toRep`) and
  associators.

### The theorem

- `Langlands.Derivative.rightMixedProductDerivativeFiltration_zero T ψ r d hd`: the
  statement displayed above. The enumeration `e` is the inverse of
  `Finset.equivFin`. The index set is the singleton `{(d, 0)}`
  (`rightMixedDerivativeIndices_zero_gl`), so its cardinality is `1`, and
  `isGluedFrom_of_iso` applies with `nonempty_sourceIso_piece`.

## Imports

`Langlands.Representation.Derivative.ZeroRankTensor` (tensor commutation and the
binary product with a `GL_0` factor),
`Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`
(the statement's source, pieces and index set), and
`Langlands.Representation.Filtration.QuotientFirstIso`
(`quotientNatIsoOfSurjective`). No proposition from them is used as a hypothesis.
