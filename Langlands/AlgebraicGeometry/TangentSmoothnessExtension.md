# Dense range from tangent surjectivity at a point with values in a field extension

Author: Worker 1630.

This derived helper module extends the published tangent-space dominance
criterion `TangentSmoothness.denseRange_of_isTangentSurjectiveAt` from
rational points to points with values in a field extension. The tangent
vectors may then be taken over the extension. The project's route to
unirationality of the scheme of maximal tori (SGA 3, Exposé XIV) uses this
to prove dominance of an adjoint slice map. There the tangent computation
needs a regular element of a split torus, which exists only after extending
the base field. The argument is the standard reduction by base change. It
is written out here from Mathlib's scheme pullbacks and the published
criterion. No external theorem is asserted.

All declarations live in the namespace
`Langlands.AlgebraicGeometry.TangentSmoothness`. Throughout, `K` is a field
extension of a field `k`, both in universe `u`. `X` and `Y` are schemes with
morphisms `p : X ⟶ Spec k` and `q : Y ⟶ Spec k`. `dualNumberAugmentation K`
and `dualNumberProjection K` are the Library morphisms
`Spec K ⟶ Spec K[ε]` (for `ε ↦ 0`) and `Spec K[ε] ⟶ Spec K` (for the
inclusion `K → K[ε]`).

- `IsTangentSurjectiveAtExtension p q f x` (definition), for `f : X ⟶ Y` and
  `x : Spec K ⟶ X`. Let `t : Spec K[ε] ⟶ Y` be any morphism with
  `t ≫ q` equal to the structure morphism `Spec K[ε] ⟶ Spec k` and with
  restriction `dualNumberAugmentation K ≫ t = x ≫ f`. Then there is
  `s : Spec K[ε] ⟶ X` with `s ≫ p` the structure morphism,
  `dualNumberAugmentation K ≫ s = x` and `s ≫ f = t`. When `K = k`, this
  is the published `IsTangentSurjectiveAt` for a rational point `x`. The
  definition imposes no other condition on `f` or `x`.
- `specMap_algebraMap_dualNumber`: the structure morphism
  `Spec K[ε] ⟶ Spec k` is `dualNumberProjection K` followed by
  `Spec K ⟶ Spec k`.
- `surjective_specMap_algebraMap`: `Spec K ⟶ Spec k` is surjective, since
  `Spec k` has exactly one point.
- `denseRange_of_isTangentSurjectiveAtExtension`: assume `p` is smooth, `q`
  is locally of finite type and geometrically irreducible, `f ≫ q = p`, and
  `x ≫ p` is the structure morphism `Spec K ⟶ Spec k`. If
  `IsTangentSurjectiveAtExtension p q f x`, then `f` has dense range.

  Proof. Base change everything along `b : Spec K ⟶ Spec k`. Let
  `f_K : X_K ⟶ Y_K` be the induced map of pullbacks. `x` and the identity
  of `Spec K` give a rational point `x_K` of `X_K`. A tangent vector of
  `Y_K` at `x_K ≫ f_K` projects to a morphism `Spec K[ε] ⟶ Y` satisfying
  the hypotheses of the definition. Its lift `s` and the projection
  `Spec K[ε] ⟶ Spec K` define a tangent vector of `X_K` at `x_K`. This
  vector maps to the given one, so `f_K` is tangent-surjective at `x_K`.
  Smoothness of `p`, finite type of `q`, and irreducibility of `Y_K` (from
  geometric irreducibility) pass to the base change. So the published
  criterion `denseRange_of_isTangentSurjectiveAt` shows that `f_K` has
  dense range. The projection `Y_K ⟶ Y` is surjective, as the base change
  of the surjection `Spec K ⟶ Spec k`. So `Y_K ⟶ Y` composed with `f_K`
  has dense range. This composite equals `X_K ⟶ X ⟶ Y`, whose range is
  contained in the range of `f`.

No hypothesis is placed on the field extension `K`, and none on `X` beyond
smoothness over `k`.
