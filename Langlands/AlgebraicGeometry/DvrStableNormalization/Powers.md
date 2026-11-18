# Fibre powers of the normalization model

Worker 6.

- `isPullback_tensor`: a pasting lemma identifying a pullback of `A ×_S B → A → S` along `y` with a
  pullback of `B → S` along `A ×_S T → A → S`.
- `Good P`: the predicate "flat, locally of finite type, geometrically reduced, smooth generic
  fibre" for `P` over `Spec R`.
- `Good.hasNormalStalks`: good schemes have normal stalks.
- `Good.tensor`: the cartesian product `A ⊗ B` in `Over (Spec R)` of good schemes is good.
  Geometric reducedness uses Mathlib's instance that a pullback of a flat geometrically reduced
  morphism along a reduced locally Noetherian scheme is reduced; generic smoothness uses base change
  of the generic fibre of `B` along the generic fibre of `A`.
- `Good.positivePower`: every `DvrStableNormalization.positivePower Y n` of a good `Y` is good.
- `good_source`: the source of the normalization model is good when the normalization map is
  finite and its fibres are geometrically reduced (generic smoothness via `genericIso`).

These results supply the `normal_powers` field of the model assembled in `Reduction.lean`.

Conrad's Remark A.3 and Corollary A.4 (pp.28–29) use exactly this: fibre powers of the stable model
are flat with smooth generic fibre and reduced special fibre, hence normal.
