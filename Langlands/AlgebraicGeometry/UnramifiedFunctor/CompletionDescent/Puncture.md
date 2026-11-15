# Comparison over an open subset of the base

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Puncture`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). Its definitions are internal to that proof and
are not meant to match a literature definition. The final proof uses it with
`π = completionMap R : Spec R̂ ⟶ Spec R` and with `U` the punctured spectrum of `R`.

Setting: `π : S' ⟶ S`, `U : S.Opens`, a presheaf `F` on `Over S`, and
`e' : (baseChange π F).RepresentableBy (Over.mk q')` for `q' : X' ⟶ S'`. Also
`eU : (baseChange U.ι F).RepresentableBy (Over.mk qU)` for `qU : X_U ⟶ U`. The
element `pt` is defined in `Points.md`.

## Definitions

- `puncSource π U q'`: the part `P' := X' ×_{S'} π⁻¹(U)` of `X'` over
  `U' := π⁻¹(U)`, i.e. `pullback q' (π ⁻¹ᵁ U).ι`.
- `puncι π U q' : P' ⟶ X'`: the first projection, an open immersion.
- `puncBase π U q' : P' ⟶ U`: the composite `P' ⟶ U' ⟶ U`, built from the
  restriction `π ∣_ U`. `puncBase_ι` says that `puncBase ≫ U.ι = puncι ≫ q' ≫ π`.
- `puncMap π U e' eU : P' ⟶ X_U`: the `U`-morphism classifying the element
  `pt e' _ (puncι) _` of `F(P' ⟶ S)` under `eU`. `puncMap_comp` says that
  `puncMap ≫ qU = puncBase`.
- `puncComparison : P' ⟶ X_U ×_U U'`: the morphism `(puncMap, pullback.snd)`.
- `puncTarget π U qU : Over S`: the scheme `X_U ×_U U'` over `S`. `pullback_fst_comp`
  records its structure morphism through the first factor.

## Results

- `pt_puncMap`: for `T : Over S` and `a : T.left ⟶ P'`, the elements
  `pt eU T (a ≫ puncMap)` and `pt e' T (a ≫ puncι)` of `F(T)` agree. Proof: by
  `homEquiv_eq_pt`, the defining property of `puncMap` is this identity for
  `a = 𝟙`. The general case follows by applying `F.map` along `a` and using
  `pt_comp` on both sides.
- `puncMap_eq_of_pt_eq`: if `a, b : T.left ⟶ P'` lie over `T.hom` and
  `pt e' T (a ≫ puncι) = pt e' T (b ≫ puncι)`, then `a ≫ puncMap = b ≫ puncMap`.
  Proof: both composites have the same image in `U` (`puncMap_comp`, `puncBase_ι`,
  and `U.ι` is a monomorphism) and the same element of `F` by `pt_puncMap`. So
  `pt_inj` for `eU` applies.
- `exists_puncInv`: by `exists_pt` for `e'`, there is `a : X_U ×_U U' ⟶ X'` over
  `snd ≫ (π⁻¹ᵁ U).ι` with `pt e' a = pt eU fst`.
- `isIso_puncComparison`: `P'` is the base change of `X_U` along `U' ⟶ U`. The
  inverse is `ψ := pullback.lift a snd`. Both composites are checked on the two
  pullback projections. The `X'`-component of `puncComparison ≫ ψ`, and the
  `X_U`-component of `ψ ≫ puncComparison`, are identified by `pt_inj` (for `e'`,
  respectively `eU`). The element equalities come from `pt_comp`, `pt_puncMap` and
  the defining property of `a`. The remaining components are pullback identities.
- `isAffineHom_puncMap`: if `π` is affine, so is `puncMap`. Proof: `π ∣_ U` is affine
  (`IsZariskiLocalAtTarget.restrict`), so is its base change
  `pullback.fst : X_U ×_U U' ⟶ X_U`, and `puncMap` is the isomorphism
  `puncComparison` followed by this projection. This proof sets the option
  `backward.isDefEq.respectTransparency.types false`, which the restriction lemma
  needs to elaborate.
