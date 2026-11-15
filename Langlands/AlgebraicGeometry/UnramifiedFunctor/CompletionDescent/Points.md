# Points of a scheme representing a base change

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent.Points`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent`.

This is a helper module for the proof of Step 2b of Murre's induction
(`MurreCompletionDescentProof.md`). It defines only internal bookkeeping notions,
which serve the proof and are not meant to match a literature definition.

Throughout, `π : S' ⟶ S` is a morphism of schemes and `F` is a presheaf on `Over S`.
`q' : X' ⟶ S'` represents the base change `baseChange π F` (published in
`MurreProofSteps`: the presheaf `T' ↦ F(T' ⟶ S' ⟶ S)` on `Over S'`), via
`e : (baseChange π F).RepresentableBy (Over.mk q')`.

## Definitions

- `univ e : F(X' ⟶ S' ⟶ S)`, the universal element `e.homEquiv (𝟙 _)`.
- `pt e T a ha : F(T)`, for `T : Over S` and `a : T.left ⟶ X'` with
  `ha : a ≫ q' ≫ π = T.hom`: the pullback of `univ e` along the morphism
  `Over.homMk a ha : T ⟶ (X' ⟶ S)` of `Over S`.
- `prodOver q' π : Over S`, the abbreviation for `X' ×_S S'` (the pullback of
  `q' ≫ π` and `π`) with structure morphism `pullback.snd ≫ π`.

## Lemmas

- `pt_congr`: `pt` does not depend on the proof argument when the morphisms are equal.
- `map_univ`: `F.map g.op (univ e) = pt e T g.left _` for every
  `g : T ⟶ (X' ⟶ S)`.
- `pt_comp`: naturality. `F.map f.op (pt e T₂ a _) = pt e T₁ (f.left ≫ a) _` for
  `f : T₁ ⟶ T₂` in `Over S`. Proof: functoriality of `F`.
- `homEquiv_eq_pt`: for `h : T' ⟶ Over.mk q'` in `Over S'`, the element
  `e.homEquiv h` is `pt e (T' ⟶ S' ⟶ S) h.left _`. Proof: `e.homEquiv_comp`
  applied to `h ≫ 𝟙`, then `map_univ`.
- `pt_inj`: if `a, b : T.left ⟶ X'` satisfy `a ≫ q' = b ≫ q'` and
  `pt e T a _ = pt e T b _`, then `a = b`. Proof: let `T' := (T.left, a ≫ q')` in
  `Over S'`. Both `a` and `b` are morphisms `T' ⟶ Over.mk q'`. By `homEquiv_eq_pt`
  and `pt_comp` along the identity of `T.left`, their images under the bijection
  `e.homEquiv` are the two given equal elements, so they are equal.
- `exists_pt`: for `c : T.left ⟶ S'` with `c ≫ π = T.hom` and `v ∈ F(T)`, there is
  `a : T.left ⟶ X'` with `a ≫ q' = c` and `pt e T a _ = v`. Proof: take
  `a := (e.homEquiv.symm v).left` for `T' := (T.left, c)`, which lies over `c`, and
  compare with `homEquiv_eq_pt` along the identity of `T.left`.
- `fst_comp_eq`: `fst ≫ q' ≫ π = (prodOver q' π).hom`, i.e. the pullback condition.
- `exists_sigma`: there is `σ : X' ×_S S' ⟶ X'` with `σ ≫ q' = snd` and
  `pt σ = pt fst` in `F(X' ×_S S')`. This is `exists_pt` with `c := snd` and
  `v := pt fst`. The map `σ` is the descent datum on `X'`: it sends a point
  `(x, s')` to the unique point of `X'` over `s'` with the same image in `F` as `x`.
