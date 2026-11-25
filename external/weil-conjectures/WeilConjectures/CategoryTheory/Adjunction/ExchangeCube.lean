/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

/-!
# Exchange morphisms under a change of layer

Consider two "layers" of adjunctions `Lf ⊣ Rf`, `Lf' ⊣ Rf'` and `Mf ⊣ Sf`, `Mf' ⊣ Sf'` (e.g. derived
pullback and pushforward along `f` and `f'`, with coefficients `Λ` and `Λ'`), comparisons
`θr : Gr ⋙ Lf' ≅ Lf ⋙ Hr`, `θs : Gs ⋙ Mf' ≅ Mf ⋙ Hs` of left adjoints (pullback square
comparisons), and functors `PY`, `PX`, `PY'`, `PX'` from the first to the second layer (a change
of coefficients) with isomorphisms `πf : Lf ⋙ PX ≅ PY ⋙ Mf`, `πf'`, `πg : Gr ⋙ PY' ≅ PY ⋙ Gs`,
`πg'` (the coefficient change commutes with the derived pullbacks).

If the cube of the left adjoints commutes, and the mates `Rf ⋙ PY ⟶ PX ⋙ Sf` of `πf.inv` and of
`πf'.inv` (the coefficient change for the derived pushforward) are invertible at the relevant
objects, then `PY'` of the exchange morphism of `θr` at `K` and the exchange morphism of `θs` at
`PX K` are isomorphic arrows (`CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app`).
The same holds for the restrictions of all the functors to full subcategories
(`CategoryTheory.Adjunction.nonempty_arrowIso_lift_map_exchangeRight_restrictFullyFaithful_app`).

We also record that in the square of adjunctions of `CategoryTheory.Adjunction.pullIsoOfComapIso`,
the comparison `Adjunction.pushHomOfComapIso` is the mate of the inverse of the conjugate
`Adjunction.pullIsoOfComapIso` (`CategoryTheory.Adjunction.pushHomOfComapIso_eq_mateEquiv`).
-/

@[expose] public section

namespace CategoryTheory

/-- If the images under a fully faithful functor of two morphisms are isomorphic arrows, so are
the morphisms. -/
lemma Functor.FullyFaithful.nonempty_arrowIso_of_map {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} (hF : F.FullyFaithful) {X₁ Y₁ X₂ Y₂ : C} (u : X₁ ⟶ Y₁) (v : X₂ ⟶ Y₂)
    (e : Arrow.mk (F.map u) ≅ Arrow.mk (F.map v)) : Nonempty (Arrow.mk u ≅ Arrow.mk v) :=
  ⟨Arrow.isoMk (hF.preimageIso (Arrow.leftFunc.mapIso e))
    (hF.preimageIso (Arrow.rightFunc.mapIso e)) (hF.map_injective (by
      simp))⟩

namespace Adjunction

section PushHom

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)

/-- The comparison `pushHomOfComapIso : L₁ ⋙ E₂ ⟶ E₁ ⋙ L₂` is the mate along `U₁ ⊣ L₁` and
`U₂ ⊣ L₂` of the inverse of the conjugate `pullIsoOfComapIso : U₁ ⋙ E₁ ≅ E₂ ⋙ U₂`. -/
lemma pushHomOfComapIso_eq_mateEquiv :
    pushHomOfComapIso adj₁ adj₂ e =
      (mateEquiv adjR adjS (pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv) := by
  have h := iterated_mateEquiv_conjugateEquiv adjR adjS adj₂ adj₁
    (pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv
  have he : conjugateEquiv (adjR.comp adj₁) (adj₂.comp adjS)
      (pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv = e.inv := by
    exact congrArg Iso.inv
      ((conjugateIsoEquiv (adj₂.comp adjS) (adjR.comp adj₁)).apply_symm_apply e)
  rw [he] at h
  unfold pushHomOfComapIso
  rw [← h]
  exact ((mateEquiv adj₁ adj₂).symm_apply_apply _)

end PushHom

section Cube

variable {DY DX DY' DX' EY EX EY' EX' : Type*} [Category* DY] [Category* DX] [Category* DY']
  [Category* DX'] [Category* EY] [Category* EX] [Category* EY'] [Category* EX']
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
  {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
  {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}

/-- **Exchange morphisms under a change of layer.** If the cube of 2-cells on the left adjoints
built from `θr`, `θs`, `πf`, `πf'`, `πg`, `πg'` commutes, and the comparisons
`ρf = mate(πf.inv) : Rf ⋙ PY ⟶ PX ⋙ Sf` and `ρf' = mate(πf'.inv)` are invertible at `K` and
`Hr K`, then `PY'` of the exchange morphism `Rf ⋙ Gr ⟶ Hr ⋙ Rf'` of `θr` at `K` and the exchange
morphism `Sf ⋙ Gs ⟶ Hs ⋙ Sf'` of `θs` at `PX K` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_exchangeRight_app (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf)
    (bf' : Mf' ⊣ Sf') (θr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (θs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (πf : Lf ⋙ PX ≅ PY ⋙ Mf) (πf' : Lf' ⋙ PX' ≅ PY' ⋙ Mf') (πg : Gr ⋙ PY' ≅ PY ⋙ Gs)
    (πg' : Hr ⋙ PX' ≅ PX ⋙ Hs)
    (h : ∀ M, Mf'.map (πg.inv.app M) ≫ πf'.inv.app (Gr.obj M) ≫ PX'.map (θr.hom.app M) =
      θs.hom.app (PY.obj M) ≫ Hs.map (πf.inv.app M) ≫ πg'.inv.app (Lf.obj M))
    (ρf : Rf ⋙ PY ⟶ PX ⋙ Sf) (hρf : ρf = (mateEquiv af bf πf.inv))
    (ρf' : Rf' ⋙ PY' ⟶ PX' ⋙ Sf') (hρf' : ρf' = (mateEquiv af' bf' πf'.inv))
    (K : DX) (h₁ : IsIso (ρf.app K)) (h₂ : IsIso (ρf'.app (Hr.obj K))) :
    Nonempty (Arrow.mk (PY'.map ((exchangeRight af af' θr).app K)) ≅
      Arrow.mk ((exchangeRight bf bf' θs).app (PX.obj K))) := by
  have hc := mateEquiv_app_cube af af' bf bf' θr.hom θs.hom πf.inv πf'.inv πg.inv πg'.inv h K
  refine ⟨Arrow.isoMk (πg.app (Rf.obj K) ≪≫ Gs.mapIso (asIso (ρf.app K)))
    (asIso (ρf'.app (Hr.obj K)) ≪≫ Sf'.mapIso (πg'.app K)) ?_⟩
  have hr : (mateEquiv af af' θr.hom).app K = (exchangeRight af af' θr).app K := by
    rw [exchangeRight_eq_mateEquiv]
  have hs : (mateEquiv bf bf' θs.hom).app (PX.obj K) =
      (exchangeRight bf bf' θs).app (PX.obj K) := by
    rw [exchangeRight_eq_mateEquiv]
  rw [hr, hs] at hc
  subst hρf hρf'
  dsimp only [Arrow.mk_hom, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← cancel_epi (πg.inv.app (Rf.obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at hc ⊢
  erw [reassoc_of% hc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.map_id,
    Category.comp_id]

/-- **Exchange morphisms under a change of layer, on full subcategories.** The situation of
`nonempty_arrowIso_map_exchangeRight_app`, where all the functors preserve given full
subcategories, and `θr'`, `θs'` are comparisons of the restricted functors which are `θr`, `θs` on
the underlying objects: then the image of the exchange morphism of `θr'` at `K` under the
restriction of `PY'` and the exchange morphism of `θs'` at the image of `K` under the restriction
of `PX` are isomorphic arrows. -/
theorem nonempty_arrowIso_lift_map_exchangeRight_restrictFullyFaithful_app
    {QY : ObjectProperty DY} {QX : ObjectProperty DX} {QY' : ObjectProperty DY'}
    {QX' : ObjectProperty DX'} {RY : ObjectProperty EY} {RX : ObjectProperty EX}
    {RY' : ObjectProperty EY'} {RX' : ObjectProperty EX'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf)
    (bf' : Mf' ⊣ Sf') (θr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (θs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (πf : Lf ⋙ PX ≅ PY ⋙ Mf) (πf' : Lf' ⋙ PX' ≅ PY' ⋙ Mf') (πg : Gr ⋙ PY' ≅ PY ⋙ Gs)
    (πg' : Hr ⋙ PX' ≅ PX ⋙ Hs)
    (h : ∀ M, Mf'.map (πg.inv.app M) ≫ πf'.inv.app (Gr.obj M) ≫ PX'.map (θr.hom.app M) =
      θs.hom.app (PY.obj M) ≫ Hs.map (πf.inv.app M) ≫ πg'.inv.app (Lf.obj M))
    (ρf : Rf ⋙ PY ⟶ PX ⋙ Sf) (hρf : ρf = (mateEquiv af bf πf.inv))
    (ρf' : Rf' ⋙ PY' ⟶ PX' ⋙ Sf') (hρf' : ρf' = (mateEquiv af' bf' πf'.inv))
    (hLf : ∀ K : QY.FullSubcategory, QX ((QY.ι ⋙ Lf).obj K))
    (hRf : ∀ K : QX.FullSubcategory, QY ((QX.ι ⋙ Rf).obj K))
    (hLf' : ∀ K : QY'.FullSubcategory, QX' ((QY'.ι ⋙ Lf').obj K))
    (hRf' : ∀ K : QX'.FullSubcategory, QY' ((QX'.ι ⋙ Rf').obj K))
    (hGr : ∀ K : QY.FullSubcategory, QY' ((QY.ι ⋙ Gr).obj K))
    (hHr : ∀ K : QX.FullSubcategory, QX' ((QX.ι ⋙ Hr).obj K))
    (hMf : ∀ K : RY.FullSubcategory, RX ((RY.ι ⋙ Mf).obj K))
    (hSf : ∀ K : RX.FullSubcategory, RY ((RX.ι ⋙ Sf).obj K))
    (hMf' : ∀ K : RY'.FullSubcategory, RX' ((RY'.ι ⋙ Mf').obj K))
    (hSf' : ∀ K : RX'.FullSubcategory, RY' ((RX'.ι ⋙ Sf').obj K))
    (hGs : ∀ K : RY.FullSubcategory, RY' ((RY.ι ⋙ Gs).obj K))
    (hHs : ∀ K : RX.FullSubcategory, RX' ((RX.ι ⋙ Hs).obj K))
    (hPX : ∀ K : QX.FullSubcategory, RX ((QX.ι ⋙ PX).obj K))
    (hPY' : ∀ K : QY'.FullSubcategory, RY' ((QY'.ι ⋙ PY').obj K))
    (θr' : QY'.lift (QY.ι ⋙ Gr) hGr ⋙ QX'.lift (QY'.ι ⋙ Lf') hLf' ≅
      QX.lift (QY.ι ⋙ Lf) hLf ⋙ QX'.lift (QX.ι ⋙ Hr) hHr)
    (hθr : ∀ K, (θr'.hom.app K).hom = θr.hom.app K.obj)
    (θs' : RY'.lift (RY.ι ⋙ Gs) hGs ⋙ RX'.lift (RY'.ι ⋙ Mf') hMf' ≅
      RX.lift (RY.ι ⋙ Mf) hMf ⋙ RX'.lift (RX.ι ⋙ Hs) hHs)
    (hθs : ∀ K, (θs'.hom.app K).hom = θs.hom.app K.obj)
    (K : QX.FullSubcategory) (h₁ : IsIso (ρf.app K.obj)) (h₂ : IsIso (ρf'.app (Hr.obj K.obj))) :
    Nonempty (Arrow.mk ((RY'.lift (QY'.ι ⋙ PY') hPY').map ((exchangeRight
        (af.restrictFullyFaithful QY.fullyFaithfulι QX.fullyFaithfulι
          (QX.liftCompιIso (QY.ι ⋙ Lf) hLf).symm (QY.liftCompιIso (QX.ι ⋙ Rf) hRf).symm)
        (af'.restrictFullyFaithful QY'.fullyFaithfulι QX'.fullyFaithfulι
          (QX'.liftCompιIso (QY'.ι ⋙ Lf') hLf').symm (QY'.liftCompιIso (QX'.ι ⋙ Rf') hRf').symm)
        θr').app K)) ≅
      Arrow.mk ((exchangeRight
        (bf.restrictFullyFaithful RY.fullyFaithfulι RX.fullyFaithfulι
          (RX.liftCompιIso (RY.ι ⋙ Mf) hMf).symm (RY.liftCompιIso (RX.ι ⋙ Sf) hSf).symm)
        (bf'.restrictFullyFaithful RY'.fullyFaithfulι RX'.fullyFaithfulι
          (RX'.liftCompιIso (RY'.ι ⋙ Mf') hMf').symm (RY'.liftCompιIso (RX'.ι ⋙ Sf') hSf').symm)
        θs').app ((RX.lift (QX.ι ⋙ PX) hPX).obj K))) := by
  obtain ⟨e⟩ := nonempty_arrowIso_map_exchangeRight_app af af' bf bf' θr θs πf πf' πg πg' h ρf hρf
    ρf' hρf' K.obj h₁ h₂
  apply RY'.fullyFaithfulι.nonempty_arrowIso_of_map
  have e₁ := exchangeRight_restrictFullyFaithful_app_hom af af' θr hLf hRf hLf' hRf' hGr hHr θr'
    hθr K
  have e₂ := exchangeRight_restrictFullyFaithful_app_hom bf bf' θs hMf hSf hMf' hSf' hGs hHs θs'
    hθs ((RX.lift (QX.ι ⋙ PX) hPX).obj K)
  rw [ObjectProperty.ι_map, ObjectProperty.ι_map, e₂]
  change Arrow.mk (PY'.map ((exchangeRight _ _ θr').app K).hom) ≅ _
  rw [e₁]
  exact e

/-- `nonempty_arrowIso_lift_map_exchangeRight_restrictFullyFaithful_app` for transformations
`βr`, `βs` which are equal to the exchange morphisms of the restrictions. -/
theorem nonempty_arrowIso_lift_map_app_of_eq_exchangeRight_restrictFullyFaithful
    {QY : ObjectProperty DY} {QX : ObjectProperty DX} {QY' : ObjectProperty DY'}
    {QX' : ObjectProperty DX'} {RY : ObjectProperty EY} {RX : ObjectProperty EX}
    {RY' : ObjectProperty EY'} {RX' : ObjectProperty EX'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf)
    (bf' : Mf' ⊣ Sf') (θr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (θs : Gs ⋙ Mf' ≅ Mf ⋙ Hs)
    (πf : Lf ⋙ PX ≅ PY ⋙ Mf) (πf' : Lf' ⋙ PX' ≅ PY' ⋙ Mf') (πg : Gr ⋙ PY' ≅ PY ⋙ Gs)
    (πg' : Hr ⋙ PX' ≅ PX ⋙ Hs)
    (h : ∀ M, Mf'.map (πg.inv.app M) ≫ πf'.inv.app (Gr.obj M) ≫ PX'.map (θr.hom.app M) =
      θs.hom.app (PY.obj M) ≫ Hs.map (πf.inv.app M) ≫ πg'.inv.app (Lf.obj M))
    (ρf : Rf ⋙ PY ⟶ PX ⋙ Sf) (hρf : ρf = (mateEquiv af bf πf.inv))
    (ρf' : Rf' ⋙ PY' ⟶ PX' ⋙ Sf') (hρf' : ρf' = (mateEquiv af' bf' πf'.inv))
    (hLf : ∀ K : QY.FullSubcategory, QX ((QY.ι ⋙ Lf).obj K))
    (hRf : ∀ K : QX.FullSubcategory, QY ((QX.ι ⋙ Rf).obj K))
    (hLf' : ∀ K : QY'.FullSubcategory, QX' ((QY'.ι ⋙ Lf').obj K))
    (hRf' : ∀ K : QX'.FullSubcategory, QY' ((QX'.ι ⋙ Rf').obj K))
    (hGr : ∀ K : QY.FullSubcategory, QY' ((QY.ι ⋙ Gr).obj K))
    (hHr : ∀ K : QX.FullSubcategory, QX' ((QX.ι ⋙ Hr).obj K))
    (hMf : ∀ K : RY.FullSubcategory, RX ((RY.ι ⋙ Mf).obj K))
    (hSf : ∀ K : RX.FullSubcategory, RY ((RX.ι ⋙ Sf).obj K))
    (hMf' : ∀ K : RY'.FullSubcategory, RX' ((RY'.ι ⋙ Mf').obj K))
    (hSf' : ∀ K : RX'.FullSubcategory, RY' ((RX'.ι ⋙ Sf').obj K))
    (hGs : ∀ K : RY.FullSubcategory, RY' ((RY.ι ⋙ Gs).obj K))
    (hHs : ∀ K : RX.FullSubcategory, RX' ((RX.ι ⋙ Hs).obj K))
    (hPX : ∀ K : QX.FullSubcategory, RX ((QX.ι ⋙ PX).obj K))
    (hPY' : ∀ K : QY'.FullSubcategory, RY' ((QY'.ι ⋙ PY').obj K))
    (θr' : QY'.lift (QY.ι ⋙ Gr) hGr ⋙ QX'.lift (QY'.ι ⋙ Lf') hLf' ≅
      QX.lift (QY.ι ⋙ Lf) hLf ⋙ QX'.lift (QX.ι ⋙ Hr) hHr)
    (hθr : ∀ K, (θr'.hom.app K).hom = θr.hom.app K.obj)
    (θs' : RY'.lift (RY.ι ⋙ Gs) hGs ⋙ RX'.lift (RY'.ι ⋙ Mf') hMf' ≅
      RX.lift (RY.ι ⋙ Mf) hMf ⋙ RX'.lift (RX.ι ⋙ Hs) hHs)
    (hθs : ∀ K, (θs'.hom.app K).hom = θs.hom.app K.obj)
    (βr : QY.lift (QX.ι ⋙ Rf) hRf ⋙ QY'.lift (QY.ι ⋙ Gr) hGr ⟶
      QX'.lift (QX.ι ⋙ Hr) hHr ⋙ QY'.lift (QX'.ι ⋙ Rf') hRf')
    (hβr : βr = exchangeRight
        (af.restrictFullyFaithful QY.fullyFaithfulι QX.fullyFaithfulι
          (QX.liftCompιIso (QY.ι ⋙ Lf) hLf).symm (QY.liftCompιIso (QX.ι ⋙ Rf) hRf).symm)
        (af'.restrictFullyFaithful QY'.fullyFaithfulι QX'.fullyFaithfulι
          (QX'.liftCompιIso (QY'.ι ⋙ Lf') hLf').symm (QY'.liftCompιIso (QX'.ι ⋙ Rf') hRf').symm)
        θr')
    (βs : RY.lift (RX.ι ⋙ Sf) hSf ⋙ RY'.lift (RY.ι ⋙ Gs) hGs ⟶
      RX'.lift (RX.ι ⋙ Hs) hHs ⋙ RY'.lift (RX'.ι ⋙ Sf') hSf')
    (hβs : βs = exchangeRight
        (bf.restrictFullyFaithful RY.fullyFaithfulι RX.fullyFaithfulι
          (RX.liftCompιIso (RY.ι ⋙ Mf) hMf).symm (RY.liftCompιIso (RX.ι ⋙ Sf) hSf).symm)
        (bf'.restrictFullyFaithful RY'.fullyFaithfulι RX'.fullyFaithfulι
          (RX'.liftCompιIso (RY'.ι ⋙ Mf') hMf').symm (RY'.liftCompιIso (RX'.ι ⋙ Sf') hSf').symm)
        θs')
    (K : QX.FullSubcategory) (h₁ : IsIso (ρf.app K.obj)) (h₂ : IsIso (ρf'.app (Hr.obj K.obj))) :
    Nonempty (Arrow.mk ((RY'.lift (QY'.ι ⋙ PY') hPY').map (βr.app K)) ≅
      Arrow.mk (βs.app ((RX.lift (QX.ι ⋙ PX) hPX).obj K))) := by
  subst hβr hβs
  exact nonempty_arrowIso_lift_map_exchangeRight_restrictFullyFaithful_app af af' bf bf' θr θs πf
    πf' πg πg' h ρf hρf ρf' hρf' hLf hRf hLf' hRf' hGr hHr hMf hSf hMf' hSf' hGs hHs hPX hPY' θr'
    hθr θs' hθs K h₁ h₂


end Cube

end Adjunction

end CategoryTheory
