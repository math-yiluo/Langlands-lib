/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The mate of a pasting of three squares

Let `α : (E ⋙ J ⋙ I) ⋙ Lf' ⟶ Lf ⋙ E' ⋙ J' ⋙ I'` be the horizontal pasting of three 2-squares
`γ₁ : E ⋙ Lg ⟶ Lf ⋙ E'`, `γ₂ : J ⋙ Lt ⟶ Lg ⋙ J'` and `γ₃ : I ⋙ Lf' ⟶ Lt ⋙ I'` whose vertical
functors `Lf`, `Lg`, `Lt`, `Lf'` are left adjoints. The component at `K` of the mate of `α` is the
composite of the components of the mates of `γ₁`, `γ₂` and `γ₃`
(`CategoryTheory.mateEquiv_app_eq_comp_of_eq_pasting`), by `CategoryTheory.mateEquiv_vcomp`.
-/

@[expose] public section

namespace CategoryTheory

variable {DY DGN DTN DY' DX DGM DTM DX' : Type*} [Category* DY] [Category* DGN] [Category* DTN]
  [Category* DY'] [Category* DX] [Category* DGM] [Category* DTM] [Category* DX']
  {EN : DY ⥤ DGN} {JN : DGN ⥤ DTN} {IN : DTN ⥤ DY'} {EM : DX ⥤ DGM} {JM : DGM ⥤ DTM}
  {IM : DTM ⥤ DX'} {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lg : DGN ⥤ DGM} {Rg : DGM ⥤ DGN}
  {Lt : DTN ⥤ DTM} {Rt : DTM ⥤ DTN} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}

/-- **The mate of a pasting of three squares.** Let
`α : (EN ⋙ JN ⋙ IN) ⋙ Lf' ⟶ Lf ⋙ EM ⋙ JM ⋙ IM` be the horizontal pasting of three 2-squares
`γ₁ : EN ⋙ Lg ⟶ Lf ⋙ EM`, `γ₂ : JN ⋙ Lt ⟶ Lg ⋙ JM` and `γ₃ : IN ⋙ Lf' ⟶ Lt ⋙ IM` with left
adjoint vertical functors:
```
     EN       JN       IN
 DY ---> DGN ---> DTN ---> DY'
 |        |        |        |
 Lf  γ₁   Lg  γ₂   Lt  γ₃   Lf'
 v        v        v        v
 DX ---> DGM ---> DTM ---> DX'
     EM       JM       IM
```
Then the component at `K` of the mate `Rf ⋙ EN ⋙ JN ⋙ IN ⟶ (EM ⋙ JM ⋙ IM) ⋙ Rf'` of `α` is the
composite of the mates of `γ₁`, `γ₂` and `γ₃`. -/
lemma mateEquiv_app_eq_comp_of_eq_pasting (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjt : Lt ⊣ Rt)
    (adjf' : Lf' ⊣ Rf') (γ₁ : EN ⋙ Lg ⟶ Lf ⋙ EM) (γ₂ : JN ⋙ Lt ⟶ Lg ⋙ JM)
    (γ₃ : IN ⋙ Lf' ⟶ Lt ⋙ IM) (α : (EN ⋙ JN ⋙ IN) ⋙ Lf' ⟶ Lf ⋙ EM ⋙ JM ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JN) γ₃ ≫
      Functor.whiskerRight (Functor.whiskerLeft EN γ₂ ≫ Functor.whiskerRight γ₁ JM) IM)
    (K : DX) :
    (mateEquiv adjf adjf' α).app K =
      IN.map (JN.map ((mateEquiv adjf adjg γ₁).app K)) ≫
        IN.map ((mateEquiv adjg adjt γ₂).app (EM.obj K)) ≫
          (mateEquiv adjt adjf' γ₃).app (JM.obj (EM.obj K)) := by
  have h : α = (TwoSquare.hComp (TwoSquare.hComp γ₁ γ₂) γ₃ : TwoSquare _ _ _ _) := by
    subst hα
    ext X
    simp [TwoSquare.hComp]
  subst h
  have e₂ := NatTrans.congr_app (mateEquiv_vcomp adjf adjt adjf' (TwoSquare.hComp γ₁ γ₂) γ₃) K
  have e₁ := NatTrans.congr_app (mateEquiv_vcomp adjf adjg adjt γ₁ γ₂) K
  refine e₂.trans ?_
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj] at e₁ ⊢
  rw [e₁]
  simp

/-- A form of `CategoryTheory.mateEquiv_app_eq_comp_of_eq_pasting` in which the mates are given
through equations, so that it can be applied to transformations defined as mates. -/
lemma app_eq_comp_of_eq_mateEquiv_pasting (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjt : Lt ⊣ Rt)
    (adjf' : Lf' ⊣ Rf') (γ₁ : EN ⋙ Lg ⟶ Lf ⋙ EM) (γ₂ : JN ⋙ Lt ⟶ Lg ⋙ JM)
    (γ₃ : IN ⋙ Lf' ⟶ Lt ⋙ IM) (α : (EN ⋙ JN ⋙ IN) ⋙ Lf' ⟶ Lf ⋙ EM ⋙ JM ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JN) γ₃ ≫
      Functor.whiskerRight (Functor.whiskerLeft EN γ₂ ≫ Functor.whiskerRight γ₁ JM) IM)
    (χ : Rf ⋙ EN ⋙ JN ⋙ IN ⟶ (EM ⋙ JM ⋙ IM) ⋙ Rf') (hχ : χ = (mateEquiv adjf adjf' α))
    (β₁ : Rf ⋙ EN ⟶ EM ⋙ Rg) (hβ₁ : β₁ = (mateEquiv adjf adjg γ₁))
    (β₂ : Rg ⋙ JN ⟶ JM ⋙ Rt) (hβ₂ : β₂ = (mateEquiv adjg adjt γ₂))
    (β₃ : Rt ⋙ IN ⟶ IM ⋙ Rf') (hβ₃ : β₃ = (mateEquiv adjt adjf' γ₃)) (K : DX) :
    χ.app K = IN.map (JN.map (β₁.app K)) ≫ IN.map (β₂.app (EM.obj K)) ≫
      β₃.app (JM.obj (EM.obj K)) := by
  subst hχ hβ₁ hβ₂ hβ₃
  exact mateEquiv_app_eq_comp_of_eq_pasting adjf adjg adjt adjf' γ₁ γ₂ γ₃ α hα K

end CategoryTheory
