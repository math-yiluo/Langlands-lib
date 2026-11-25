/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.CategoryTheory.PullbackFamily

/-!

# Base change for a family of pushforwards

Let `P` be a family of pullbacks `P f : D Y ⥤ D X` with composition isomorphisms
`c f g : P (f ≫ g) ≅ P g ⋙ P f` (`CategoryTheory.PullbackAssoc`), and `Q f : D X ⥤ D Y` right
adjoints `P f ⊣ Q f`. For a commutative square `g' ≫ f = f' ≫ g`, the base-change morphism
`Q f ⋙ P g ⟶ P g' ⋙ Q f'` (`CategoryTheory.pushforwardBaseChange`) is the exchange morphism of the
comparison `P g ⋙ P f' ≅ P f ⋙ P g'` of the composition isomorphisms
(`CategoryTheory.pullbackFamilySquareComparison`). The base-change morphisms of two horizontally
pasted squares paste (`CategoryTheory.pushforwardBaseChange_app_paste`).

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : C → Type*} [∀ X, Category (D X)]
  {P : ∀ {X Y : C}, (X ⟶ Y) → D Y ⥤ D X}
  {c : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f}
  {Q : ∀ {X Y : C}, (X ⟶ Y) → D X ⥤ D Y} (adj : ∀ {X Y : C} (f : X ⟶ Y), P f ⊣ Q f)


section BaseChange

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

variable (c) in
/-- The comparison `P g ⋙ P f' ≅ P f ⋙ P g'` of a commutative square `g' ≫ f = f' ≫ g`, through
the composition isomorphisms. -/
def pullbackFamilySquareComparison (h : g' ≫ f = f' ≫ g) : P g ⋙ P f' ≅ P f ⋙ P g' :=
  (c f' g).symm ≪≫ eqToIso (congrArg (fun x ↦ P x) h.symm) ≪≫ c g' f

lemma pullbackFamilySquareComparison_hom_app (h : g' ≫ f = f' ≫ g) (N : D Y) :
    (pullbackFamilySquareComparison c h).hom.app N =
      (c f' g).inv.app N ≫ eqToHom (by rw [h]) ≫ (c g' f).hom.app N := by
  simp [pullbackFamilySquareComparison, eqToHom_app]

variable (c) in
/-- The base-change morphism `Q f ⋙ P g ⟶ P g' ⋙ Q f'` of a commutative square
`g' ≫ f = f' ≫ g`: the exchange morphism of `pullbackFamilySquareComparison` under the
adjunctions `P f ⊣ Q f` and `P f' ⊣ Q f'`. -/
def pushforwardBaseChange (h : g' ≫ f = f' ≫ g) : Q f ⋙ P g ⟶ P g' ⋙ Q f' :=
  Adjunction.exchangeRight (adj f) (adj f') (pullbackFamilySquareComparison c h)

variable {X'' Y'' : C} {k : Y'' ⟶ Y'} {k' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- **Pasting law of the pullback comparisons**: the comparison of the outer square of two
horizontally pasted squares is the pasting of their comparisons, through the composition
isomorphisms. The squares are
```
X'' --k'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --k---> Y' --g---> Y
```
-/
lemma pullbackFamilySquareComparison_paste (hc : PullbackAssoc P c) (h₁ : g' ≫ f = f' ≫ g)
    (h₂ : k' ≫ f' = f'' ≫ k) (h : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) (N : D Y) :
    (P f'').map ((c k g).hom.app N) ≫
        (pullbackFamilySquareComparison c h₂).hom.app ((P g).obj N) ≫
          (P k').map ((pullbackFamilySquareComparison c h₁).hom.app N) =
      (pullbackFamilySquareComparison c h).hom.app N ≫ (c k' g').hom.app ((P f).obj N) := by
  rw [← cancel_epi ((c f'' (k ≫ g)).hom.app N), pullbackFamilySquareComparison_hom_app,
    pullbackFamilySquareComparison_hom_app, pullbackFamilySquareComparison_hom_app]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [hc.hom_app_comp_map_hom_app_assoc f'' k g, Iso.hom_inv_id_app_assoc,
    pullbackComp_hom_app_comp_eqToHom_left_assoc (c := c) h₂.symm g,
    reassoc_of% (hc.hom_app k' f' g N)]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_map,
    pullbackComp_hom_app_comp_eqToHom_right_assoc (c := c) k' h₁.symm,
    hc.hom_app_comp_map_hom_app k' g' f]
  simp only [eqToHom_trans_assoc]

/-- **Pasting law of the base-change morphisms**: the base-change morphism of the outer square of
two horizontally pasted squares is the pasting of their base-change morphisms, through the
composition isomorphisms. The squares are
```
X'' --k'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --k---> Y' --g---> Y
```
-/
@[reassoc]
lemma pushforwardBaseChange_app_paste (hc : PullbackAssoc P c) (h₁ : g' ≫ f = f' ≫ g)
    (h₂ : k' ≫ f' = f'' ≫ k) (h : (k' ≫ g') ≫ f = f'' ≫ (k ≫ g)) (M : D X) :
    (c k g).hom.app ((Q f).obj M) ≫ (P k).map ((pushforwardBaseChange c adj h₁).app M) ≫
        (pushforwardBaseChange c adj h₂).app ((P g').obj M) =
      (pushforwardBaseChange c adj h).app M ≫ (Q f'').map ((c k' g').hom.app M) :=
  Adjunction.exchangeRight_app_paste (adj f) (adj f') (adj f'')
    (pullbackFamilySquareComparison c h₁) (pullbackFamilySquareComparison c h₂)
    (pullbackFamilySquareComparison c h) (c k g) (c k' g')
    (pullbackFamilySquareComparison_paste hc h₁ h₂ h) M

end BaseChange

end CategoryTheory
