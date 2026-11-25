/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Isomorphisms of arrows from factorisations

An arrow `a ≫ c ≫ b` with `a` and `b` isomorphisms is isomorphic to `c`
(`CategoryTheory.Arrow.isoOfIsIsoComp`), and an isomorphism `x ≅ y` identifies the arrows
`H (α_x)` and `H (α_y)` attached to a natural transformation `α` and a functor `H`
(`CategoryTheory.Arrow.isoMapApp`). More generally, two arrows related by isomorphisms
through a commuting diagram are isomorphic (`CategoryTheory.Arrow.isoOfCompEq`). These are the
forms in which a morphism is identified with another one, up to isomorphism, once a factorisation
of it is known.
-/

@[expose] public section

namespace CategoryTheory.Arrow

variable {C : Type*} [Category* C]

/-- An arrow `a ≫ c ≫ b` with `a` and `b` isomorphisms is isomorphic to `c`. -/
@[simps!]
noncomputable def isoOfIsIsoComp {W X Y Z : C} (a : W ⟶ X) [IsIso a] (c : X ⟶ Y)
    (b : Y ⟶ Z) [IsIso b] : Arrow.mk (a ≫ c ≫ b) ≅ Arrow.mk c :=
  Arrow.isoMk (asIso a) (asIso b).symm (by simp)

/-- An isomorphism `x ≅ y` identifies the arrows `H (α_x)` and `H (α_y)`, for a natural
transformation `α : P ⟶ Q` and a functor `H`. -/
@[simps!]
def isoMapApp {D E : Type*} [Category* D] [Category* E] {P Q : C ⥤ D} (α : P ⟶ Q)
    (H : D ⥤ E) {x y : C} (ι : x ≅ y) :
    Arrow.mk (H.map (α.app x)) ≅ Arrow.mk (H.map (α.app y)) :=
  Arrow.isoMk (H.mapIso (P.mapIso ι)) (H.mapIso (Q.mapIso ι)) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Functor.mapIso_hom, Arrow.mk_hom, ← H.map_comp,
      α.naturality])

/-- If `f₁ ≫ δ = a ≫ m ≫ b` and a functor `H` sends `f₁`, `a` and `b` to isomorphisms, then
the arrows `H δ` and `H m` are isomorphic. -/
noncomputable def isoOfFac {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {P₀ P P' Q Q' : D} (δ : P ⟶ Q) (m : P' ⟶ Q') (f₁ : P₀ ⟶ P) (a : P₀ ⟶ P') (b : Q' ⟶ Q)
    (w : f₁ ≫ δ = a ≫ m ≫ b) [IsIso (H.map f₁)] [IsIso (H.map a)] [IsIso (H.map b)] :
    Arrow.mk (H.map δ) ≅ Arrow.mk (H.map m) :=
  Arrow.isoMk ((asIso (H.map f₁)).symm ≪≫ asIso (H.map a)) (asIso (H.map b)).symm (by
    simp only [Arrow.mk_left, Arrow.mk_right, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      asIso_hom, Arrow.mk_hom, Category.assoc, IsIso.inv_comp_eq, IsIso.eq_comp_inv,
      ← H.map_comp, w])

/-- The component of a whiskered natural transformation `E ◁ (α ▷ H)` at `x` is, as an arrow,
`H (α_{E x})`. Stated for abstract functors, this identification is checked syntactically
when the functors are instantiated. -/
lemma mk_whiskerLeft_whiskerRight_app {B D E : Type*} [Category* B] [Category* D]
    [Category* E] (F : B ⥤ C) {P Q : C ⥤ D} (α : P ⟶ Q) (H : D ⥤ E) (x : B) :
    Arrow.mk ((Functor.whiskerLeft F (Functor.whiskerRight α H)).app x) =
      Arrow.mk (H.map (α.app (F.obj x))) :=
  rfl

/-- If `a ≫ x = b ≫ y ≫ c` with `a`, `b` and `c` isomorphisms, the arrows `x` and `y` are
isomorphic. The hypothesis says that the two paths from `P` to `B` agree:
```
P --a--> A  --x--> B
P --b--> A' --y--> B' --c--> B
```
-/
noncomputable def isoOfCompEq {P A B A' B' : C} {x : A ⟶ B} {y : A' ⟶ B'} (a : P ⟶ A)
    (b : P ⟶ A') (c : B' ⟶ B) [IsIso a] [IsIso b] [IsIso c] (w : a ≫ x = b ≫ y ≫ c) :
    Arrow.mk x ≅ Arrow.mk y :=
  Arrow.isoMk (asIso (inv a ≫ b)) (asIso (inv c)) (by
    dsimp
    rw [← cancel_epi a, ← cancel_mono c]
    simp [reassoc_of% w])

end CategoryTheory.Arrow
