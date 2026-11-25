module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_

@[expose] public section

universe vA vB uA uB

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Intermediate construction of the lifted commutative-group adjunction.
(blueprint: lem-weil-pbc-lifted-comm-group-branch)
Source: Stacks Project, Proposition 00YV, proof of the abelian-group part.

Proof: use `Adjunction.mapCommGrp` with the canonical braided structures induced by
Cartesian monoidal categories.  Its transported operations are expressed by the
product and terminal comparison isomorphisms.  Naturality of those comparisons
proves that the transported operations satisfy the group axioms and that maps of
objects remain morphisms.  The hom-equivalence of the original adjunction restricts
to group morphisms because the unit and counit preserve all three operations;
its inverse is given by composing with the counit.  The displayed comparison,
unit, counit, and adjunct equations are exactly these naturality identities.
-/
theorem liftedCommGrpBranch
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [PreservesFiniteProducts L]
    [PreservesFiniteProducts R] :
    let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    (∃ (LF : CommGrp A ⥤ CommGrp B) (RF : CommGrp B ⥤ CommGrp A)
          (hL : LF ⋙ CommGrp.forget B = CommGrp.forget A ⋙ L)
          (hR : RF ⋙ CommGrp.forget A = CommGrp.forget B ⋙ R),
        let eL := eqToIso hL
        let eR := eqToIso hR
        ∃ (a : LF ⊣ RF),
          (∀ X : CommGrp A,
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (GrpObj.inv (X := X.X))) ∧
          (∀ X : CommGrp B,
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (GrpObj.inv (X := X.X))) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (f : LF.obj X ⟶ Y),
            (CommGrp.forget A).map (a.homEquiv X Y f) ≫ eR.hom.app Y =
              adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommGrp.forget B).map f)) ∧
          (∀ X : CommGrp A,
            (CommGrp.forget A).map (a.unit.app X) ≫ eR.hom.app (LF.obj X) ≫
                R.map (eL.hom.app X) = adj.unit.app X.X) ∧
          (∀ Y : CommGrp B,
            L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
                (CommGrp.forget B).map (a.counit.app Y) = adj.counit.app Y.X) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (α : L.obj X.X ⟶ Y.X),
            (∃ f : LF.obj X ⟶ Y, eL.inv.app X ≫ (CommGrp.forget B).map f = α) ↔
              ∃ g : X ⟶ RF.obj Y,
                (CommGrp.forget A).map g ≫ eR.hom.app Y = adj.homEquiv X.X Y.X α)) := by
  let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
  let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
  have hforward (X : CommGrp A) (Y : CommGrp B) (f : L.mapCommGrp.obj X ⟶ Y) :
      (adj.mapCommGrp.homEquiv X Y f).hom.hom.hom =
        adj.homEquiv X.X Y.X f.hom.hom.hom := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (𝟙 _ ≫ adj.unit.app X.X ≫ 𝟙 _) ≫ R.map f.hom.hom.hom = _
    simp only [Category.id_comp, Category.comp_id]
  refine ⟨L.mapCommGrp, R.mapCommGrp, rfl, rfl, adj.mapCommGrp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    change
      ((Functor.LaxMonoidal.μ L X.X X.X ≫ L.map MonObj.mul) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (prodComparisonIso L X.X X.X).inv ≫ L.map MonObj.mul) ∧
      ((Functor.LaxMonoidal.ε L ≫ L.map MonObj.one) ≫ 𝟙 _ =
        (preservesTerminalIso L).inv ≫ L.map MonObj.one) ∧
      (L.map GrpObj.inv ≫ 𝟙 _ = 𝟙 _ ≫ L.map GrpObj.inv)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      Functor.Monoidal.ε_of_cartesianMonoidalCategory, and_self]
  · intro X
    change
      ((Functor.LaxMonoidal.μ R X.X X.X ≫ R.map MonObj.mul) ≫ 𝟙 _ =
        (𝟙 _ ⊗ₘ 𝟙 _) ≫ (prodComparisonIso R X.X X.X).inv ≫ R.map MonObj.mul) ∧
      ((Functor.LaxMonoidal.ε R ≫ R.map MonObj.one) ≫ 𝟙 _ =
        (preservesTerminalIso R).inv ≫ R.map MonObj.one) ∧
      (R.map GrpObj.inv ≫ 𝟙 _ = 𝟙 _ ≫ R.map GrpObj.inv)
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      Functor.Monoidal.ε_of_cartesianMonoidalCategory, and_self]
  · intro X Y f
    change (adj.mapCommGrp.homEquiv X Y f).hom.hom.hom ≫ 𝟙 _ =
      adj.homEquiv X.X Y.X (𝟙 _ ≫ f.hom.hom.hom)
    simp only [Category.comp_id, Category.id_comp]
    exact hforward X Y f
  · intro X
    change (𝟙 _ ≫ adj.unit.app X.X ≫ 𝟙 _) ≫ 𝟙 _ ≫ R.map (𝟙 _) = _
    simp only [Functor.map_id, Category.comp_id, Category.id_comp]
    exact Category.comp_id _
  · intro Y
    change L.map (𝟙 _) ≫ 𝟙 _ ≫ (𝟙 _ ≫ adj.counit.app Y.X ≫ 𝟙 _) = _
    simp only [Category.comp_id, Category.id_comp, Functor.map_id]
  · intro X Y α
    change (∃ f : L.mapCommGrp.obj X ⟶ Y, 𝟙 _ ≫ f.hom.hom.hom = α) ↔
      ∃ g : X ⟶ R.mapCommGrp.obj Y,
        g.hom.hom.hom ≫ 𝟙 _ = adj.homEquiv X.X Y.X α
    simp only [Category.id_comp, Category.comp_id]
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨adj.mapCommGrp.homEquiv X Y f, (hforward X Y f).trans (congrArg _ hf)⟩
    · rintro ⟨g, hg⟩
      refine ⟨(adj.mapCommGrp.homEquiv X Y).symm g, ?_⟩
      apply (adj.homEquiv X.X Y.X).injective
      rw [← hforward X Y, Equiv.apply_symm_apply, hg]

end CategoryTheory.Adjunction
