/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Underlying sets of abelian inverse image

Source: Stacks Project, Sites, Section 00YR and Proposition 00YV (2), and
Modules on Sites, proof of Lemma 04JC
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Section 00YR and Proposition 00YV (2), and
Modules on Sites, first paragraph of the proof of Lemma 04JC
(auxiliary; not a blueprint node).

The site object and morphism universes may differ. Sheafification and left Kan
extension existence are explicit hypotheses; coefficients live in `max u v w`.

Proof: Identify abelian sheaves on both sites with commutative group objects in
sheaves of sets, using `sheavesAlgebraicStructuresAbelian`. Lift the set-valued
pullback-pushforward adjunction using `Adjunction.mapCommGrp`: finite
limit preservation implies finite product preservation, so the left lift has
underlying functor equal to set-valued pullback. The right lift is naturally
isomorphic to abelian pushforward: precomposition computes products sectionwise,
so its transported multiplication, unit and inverse are the original sectionwise
addition, zero and negation. Transport the lifted adjunction across the two
identifications. Both its left adjoint and the constructed abelian pullback are
left adjoint to abelian pushforward. Uniqueness of left adjoints gives a natural
isomorphism between them. Composing with the forgetful identifications gives the
asserted isomorphism of underlying sheaves, on objects and morphisms. -/
theorem sitePullback_abelian_underlying_of_hasSheafify
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K]
    [HasWeakSheafify K (Type (max u v w))]
    [HasWeakSheafify K AddCommGrpCat.{max u v w}]
    [∀ F : Cᵒᵖ ⥤ Type (max u v w), U.op.HasLeftKanExtension F]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}, U.op.HasLeftKanExtension F]
    [PreservesFiniteLimits (sheafPullback U (Type (max u v w)) J K)] :
    Nonempty (sheafPullback U AddCommGrpCat.{max u v w} J K ⋙
        sheafCompose K (forget AddCommGrpCat.{max u v w}) ≅
      sheafCompose J (forget AddCommGrpCat.{max u v w}) ⋙
        sheafPullback U (Type (max u v w)) J K) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    let : BraidedCategory (Sheaf J (Type (max u v w))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let : BraidedCategory (Sheaf K (Type (max u v w))) :=
      BraidedCategory.ofCartesianMonoidalCategory
    let R := U.sheafPushforwardContinuous (Type (max u v w)) J K
    let : R.Braided := Functor.Braided.ofChosenFiniteProducts R
    let Rab := U.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K
    obtain ⟨FJ, GJ, hFJ, hGJ, hFJGJ, hGJFJ, opJ, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u, v, w} J
    obtain ⟨FK, GK, hFK, hGK, hFKGK, hGKFK, opK, _⟩ :=
      sheavesAlgebraicStructuresAbelian.{u, v, w} K
    let EJ := Equivalence.mk FJ GJ (eqToIso hFJGJ.symm) (eqToIso hGJFJ)
    let EK := Equivalence.mk FK GK (eqToIso hFKGK.symm) (eqToIso hGKFK)
    let e : (FK ⋙ R.mapCommGrp) ⋙ CommGrp.forget _ ≅
        (Rab ⋙ FJ) ⋙ CommGrp.forget _ :=
      (Functor.associator FK (CommGrp.forget _) R).symm ≪≫
        Functor.isoWhiskerRight (eqToIso hFK) R ≪≫
        Iso.refl _ ≪≫
        Functor.isoWhiskerLeft Rab (eqToIso hFJ).symm
    have hprod (X Y : Sheaf K (Type (max u v w))) :
        (CartesianMonoidalCategory.prodComparisonIso R X Y).inv = 𝟙 _ := by
      have h : (CartesianMonoidalCategory.prodComparisonIso R X Y).hom = 𝟙 _ := by
        rfl
      change (CartesianMonoidalCategory.prodComparisonIso R X Y).inv =
        𝟙 (R.obj (MonoidalCategory.tensorObj X Y))
      simpa only [h, Category.id_comp] using
      (CartesianMonoidalCategory.prodComparisonIso R X Y).hom_inv_id
    have hone : (CartesianMonoidalCategory.preservesTerminalIso R).inv = 𝟙 _ := by
      rfl
    have he (A : Sheaf K AddCommGrpCat.{max u v w}) :
        (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) =
          R.map ((eqToIso hFK).hom.app A) := by
      simp [e]
    let egroup : FK ⋙ R.mapCommGrp ≅ Rab ⋙ FJ :=
      NatIso.ofComponents (fun A ↦ CommGrp.mkIso (e.app A) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.ε R ≫ R.map MonObj.one) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.ε_of_cartesianMonoidalCategory, hone, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X t
        exact (opK A (U.op.obj X)).2.1 t |>.trans
          ((opJ (Rab.obj A) X).2.1 t).symm) (by
        apply (cancel_mono ((eqToIso hFJ).hom.app (Rab.obj A))).1
        change (Functor.LaxMonoidal.μ R _ _ ≫ R.map MonObj.mul) ≫
          (e.app A).hom ≫ (eqToIso hFJ).hom.app (Rab.obj A) = _
        rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory, hprod, Category.id_comp, he]
        apply Sheaf.hom_ext
        ext X ab
        rcases ab with ⟨a, b⟩
        change ((eqToIso hFK).hom.app A).hom.app (U.op.obj X)
          ((MonObj.mul (X := (FK.obj A).X)).hom.app (U.op.obj X) (a, b)) = _
        rw [(opK A (U.op.obj X)).1 a b]
        change _ = ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
          ((MonObj.mul (X := (FJ.obj (Rab.obj A)).X)).hom.app X
            (((e.app A).hom.hom.app X) a, ((e.app A).hom.hom.app X) b))
        rw [(opJ (Rab.obj A) X).1]
        have hea (x : (R.obj (FK.obj A).X).obj.obj X) :
            ((eqToIso hFJ).hom.app (Rab.obj A)).hom.app X
                (((e.app A).hom.hom.app X) x) =
              ((eqToIso hFK).hom.app A).hom.app (U.op.obj X) x :=
          congrArg (fun f ↦ f.hom.app X x) (he A)
        rw [hea a, hea b])) (by
        intro A B f
        apply CommGrp.hom_ext
        exact e.hom.naturality f)
    let eR := Functor.isoWhiskerRight egroup GJ ≪≫
      Functor.associator Rab FJ GJ ≪≫
      Functor.isoWhiskerLeft Rab (eqToIso hFJGJ) ≪≫ Rab.rightUnitor
    -- Lift and transport the adjunction using Mathlib's canonical commutative-group lift.
    let L := sheafPullback U (Type (max u v w)) J K
    let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
    let adj := sheafAdjunctionContinuous U (Type (max u v w)) J K
    let lifted := (EJ.toAdjunction.comp adj.mapCommGrp).comp EK.symm.toAdjunction
    let transported := lifted.ofNatIsoRight eR
    let comparison :=
      (sheafAdjunctionContinuous U AddCommGrpCat.{max u v w} J K).leftAdjointUniq transported
    refine ⟨Functor.isoWhiskerRight comparison _ ≪≫ ?_⟩
    exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso hGK) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Iso.refl _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight (eqToIso hFJ) L)

end CategoryTheory
