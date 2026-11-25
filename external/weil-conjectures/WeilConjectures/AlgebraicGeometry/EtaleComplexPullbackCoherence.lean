/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Coherence of termwise pullbacks over a cone

Source: Stacks Project, Tag 0GIT, proof, and inverse-image composition coherence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale


set_option backward.defeqAttrib.useBackward true

private lemma composition_cancel {V : Type*} [Category V]
    {A B C D : V} (a : A ⟶ B) (b : B ⟶ C) (e : D ≅ C) (d : A ⟶ D)
    (h : a ≫ b = d ≫ e.hom) : d = a ≫ b ≫ e.inv := by
  exact ((Iso.eq_comp_inv e).mpr h.symm).trans (Category.assoc _ _ _)

private lemma cone_cancel {V : Type*} [Category V]
    {A B C D : V} (e : A ≅ B) (e' : A ≅ D) (a : B ⟶ C) (b : C ⟶ D)
    (h : a ≫ b = e.inv ≫ e'.hom) : 𝟙 A = e.hom ≫ a ≫ b ≫ e'.inv := by
  rw [← Category.assoc a b, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]

private lemma iso_unit_transport {α V W : Type*} [Category V] [Category W]
    (P : α → (V ⥤ V)) (Q : W ⥤ V) (H : α → Prop)
    (E : ∀ a, H a → (Q ≅ Q ⋙ P a)) (a a₀ : α) (ha : a = a₀)
    (h : H a) (h₀ : H a₀) (U : P a₀ ≅ 𝟭 V)
    (hE : E a₀ h₀ = (Functor.rightUnitor Q).symm ≪≫ Functor.isoWhiskerLeft Q U.symm)
    (G : W) :
    (E a h).inv.app G = (eqToIso (congrArg P ha)).hom.app (Q.obj G) ≫
      U.hom.app (Q.obj G) := by
  subst a
  rw [hE]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact Category.comp_id _

private lemma unit_comparison {X T : Scheme.{u}} (a : X ⟶ X) (ha : a = 𝟙 X)
    (g : X ⟶ T) (h : g = a ≫ g) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} a g g h).inv.app G =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) ha)).hom.app
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) ≫
      (upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) := by
  exact iso_unit_transport (upperStar AddCommGrpCat.{u + 1})
    (upperStar AddCommGrpCat.{u + 1} g) (fun a ↦ g = a ≫ g)
    (fun a h ↦ upperStarComp AddCommGrpCat.{u + 1} a g g h)
    a (𝟙 X) ha h (Category.id_comp g).symm
    (upperStarId AddCommGrpCat.{u + 1} X)
    (upperStarComp_id_left AddCommGrpCat.{u + 1} g) G


/-- Termwise comparisons satisfy the unit, associativity, and cone transition laws.
Source: Stacks Project, Tag 0GIT, proof, termwise pullbacks, expanded using the
inverse-image composition and identity comparisons.
(blueprint: lem-weil-pbc-etale-complex-pullback-coherence)

Proof: evaluate inverse-image unit and associativity at each degree of C. The
inverse of the composition comparison defines phi. The left unit law, together
with D.map_id and the naturality of t at the identity, gives the first equality.
For composable f and g, apply the associativity law to D.map g, D.map f, and
 t.app i. Substitute D.map_comp and naturality of t; cancel the outer composition
comparison to get the second equality. For the final equality apply associativity
to c.π.app j, D.map f, and t.app i. Substitute the cone equation c.w f, the
naturality of t, and hp. Cancel the composition comparison for c.π.app j and
 t.app j. The composite displayed then equals the identity on p inverse image C.
Equality of complex maps follows from equality in every degree. These arguments
also apply to identity arrows and to a constant diagram; no cofilteredness or
universal property of the cone is needed. -/
theorem presentation_pullback_coherence
    {I : Type u} [SmallCategory I] (T : Scheme.{u})
    (D : I ⥤ Scheme.{u}) (c : Cone D) (t : D ⟶ (Functor.const I).obj T)
    (p : c.pt ⟶ T) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    let F := fun i : I =>
      ((upperStar AddCommGrpCat.{u + 1} (t.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C
    let φ := fun {i j : I} (f : j ⟶ i) =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm))
        (ComplexShape.up ℤ)).inv.app C
    let eG := fun i : I =>
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p (hp i).symm)
        (ComplexShape.up ℤ)).app C
    (∀ i : I, φ (𝟙 i) = presentationIdentityMap D i (F i)) ∧
    (∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : j ⟶ i), ((Functor.const Iᵒᵖ).obj
      (((upperStar AddCommGrpCat.{u + 1} p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)).map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply HomologicalComplex.hom_ext
    intro n
    change (upperStarComp AddCommGrpCat.{u + 1} (D.map (𝟙 i)) (t.app i) (t.app i)
      ((Category.comp_id (t.app i)).symm.trans (t.naturality (𝟙 i)).symm)).inv.app
        (C.X n) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i))).hom.app
        ((upperStar AddCommGrpCat.{u + 1} (t.app i)).obj (C.X n)) ≫
      (upperStarId AddCommGrpCat.{u + 1} (D.obj i)).hom.app
        ((upperStar AddCommGrpCat.{u + 1} (t.app i)).obj (C.X n))
    exact unit_comparison (D.map (𝟙 i)) (D.map_id i) (t.app i) _ (C.X n)
  · intro i j k f g
    apply HomologicalComplex.hom_ext
    intro n
    change (upperStarComp AddCommGrpCat.{u + 1} (D.map (g ≫ f)) (t.app i) (t.app k)
      ((Category.comp_id (t.app k)).symm.trans (t.naturality (g ≫ f)).symm)).inv.app
        (C.X n) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f) (D.map (g ≫ f))
        (D.map_comp g f)).hom.app
          ((upperStar AddCommGrpCat.{u + 1} (t.app i)).obj (C.X n)) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g)).map
        ((upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm)).inv.app
            (C.X n)) ≫
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (t.app j) (t.app k)
        ((Category.comp_id (t.app k)).symm.trans (t.naturality g).symm)).inv.app (C.X n)
    have h := upperStarComp_hom_app_map_upperStarComp_inv_app
      AddCommGrpCat.{u + 1} (D.map g) (D.map f) (t.app i)
      (D.map (g ≫ f)) (t.app j) (t.app k) (D.map_comp g f)
      ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm)
      ((Category.comp_id (t.app k)).symm.trans (t.naturality (g ≫ f)).symm)
      (C.X n)
    exact composition_cancel _ _
      ((upperStarComp AddCommGrpCat.{u + 1} (D.map g) (t.app j) (t.app k)
        ((Category.comp_id (t.app k)).symm.trans (t.naturality g).symm)).app (C.X n))
      _ h
  · intro i j f
    apply HomologicalComplex.hom_ext
    intro n
    change 𝟙 ((upperStar AddCommGrpCat.{u + 1} p).obj (C.X n)) =
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p (hp i).symm).hom.app
        (C.X n) ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f) (c.π.app i)
        (c.w f).symm).hom.app
          ((upperStar AddCommGrpCat.{u + 1} (t.app i)).obj (C.X n)) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app j)).map
        ((upperStarComp AddCommGrpCat.{u + 1} (D.map f) (t.app i) (t.app j)
          ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm)).inv.app
            (C.X n)) ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (t.app j) p (hp j).symm).inv.app
        (C.X n)
    have h := upperStarComp_hom_app_map_upperStarComp_inv_app
      AddCommGrpCat.{u + 1} (c.π.app j) (D.map f) (t.app i)
      (c.π.app i) (t.app j) p (c.w f).symm
      ((Category.comp_id (t.app j)).symm.trans (t.naturality f).symm)
      (hp i).symm (C.X n)
    exact cone_cancel
      ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app i) (t.app i) p
        (hp i).symm).app (C.X n))
      ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (t.app j) p
        (hp j).symm).app (C.X n)) _ _ h

end AlgebraicGeometry.Etale
