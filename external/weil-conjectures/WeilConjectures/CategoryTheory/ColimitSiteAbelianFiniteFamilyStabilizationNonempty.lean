/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ColimitSiteAbelianFiniteIndexedMatching

/-! # Nonempty finite-family stabilization

Source: Stacks Project, Sites, Tag 0A35.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem comparison_exists
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u}) :
    ∃ a : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
        ((sheafPullback h AddCommGrpCat.{u} T R).obj G),
      ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
        (op X)) := by
  subst h
  let A := sheafAdjunctionContinuous f AddCommGrpCat.{u} T S
  let B := sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R
  let H := (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
    ((sheafPullback (f ⋙ g) AddCommGrpCat.{u} T R).obj G)
  let a := (A.homEquiv G H).symm (B.unit.app G)
  refine ⟨a, ?_⟩
  intro X
  have ha := (A.homEquiv G H).apply_symm_apply (B.unit.app G)
  exact congrArg (fun z ↦ Arrow.mk (z.hom.app (op X))) ha

private theorem presieve_map_eq_ofArrows
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (f : C ⥤ D) {W : C} (T : Presieve W) :
    T.map f = Presieve.ofArrows (fun s : T.uncurry ↦ f.obj s.val.1)
      (fun s : T.uncurry ↦ f.map s.val.2) := by
  funext Y g
  apply propext
  constructor
  · rintro ⟨hg⟩
    exact Presieve.ofArrows.mk (⟨⟨_, _⟩, hg⟩ : T.uncurry)
  · rintro ⟨s⟩
    exact Presieve.map.of s.property

/-- Nonempty-cover reduction for finite family stabilization.
Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-abelian-finite-family-stabilization-nonempty)
-/
theorem colimit_site_abelian_finite_family_stabilization_nonempty
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u})
    (α : ∀ t : Under i,
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (t : Under i) (W : F.obj t.right) (T : Presieve W) (hT : T ∈ P t.right W)
    (hTnonempty : Nonempty T.uncurry)
    (y : T.FamilyOfElements
      (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
          forget AddCommGrpCat.{u}))
    (hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙
          (ColimitSiteStageImage.target F P V Q i G).obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible) :
    ∃ (t' : Under i) (W' : F.obj t'.right) (T' : Presieve W'), T' ∈ P t'.right W' ∧
      ∃ (hW : (V.ι.app t'.right).toFunctor.obj W' = (V.ι.app t.right).toFunctor.obj W)
        (y' : T'.FamilyOfElements
          (((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        y'.Compatible ∧ ∀ {Z' : F.obj t'.right} (g' : Z' ⟶ W') (hg' : T' g'),
          ∃ (Z : F.obj t.right) (g : Z ⟶ W) (hg : T g)
            (r : (V.ι.app t'.right).toFunctor.obj Z' ⟶ (V.ι.app t.right).toFunctor.obj Z),
            (V.ι.app t'.right).toFunctor.map g' ≫ eqToHom hW =
              r ≫ (V.ι.app t.right).toFunctor.map g ∧
            (α t').hom.app (op Z') (y' g' hg') =
              (ColimitSiteStageImage.target F P V Q i G).obj.map r.op
                ((α t).hom.app (op Z) (y g hg)) := by
  classical
  rcases hTnonempty with ⟨_⟩
  have w {s s' : Under i} (b : s ⟶ s') :
      (F.map s.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map s'.hom).toFunctor := by
    change (F.map s.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  choose θ hθ using fun (s s' : Under i) (b : s ⟶ s') ↦
    comparison_exists (P i).toGrothendieck (P s.right).toGrothendieck
      (P s'.right).toGrothendieck (F.map s.hom).toFunctor
      (F.map b.right).toFunctor (F.map s'.hom).toFunctor (w b) G
  obtain ⟨t', b, hm⟩ := colimit_site_abelian_finite_indexed_matching
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
    i G α θ hα hθ t W T hT y hy
  let f := (F.map b.right).toFunctor
  let W' := f.obj W
  let T' : Presieve W' := Presieve.ofArrows (fun s : T.uncurry ↦ f.obj s.val.1)
    (fun s : T.uncurry ↦ f.map s.val.2)
  have hT' : T' ∈ P t'.right W' := by
    dsimp only [T', W']
    rw [← presieve_map_eq_ofArrows f T]
    exact hcover t.right t'.right b.right W T hT
  have hv : f ⋙ (V.ι.app t'.right).toFunctor = (V.ι.app t.right).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w b.right)
  let hW : (V.ι.app t'.right).toFunctor.obj W' =
      (V.ι.app t.right).toFunctor.obj W := Functor.congr_obj hv W
  let y' := hm.familyOfElements
  refine ⟨t', W', T', hT', hW, y', hm.familyOfElements_compatible, ?_⟩
  intro Z' g' hg'
  obtain ⟨s⟩ := hg'
  let hZ := Functor.congr_obj hv s.val.1
  refine ⟨s.val.1, s.val.2, s.property, eqToHom hZ, ?_, ?_⟩
  · change (f ⋙ (V.ι.app t'.right).toFunctor).map s.val.2 ≫ eqToHom hW = _
    rw [Functor.congr_hom hv s.val.2]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · change (α t').hom.app (op (f.obj s.val.1))
      (hm.familyOfElements _ (Presieve.ofArrows.mk s)) = _
    rw [hm.familyOfElements_ofArrows_mk]
    have hc := sheaf_comparison_comp (P i).toGrothendieck
      (P t.right).toGrothendieck (P t'.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor f (V.ι.app t'.right).toFunctor
      (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
      (w b) (congrArg Cat.Hom.toFunctor (V.w t'.hom)) hv G
      ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G)
      (ColimitSiteStageImage.target F P V Q i G)
      ((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app G)
      ((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck Q.toGrothendieck).unit.app G)
      (θ t t' b) (α t') (α t) (hθ t t' b) (hα t') (hα t) s.val.1
    have hc' : (θ t t' b).hom.app (op s.val.1) ≫
        (α t').hom.app (op (f.obj s.val.1)) =
        (α t).hom.app (op s.val.1) ≫
          (ColimitSiteStageImage.target F P V Q i G).obj.map (eqToHom hZ).op := by
      apply Arrow.mk_injective
      simpa only [eqToHom_op, eqToHom_map, Arrow.arrow_mk_comp_eqToHom] using hc
    exact ConcreteCategory.congr_hom hc' (y s.val.2 s.property)


end CategoryTheory
