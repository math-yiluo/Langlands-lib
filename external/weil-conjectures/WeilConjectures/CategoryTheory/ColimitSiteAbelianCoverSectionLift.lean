/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import WeilConjectures.CategoryTheory.ColimitSiteAbelianFiniteObjectSectionLift

/-! # Individual stage lifts on a finite cover

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem map_comp_presieve
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (H : C ⥤ D) (K : D ⥤ E) {X : C} (S : Presieve X) :
    (S.map H).map K = S.map (H ⋙ K) := by
  apply le_antisymm
  · rintro _ _ ⟨⟨hf⟩⟩
    exact ⟨hf⟩
  · rintro _ _ ⟨hf⟩
    exact ⟨⟨hf⟩⟩

private theorem transported_map_presieve
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (H : C ⥤ D) (K : D ⥤ E) (L : C ⥤ E) (h : H ⋙ K = L)
    {X : C} (S : Presieve X) :
    (Functor.congr_obj h X) ▸ (S.map H).map K = S.map L := by
  rw [map_comp_presieve]
  cases h
  rfl

private theorem transport_presieve_mem
    {C : Type u} [SmallCategory C] {X Y Z : C} (h : X = Y)
    (S : Presieve X) (f : Z ⟶ X) (hf : S f) :
    (h ▸ S) (f ≫ eqToHom h) := by
  subst Y
  simpa using hf

private theorem family_congr
    {C : Type u} [SmallCategory C] (A : Cᵒᵖ ⥤ Type u)
    {Y Z : C} (R : Presieve Y) (x : R.FamilyOfElements A)
    (f g : Z ⟶ Y) (hf : R f) (hg : R g) (h : f = g) : x f hf = x g hg := by
  subst g
  rfl

private theorem family_transport
    {C : Type u} [SmallCategory C] (A : Cᵒᵖ ⥤ Type u)
    {Y Z Z' : C} (R : Presieve Y) (x : R.FamilyOfElements A)
    (f : Z ⟶ Y) (hf : R f) (h : Z' = Z) (hg : R (eqToHom h ≫ f)) :
    A.map (eqToHom h).op (x f hf) = x (eqToHom h ≫ f) hg := by
  subst Z'
  simp only [eqToHom_refl, op_id, Functor.map_id, types_id_apply]
  exact family_congr A R x f (𝟙 Z ≫ f) hf hg (Category.id_comp f).symm

private theorem cover_above
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (V : Cocone F) (Q : Precoverage V.pt)
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    (i : J) (Y : V.pt) (R : Presieve Y) (hR : R ∈ Q Y) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W), T ∈ P t.right W ∧
      ∃ hY : (V.ι.app t.right).toFunctor.obj W = Y,
        hY ▸ T.map (V.ι.app t.right).toFunctor = R := by
  obtain ⟨j, X, S, hX, hS, hR'⟩ := (hQ Y R).mp hR
  subst Y
  subst R
  let k := IsFiltered.max i j
  let b : j ⟶ k := IsFiltered.rightToMax i j
  let t : Under i := Under.mk (IsFiltered.leftToMax i j)
  let W := (F.map b).toFunctor.obj X
  let T := S.map (F.map b).toFunctor
  have hW : (V.ι.app t.right).toFunctor.obj W = (V.ι.app j).toFunctor.obj X :=
    congrArg (fun H : F.obj j ⟶ V.pt => H.toFunctor.obj X) (V.w b)
  refine ⟨t, W, T, hcover j k b X S hS, hW, ?_⟩
  exact transported_map_presieve (F.map b).toFunctor (V.ι.app k).toFunctor
    (V.ι.app j).toFunctor (congrArg Cat.Hom.toFunctor (V.w b)) S

/-- Finite covering families of generated sections have individual stage lifts.
Source: Stacks Project, Sites, Tag 0A35, the general-object presentation and
finite-cover paragraph; Modules on Sites, Tag 03CO, for abelian coefficients.
(blueprint: lem-weil-pbc-colimit-site-abelian-cover-section-lift).

Proof: Write the Q-cover R as the transported image of a stage cover using hQ.
Its stage presieve is finite by hfinite. Move that stage above i by filteredness,
transporting the cover by hcover. For each of its finitely many arrows, expand
membership of the corresponding section in the generated subgroup as a finite
additive expression in restrictions of stage images. Lift each restriction arrow
using the arrow colimit and align its endpoints using eventual equality in the
object colimit. Move the finitely many stages and endpoint equations to a common
stage above the cover. The transition of each inverse image is the transpose of
the direct unit under the preceding stage adjunction. Uniqueness of adjuncts and
h-alpha show that alpha after this transition equals the old alpha. Naturality
therefore gives a representative of every generating restriction. Add and negate
these representatives to lift the finite additive expressions. Further transitions
retain these image formulas by the same unit argument. Take the transported stage
cover. If different original arrows become equal, choose one lift for each actual
arrow of the transported presieve; their target sections are identical, since
both are the value of x on the same image arrow. Thus the choices still satisfy
the stated image equation. This gives a family of individual lifts, with no
compatibility conclusion. For an empty cover take its empty transported family;
there are no section choices or equations. No sheaf amalgamation is used.
-/
theorem colimit_site_abelian_cover_section_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
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
    (Y : V.pt) (R : Presieve Y) (hR : R ∈ Q Y)
    (x : R.FamilyOfElements
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u})) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W), T ∈ P t.right W ∧
      ∃ (hY : (V.ι.app t.right).toFunctor.obj W = Y)
        (hTR : ∀ {Z : F.obj t.right} (g : Z ⟶ W), T g →
          R ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY))
        (y : T.FamilyOfElements
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
              forget AddCommGrpCat.{u})),
        ∀ {Z : F.obj t.right} (g : Z ⟶ W) (hg : T g),
          (α t).hom.app (op Z) (y g hg) =
            (x ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hY) (hTR g hg)).val := by
  classical
  obtain ⟨t0, W0, T0, hT0, hY0, hR0⟩ := cover_above J F P hcover V Q hQ i Y R hR
  subst Y
  subst R
  have := hfinite t0.right W0 T0 hT0
  let Z (a : T0.uncurry) := a.val.1
  let f (a : T0.uncurry) : Z a ⟶ W0 := a.val.2
  let x0 (a : T0.uncurry) := x ((V.ι.app t0.right).toFunctor.map (f a))
    (Presieve.map_map a.property)
  obtain ⟨t, e, y0, hy0⟩ := colimit_site_abelian_finite_object_section_lift
    J F P V hobjects harrows Q i G α hα t0 Z x0
  let H := (F.map e.right).toFunctor
  let W := H.obj W0
  let T := T0.map H
  let hW : (V.ι.app t.right).toFunctor.obj W =
      (V.ι.app t0.right).toFunctor.obj W0 :=
    congrArg (fun K : F.obj t0.right ⟶ V.pt => K.toFunctor.obj W0) (V.w e.right)
  have hT : T ∈ P t.right W := hcover _ _ e.right W0 T0 hT0
  have hmap := congrArg Cat.Hom.toFunctor (V.w e.right)
  have hTR {Z' : F.obj t.right} (g : Z' ⟶ W) (hg : T g) :
      (T0.map (V.ι.app t0.right).toFunctor)
        ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hW) := by
    have heq := transported_map_presieve H (V.ι.app t.right).toFunctor
      (V.ι.app t0.right).toFunctor hmap T0
    have hm := Presieve.map_map hg (F := (V.ι.app t.right).toFunctor)
    exact heq ▸ transport_presieve_mem hW _ _ hm
  have hlift {Z' : F.obj t.right} (g : Z' ⟶ W) (hg : T g) :
      ∃ z : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op Z'),
        (α t).hom.app (op Z') z =
          (x ((V.ι.app t.right).toFunctor.map g ≫ eqToHom hW) (hTR g hg)).val := by
    obtain ⟨hg0⟩ := hg
    let a : T0.uncurry := ⟨⟨_, _⟩, hg0⟩
    refine ⟨y0 a, ?_⟩
    have ha := hy0 a
    let hZ : (V.ι.app t.right).toFunctor.obj (H.obj (Z a)) =
        (V.ι.app t0.right).toFunctor.obj (Z a) :=
      congrArg (fun K : F.obj t0.right ⟶ V.pt => K.toFunctor.obj (Z a)) (V.w e.right)
    have harrow : (V.ι.app t.right).toFunctor.map (H.map (f a)) ≫ eqToHom hW =
        eqToHom hZ ≫ (V.ι.app t0.right).toFunctor.map (f a) := by
      have hm := Functor.congr_hom hmap (f a)
      change (V.ι.app t.right).toFunctor.map (H.map (f a)) = _ at hm
      rw [hm]
      simp
    have hh := family_transport
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u})
      _ x ((V.ι.app t0.right).toFunctor.map (f a)) (Presieve.map_map a.property)
      hZ (by rw [← harrow]; exact hTR _ (Presieve.map_map hg0))
    have hhval := congrArg Subtype.val hh
    change (ColimitSiteStageImage.target F P V Q i G).obj.map (eqToHom hZ).op
      (x0 a).val = _ at hhval
    have hc := family_congr
      (ColimitSiteStageImage.presheaf F P V Q i G α ⋙ forget AddCommGrpCat.{u})
      _ x _ _ (by rw [← harrow]; exact hTR _ (Presieve.map_map hg0))
      (hTR _ (Presieve.map_map hg0)) harrow.symm
    exact ha.trans (hhval.trans (congrArg Subtype.val hc))
  choose y hy using @hlift
  exact ⟨t, W, T, hT, hW, @hTR, @y, @hy⟩

end CategoryTheory
