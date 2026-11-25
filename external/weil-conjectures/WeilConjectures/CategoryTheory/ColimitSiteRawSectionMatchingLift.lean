/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.CategoryTheory.ColimitSiteRawFiniteSectionsLift
import WeilConjectures.CategoryTheory.ColimitSiteRawFiniteMatchingRefinement

/-! # Matching lifts of raw sections

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-matching-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem image_cover_eq
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (L : C ⥤ D) (M : D ⥤ E) (N : C ⥤ E) (h : L ⋙ M = N)
    {X : C} (R : Presieve X) (e : M.obj (L.obj X) = N.obj X) :
    Presieve.ofArrows
      (fun p : (R.map L).uncurry ↦ M.obj p.val.1)
      (fun p ↦ M.map p.val.2 ≫ eqToHom e) = R.map N := by
  subst N
  have he : e = rfl := Subsingleton.elim _ _
  rw [he]
  simp only [eqToHom_refl, Category.comp_id]
  apply le_antisymm
  · rintro Y f ⟨p⟩
    obtain ⟨⟨Z, g⟩, hg⟩ := p
    cases hg with
    | of hg => exact ⟨hg⟩
  · rintro Y f ⟨hf⟩
    exact Presieve.ofArrows.mk (⟨⟨_, L.map _⟩, .of hf⟩ : (R.map L).uncurry)

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the finite-cover equalizer calculation, before applying the stage sheaf condition.
(blueprint: lem-weil-pbc-colimit-site-raw-section-matching-lift).

Proof: Compute each left Kan extension pointwise. Its generators are sections of a
stage inverse image together with an arrow from the evaluation object to a stage image.
The object and arrow set-colimits let us lift that arrow and its endpoints to a common
stage; restrict the section along the lifted arrow. A finite chain of Kan relations
can likewise be lifted to a later stage. Naturality of beta and h-beta-map turn its
relations into restriction and theta transport. The equation h-theta identifies theta
with the unique adjunction transpose of the unit, so these transports compose.
Consequently every raw section has a stage representative and every equality of raw
representatives holds after further refinement.

Index the original cover by R.uncurry. Its finiteness allows us to lift all its local
sections simultaneously to a stage receiving i and j. Transport the original cover
there; hcover makes it covering. For each pair of covering arrows, hx gives equality
on their pullback in the limit category. Covering pullbacks exist at the stage, and
hpullback and hVpullback identify their images with these limit pullbacks. Apply the
raw equality criterion to the finitely many resulting equations and refine once more
so all hold. The pullback universal property then gives compatibility on every common
test object. The resulting family y has the prescribed beta/colimit images by
naturality and h-beta-map. The cocone equation identifies the transported target W
with the original image target; its equality is e. The transported covering arrows,
indexed by T.uncurry, give exactly the original image presieve, including duplicates,
which is hT. If R is empty, use its transported empty cover and the empty family:
there are no sections or equations to lift. No amalgamation or uniqueness is asserted
and no arbitrary existential witness is used to define data.
-/
theorem colimit_site_raw_section_matching_lift
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
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (j : J) (X : F.obj j) (R : Presieve X) (hR : R ∈ P j X)
    (x : (R.map (V.ι.app j).toFunctor).FamilyOfElements (colimit B))
    (hx : x.Compatible) :
    ∃ (t : Under i) (W : F.obj t.right) (T : Presieve W) (hcoverT : T ∈ P t.right W)
      (e : (V.ι.app t.right).toFunctor.obj W = (V.ι.app j).toFunctor.obj X)
      (hT : Presieve.ofArrows
        (fun p : T.uncurry ↦ (V.ι.app t.right).toFunctor.obj p.val.1)
        (fun p ↦ (V.ι.app t.right).toFunctor.map p.val.2 ≫ eqToHom e) =
          R.map (V.ι.app j).toFunctor)
      (y : T.FamilyOfElements
        ((sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj),
      y.Compatible ∧ ∀ p : T.uncurry,
        (colimit.ι B t).app (op ((V.ι.app t.right).toFunctor.obj p.val.1))
          ((β t).app (op p.val.1) (y p.val.2 p.property)) =
        x ((V.ι.app t.right).toFunctor.map p.val.2 ≫ eqToHom e)
          (hT ▸ Presieve.ofArrows.mk p) := by
  classical
  let I := R.uncurry
  have : Finite I := hfinite j X R hR
  let Y : I → F.obj j := fun p ↦ p.val.1
  let f : ∀ p : I, Y p ⟶ X := fun p ↦ p.val.2
  have hf (p : I) : R (f p) := p.property
  have hRindex : Presieve.ofArrows Y f = R := by
    apply le_antisymm
    · rintro Z g ⟨p⟩
      exact hf p
    · intro Z g hg
      exact Presieve.ofArrows.mk (⟨⟨Z, g⟩, hg⟩ : I)
  obtain ⟨t, a, e, s, hs⟩ := colimit_site_raw_finite_sections_lift
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap j I Y
    (fun p ↦ x ((V.ι.app j).toFunctor.map (f p)) (.of (hf p)))
  let L := (F.map a).toFunctor
  let M := (V.ι.app t.right).toFunctor
  let N := (V.ι.app j).toFunctor
  have hw : L ⋙ M = N := congrArg Cat.Hom.toFunctor (V.w a)
  have hm (p : I) : M.map (L.map (f p)) ≫ eqToHom (e X) =
      eqToHom (e (Y p)) ≫ N.map (f p) := by
    simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
      using congrArg (fun g ↦ g ≫ eqToHom (e X)) (Functor.congr_hom hw (f p))
  have hc : Presieve.Arrows.Compatible (M.op ⋙ colimit B)
      (fun p ↦ L.map (f p))
      (fun p ↦ (colimit.ι B t).app (op (M.obj (L.obj (Y p))))
        ((β t).app (op (L.obj (Y p))) (s p))) := by
    intro p q Z gp gq heq
    change (colimit B).map (M.map gp).op _ = (colimit B).map (M.map gq).op _
    dsimp only
    rw [hs p, hs q]
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    apply hx (M.map gp ≫ eqToHom (e (Y p)))
      (M.map gq ≫ eqToHom (e (Y q))) (.of (hf p)) (.of (hf q))
    calc
      _ = M.map (gp ≫ L.map (f p)) ≫ eqToHom (e X) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hm p]
      _ = M.map (gq ≫ L.map (f q)) ≫ eqToHom (e X) := by rw [heq]
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hm q]
  have hcov : Presieve.ofArrows (fun p ↦ L.obj (Y p))
      (fun p ↦ L.map (f p)) ∈ P t.right (L.obj X) := by
    rw [← Presieve.map_ofArrows, hRindex]
    exact hcover j t.right a X R hR
  obtain ⟨t', b, e', s', hc', hs'⟩ := colimit_site_raw_finite_matching_refinement
    J F P hcover hpullback V hobjects harrows Q i G θ hθ B β hβ
    hβmap t (L.obj X) I (fun p ↦ L.obj (Y p)) (fun p ↦ L.map (f p)) hcov s hc
  let L' := (F.map b.right).toFunctor
  let M' := (V.ι.app t'.right).toFunctor
  let T := Presieve.ofArrows (fun p ↦ L'.obj (L.obj (Y p)))
    (fun p ↦ L'.map (L.map (f p)))
  have hcov' : T ∈ P t'.right (L'.obj (L.obj X)) := by
    dsimp [T]
    rw [← Presieve.map_ofArrows]
    exact hcover t.right t'.right b.right (L.obj X) _ hcov
  let E (U : F.obj j) := (e' (L.obj U)).trans (e U)
  have hw' : (L ⋙ L') ⋙ M' = N := by
    rw [Functor.assoc, show L' ⋙ M' = M from
      congrArg Cat.Hom.toFunctor (V.w b.right)]
    exact hw
  have hT : Presieve.ofArrows
      (fun p : T.uncurry ↦ M'.obj p.val.1)
      (fun p ↦ M'.map p.val.2 ≫ eqToHom (E X)) = R.map N := by
    have hTR : T = R.map (L ⋙ L') := by
      dsimp [T]
      change Presieve.ofArrows (fun p ↦ (L ⋙ L').obj (Y p))
        (fun p ↦ (L ⋙ L').map (f p)) = _
      rw [← Presieve.map_ofArrows, hRindex]
    rw [hTR]
    exact image_cover_eq (L ⋙ L') M' N hw' R (E X)
  let y : T.FamilyOfElements
      ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj :=
    hc'.familyOfElements
  refine ⟨t', L'.obj (L.obj X), T, hcov', E X, hT, y,
    hc'.familyOfElements_compatible, ?_⟩
  intro p
  obtain ⟨⟨Z, g⟩, hg⟩ := p
  cases hg with
  | mk q =>
    rw [show y _ _ = s' q from hc'.familyOfElements_ofArrows_mk q, hs' q, hs q]
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans]
    have hm' : M'.map (L'.map (L.map (f q))) ≫ eqToHom (E X) =
        eqToHom (E (Y q)) ≫ N.map (f q) := by
      simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id]
        using congrArg (fun g ↦ g ≫ eqToHom (E X)) (Functor.congr_hom hw' (f q))
    have hxc := hx (𝟙 (M'.obj (L'.obj (L.obj (Y q))))) (eqToHom (E (Y q)))
      (hT ▸ Presieve.ofArrows.mk
        (⟨⟨_, L'.map (L.map (f q))⟩, Presieve.ofArrows.mk q⟩ : T.uncurry))
      (.of (hf q)) (by simpa only [Category.id_comp] using hm')
    simpa only [op_id, Functor.map_id, CategoryTheory.ConcreteCategory.id_apply] using hxc.symm

end CategoryTheory
