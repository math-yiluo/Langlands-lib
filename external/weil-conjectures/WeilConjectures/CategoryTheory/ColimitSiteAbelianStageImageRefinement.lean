/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionDiagram
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Stage-image descent on a filtered colimit of sites

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem arrow_comp_congr {C : Type*} [Category C]
    {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hZ, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  subst hX
  subst hY
  subst hZ
  simpa using congrArg Arrow.mk (congrArg₂ (fun f g ↦ f ≫ g) hf hg)

private theorem exists_transition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D) (R : GrothendieckTopology E)
    (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u}) :
    ∃ θ : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
        (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
          ((sheafPullback h AddCommGrpCat.{u} T R).obj G),
      ∀ X : C,
        Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
          (op X) ≫ θ.hom.app (op (f.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
          (op X)) := by
  subst h
  let H := (sheafPullback (f ⋙ g) AddCommGrpCat.{u} T R).obj G
  let η : G ⟶ (f.sheafPushforwardContinuous AddCommGrpCat.{u} T S).obj
      ((g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj H) :=
    ⟨((sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R).unit.app G).hom⟩
  let adj := sheafAdjunctionContinuous f AddCommGrpCat.{u} T S
  refine ⟨(adj.homEquiv G _).symm η, ?_⟩
  intro X
  have he := (adj.homEquiv G _).apply_symm_apply η
  rw [adj.homEquiv_unit] at he
  exact congrArg (fun a ↦ Arrow.mk (a.hom.app (op X))) he

/-- Finite additive expressions in stage images refine to a single forward stage.
Source: Stacks Project, Sites, Tag 0A35, independence of presentations and the
restriction construction, together with Tag 04AX on filtered category colimits.
(blueprint: lem-weil-pbc-colimit-site-abelian-stage-image-refinement).

Proof: First consider a generator: a section at W of the pullback along i to j,
restricted by r : V i U to V j W. Represent r in the arrow colimit. Move its
representative and j to a common stage. Eventual equality in the object
colimit aligns its source with the image of U along i to j to that stage, and
then its target with the image of W. Compose with the two endpoint transports.
Cocone naturality shows that the resulting stage arrow maps exactly to r.
Use the composite arrow out of i as the new forward presentation.
Transpose the adjunction unit to obtain the transition map between the stage
pullbacks. Its composite with alpha is the original alpha by h-alpha and
uniqueness of adjuncts. Naturality at the lifted restriction arrow then shows
that restricting the transitioned section gives a forward representative of
the generator. Negative representatives are obtained by negation. For a sum,
move the two forward stages to a common object of Under i, use the same
unit-characterized transition maps and add the two sections there. Zero is
represented by zero at the identity object of Under i. AddSubgroup closure
induction now handles every finite additive expression. Cocone naturality
identifies the target objects; HEq expresses the induced element transport.
No finite-cover, pullback-preservation, or sheaf gluing hypothesis is used.
-/
theorem colimit_site_abelian_stage_image_refinement
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
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
    (U : F.obj i)
    (x : ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
        (op ((V.ι.app i).toFunctor.obj U)))
    (hx : x ∈ ColimitSiteStageImage.subgroup F P V Q i G α
      (op ((V.ι.app i).toFunctor.obj U))) :
    ∃ (t : Under i)
      (y : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U))),
      HEq ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) x := by
  classical
  let H := ColimitSiteStageImage.target F P V Q i G
  let W (t : Under i) := (F.map t.hom).toFunctor.obj U
  let A (t : Under i) :=
    ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op (W t))
  let θ (t t' : Under i) (b : t ⟶ t') :=
    (exists_transition (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck (F.map t.hom).toFunctor
      (F.map b.right).toFunctor (F.map t'.hom).toFunctor
      (by change (F.map t.hom ≫ F.map b.right).toFunctor = _
          rw [← F.map_comp, Under.w b]) G).choose
  have hθ (t t' : Under i) (b : t ⟶ t') :=
    (exists_transition (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck (F.map t.hom).toFunctor
      (F.map b.right).toFunctor (F.map t'.hom).toFunctor
      (by change (F.map t.hom ≫ F.map b.right).toFunctor = _
          rw [← F.map_comp, Under.w b]) G).choose_spec
  have hvo (t : Under i) :
      (V.ι.app t.right).toFunctor.obj (W t) = (V.ι.app i).toFunctor.obj U :=
    congrArg (fun f ↦ f.obj U) (congrArg Cat.Hom.toFunctor (V.w t.hom))
  let k (t : Under i) : A t ⟶ H.obj.obj (op ((V.ι.app i).toFunctor.obj U)) :=
    (α t).hom.app (op (W t)) ≫
      eqToHom (congrArg (fun Y ↦ H.obj.obj (op Y)) (hvo t))
  have hk (t t' : Under i) (b : t ⟶ t') :
      Arrow.mk ((θ t t' b).hom.app (op (W t)) ≫
        (α t').hom.app (op ((F.map b.right).toFunctor.obj (W t)))) =
      Arrow.mk ((α t).hom.app (op (W t))) := by
    apply sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (V.ι.app t'.right).toFunctor
      (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
      (by change (F.map t.hom ≫ F.map b.right).toFunctor = _
          rw [← F.map_comp, Under.w b])
      (congrArg Cat.Hom.toFunctor (V.w t'.hom))
      (congrArg Cat.Hom.toFunctor (V.w b.right)) G
      (θ t t' b) (α t') (α t) (hθ t t' b) (hα t') (hα t) (W t)
  let m (t t' : Under i) (b : t ⟶ t') : A t ⟶ A t' :=
    (θ t t' b).hom.app (op (W t)) ≫
      eqToHom (congrArg (fun Y ↦
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj (op Y))
        (congrArg (fun f ↦ f.obj U)
          (show (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
            (F.map t'.hom).toFunctor from
              by change (F.map t.hom ≫ F.map b.right).toFunctor = _
                 rw [← F.map_comp, Under.w b])))
  have hmk (t t' : Under i) (b : t ⟶ t') : m t t' b ≫ k t' = k t := by
    apply Arrow.mk_injective
    have hn := (α t').hom.naturality
      (eqToHom (congrArg op (congrArg (fun f ↦ f.obj U)
        (show (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
          (F.map t'.hom).toFunctor from
            by change (F.map t.hom ≫ F.map b.right).toFunctor = _
               rw [← F.map_comp, Under.w b]))))
    simp only [eqToHom_map] at hn
    dsimp only [m, k]
    rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
    simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    exact hk t t' b
  -- Lift one generating restriction arrow, retaining its forward source presentation.
  have hgen {z : H.obj.obj (op ((V.ι.app i).toFunctor.obj U))}
      (hz : z ∈ ColimitSiteStageImage.generators F P V Q i G α
        (op ((V.ι.app i).toFunctor.obj U))) :
      ∃ t : Under i, ∃ y : A t, k t y = z := by
    rcases hz with ⟨t, T, r, y, rfl⟩
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit harrows (Arrow.mk r)
    change Arrow (F.obj j) at a
    change Arrow.mk ((V.ι.app j).toFunctor.map a.hom) = Arrow.mk r at ha
    let l := IsFiltered.max t.right j
    let b := IsFiltered.leftToMax t.right j
    let c := IsFiltered.rightToMax t.right j
    let a' := (F.map c).toFunctor.mapArrow.obj a
    let U' := (F.map (t.hom ≫ b)).toFunctor.obj U
    let T' := (F.map b).toFunctor.obj T
    have harr : Arrow.mk ((V.ι.app l).toFunctor.map a'.hom) = Arrow.mk r := by
      exact (congrArg (fun f ↦ f.mapArrow.obj a)
        (congrArg Cat.Hom.toFunctor (V.w c))).trans ha
    have hsource : (Cat.objects.mapCocone V).ι.app l a'.left =
        (Cat.objects.mapCocone V).ι.app l U' := by
      exact (congrArg Arrow.left harr).trans
        (congrArg (fun f ↦ f.obj U)
          (congrArg Cat.Hom.toFunctor (V.w (t.hom ≫ b)))).symm
    obtain ⟨l₁, d, hd⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hobjects a'.left U').mp hsource
    change (F.map d).toFunctor.obj a'.left = (F.map d).toFunctor.obj U' at hd
    have htarget : (Cat.objects.mapCocone V).ι.app l a'.right =
        (Cat.objects.mapCocone V).ι.app l T' := by
      exact (congrArg Arrow.right harr).trans
        (congrArg (fun f ↦ f.obj T)
          (congrArg Cat.Hom.toFunctor (V.w b))).symm
    have htarget₁ : (Cat.objects.mapCocone V).ι.app l₁
        ((F.map d).toFunctor.obj a'.right) =
      (Cat.objects.mapCocone V).ι.app l₁ ((F.map d).toFunctor.obj T') := by
      exact (ConcreteCategory.congr_hom ((Cat.objects.mapCocone V).w d) a'.right).trans
        (htarget.trans (ConcreteCategory.congr_hom
          ((Cat.objects.mapCocone V).w d) T').symm)
    obtain ⟨l₂, e, he⟩ := (Types.FilteredColimit.isColimit_eq_iff' hobjects
      ((F.map d).toFunctor.obj a'.right) ((F.map d).toFunctor.obj T')).mp htarget₁
    change (F.map e).toFunctor.obj ((F.map d).toFunctor.obj a'.right) =
      (F.map e).toFunctor.obj ((F.map d).toFunctor.obj T') at he
    let b' := b ≫ d ≫ e
    let t' : Under i := Under.mk (t.hom ≫ b')
    let q : t ⟶ t' := Under.homMk b' rfl
    have hs : (F.map (d ≫ e)).toFunctor.obj a'.left = W t' := by
      have hh := congrArg (F.map e).toFunctor.obj hd
      simpa [U', W, t', b', F.map_comp] using hh
    have ht : (F.map (d ≫ e)).toFunctor.obj a'.right =
        (F.map b').toFunctor.obj T := by
      simpa [T', b', F.map_comp] using he
    let f : W t' ⟶ (F.map b').toFunctor.obj T :=
      eqToHom hs.symm ≫ (F.map (d ≫ e)).toFunctor.map a'.hom ≫ eqToHom ht
    have hf : Arrow.mk ((V.ι.app l₂).toFunctor.map f) = Arrow.mk r := by
      dsimp only [f]
      simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp,
        Arrow.arrow_mk_comp_eqToHom]
      exact (congrArg (fun g ↦ g.mapArrow.obj a')
        (congrArg Cat.Hom.toFunctor (V.w (d ≫ e)))).trans harr
    let z' := (θ t t' q).hom.app (op T) y
    let y' : A t' :=
      ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map f.op z'
    refine ⟨t', y', ?_⟩
    have : (F.map b').toFunctor.IsContinuous
        (P t.right).toGrothendieck (P t'.right).toGrothendieck :=
      inferInstanceAs ((F.map b').toFunctor.IsContinuous
        (P t.right).toGrothendieck (P l₂).toGrothendieck)
    have hcone : Arrow.mk ((θ t t' q).hom.app (op T) ≫
        (α t').hom.app (op ((F.map b').toFunctor.obj T))) =
        Arrow.mk ((α t).hom.app (op T)) := by
      exact sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
        (P t'.right).toGrothendieck Q.toGrothendieck
        (F.map t.hom).toFunctor (F.map b').toFunctor (V.ι.app t'.right).toFunctor
        (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
        (by change (F.map t.hom ≫ F.map b').toFunctor = _
            rw [← F.map_comp]; rfl)
        (congrArg Cat.Hom.toFunctor (V.w t'.hom))
        (congrArg Cat.Hom.toFunctor (V.w b')) G
        (θ t t' q) (α t') (α t) (hθ t t' q) (hα t') (hα t) T
    have hn := NatTrans.naturality_apply (α t').hom f.op z'
    change (α t').hom.app (op (W t')) y' =
      H.obj.map ((V.ι.app t'.right).toFunctor.map f).op
        ((α t').hom.app (op ((F.map b').toFunctor.obj T)) z') at hn
    dsimp only [k]
    rw [AddCommGrpCat.comp_apply, hn]
    have hmap : Arrow.mk (H.obj.map ((V.ι.app t'.right).toFunctor.map f).op) =
        Arrow.mk (H.obj.map r.op) := by
      exact congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.obj.map a.hom.op)) hf
    have htotal : (θ t t' q).hom.app (op T) ≫
        (α t').hom.app (op ((F.map b').toFunctor.obj T)) ≫
        H.obj.map ((V.ι.app t'.right).toFunctor.map f).op ≫
        eqToHom (congrArg (fun Y ↦ H.obj.obj (op Y)) (hvo t')) =
        (α t).hom.app (op T) ≫ H.obj.map r.op := by
      apply Arrow.mk_injective
      rw [← Category.assoc, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      exact arrow_comp_congr _ _ _ _ hcone hmap
    exact ConcreteCategory.congr_hom htotal y
  -- Filteredness turns a finite additive expression into one representative.
  have hmem : ∃ t : Under i, ∃ y : A t, k t y = x := by
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact hgen hz
    | zero => exact ⟨Under.mk (𝟙 i), 0, map_zero _⟩
    | add z w _ _ hz hw =>
      obtain ⟨t, y, hy⟩ := hz
      obtain ⟨s, v, hv⟩ := hw
      let r := IsFiltered.max t s
      let b := IsFiltered.leftToMax t s
      let c := IsFiltered.rightToMax t s
      refine ⟨r, m t r b y + m s r c v, ?_⟩
      rw [map_add]
      exact congrArg₂ (fun a b ↦ a + b)
        ((ConcreteCategory.congr_hom (hmk t r b) y).trans hy)
        ((ConcreteCategory.congr_hom (hmk s r c) v).trans hv)
    | neg z _ hz =>
      obtain ⟨t, y, hy⟩ := hz
      exact ⟨t, -y, by rw [map_neg, hy]⟩
  obtain ⟨t, y, hy⟩ := hmem
  refine ⟨t, y, ?_⟩
  have he : HEq (k t y) ((α t).hom.app (op (W t)) y) := by
    have hh {B C : AddCommGrpCat.{u}} (h : B = C) (z : B) :
        HEq (eqToHom h z) z := by
      subst C
      rfl
    exact hh _ _
  exact he.symm.trans (heq_of_eq hy)

end CategoryTheory
