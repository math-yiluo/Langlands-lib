/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageRefinement
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionDiagram
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Simultaneous representatives at prescribed stage objects

Source: Stacks Project, Sites, Tag 0A35; Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem restriction_at_stage
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t0 t : Under i) (Z : F.obj t0.right) (T : F.obj t.right)
    (r : (V.ι.app t0.right).toFunctor.obj Z ⟶ (V.ι.app t.right).toFunctor.obj T) :
    ∃ (q : Under t0) (c : t ⟶ q.right)
      (f : (F.map q.hom.right).toFunctor.obj Z ⟶ (F.map c.right).toFunctor.obj T),
      Arrow.mk ((V.ι.app q.right.right).toFunctor.map f) = Arrow.mk r := by
  classical
  obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit harrows (Arrow.mk r)
  change Arrow (F.obj j) at a
  change Arrow.mk ((V.ι.app j).toFunctor.map a.hom) = Arrow.mk r at ha
  let s := IsFiltered.max t0 t
  let b0 := IsFiltered.leftToMax t0 t
  let b := IsFiltered.rightToMax t0 t
  let l := IsFiltered.max s.right j
  let d0 := IsFiltered.leftToMax s.right j
  let d1 := IsFiltered.rightToMax s.right j
  let s1 : Under i := Under.mk (s.hom ≫ d0)
  let v : s ⟶ s1 := Under.homMk d0 rfl
  let a' := (F.map d1).toFunctor.mapArrow.obj a
  let Z' := (F.map (b0 ≫ v).right).toFunctor.obj Z
  let T' := (F.map (b ≫ v).right).toFunctor.obj T
  have harr : Arrow.mk ((V.ι.app l).toFunctor.map a'.hom) = Arrow.mk r := by
    exact (congrArg (fun H ↦ H.mapArrow.obj a)
      (congrArg Cat.Hom.toFunctor (V.w d1))).trans ha
  have hsource : (Cat.objects.mapCocone V).ι.app l a'.left =
      (Cat.objects.mapCocone V).ι.app l Z' := by
    exact (congrArg Arrow.left harr).trans
      (congrArg (fun H ↦ H.obj Z)
        (congrArg Cat.Hom.toFunctor (V.w (b0 ≫ v).right))).symm
  obtain ⟨l1, d, hd⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hobjects a'.left Z').mp hsource
  change (F.map d).toFunctor.obj a'.left = (F.map d).toFunctor.obj Z' at hd
  have htarget : (Cat.objects.mapCocone V).ι.app l a'.right =
      (Cat.objects.mapCocone V).ι.app l T' := by
    exact (congrArg Arrow.right harr).trans
      (congrArg (fun H ↦ H.obj T)
        (congrArg Cat.Hom.toFunctor (V.w (b ≫ v).right))).symm
  have htarget1 : (Cat.objects.mapCocone V).ι.app l1
      ((F.map d).toFunctor.obj a'.right) =
      (Cat.objects.mapCocone V).ι.app l1 ((F.map d).toFunctor.obj T') := by
    exact (ConcreteCategory.congr_hom ((Cat.objects.mapCocone V).w d) a'.right).trans
      (htarget.trans (ConcreteCategory.congr_hom
        ((Cat.objects.mapCocone V).w d) T').symm)
  obtain ⟨l2, e, he⟩ := (Types.FilteredColimit.isColimit_eq_iff' hobjects
    ((F.map d).toFunctor.obj a'.right) ((F.map d).toFunctor.obj T')).mp htarget1
  change (F.map e).toFunctor.obj ((F.map d).toFunctor.obj a'.right) =
    (F.map e).toFunctor.obj ((F.map d).toFunctor.obj T') at he
  let s2 : Under i := Under.mk (s1.hom ≫ (d ≫ e))
  let v2 : s1 ⟶ s2 := Under.homMk (d ≫ e) rfl
  let q : Under t0 := Under.mk (b0 ≫ v ≫ v2)
  let c : t ⟶ q.right := b ≫ v ≫ v2
  have hs : (F.map (d ≫ e)).toFunctor.obj a'.left =
      (F.map q.hom.right).toFunctor.obj Z := by
    have hh := congrArg (F.map e).toFunctor.obj hd
    simpa [Z', q, v2, F.map_comp] using hh
  have ht : (F.map (d ≫ e)).toFunctor.obj a'.right =
      (F.map c.right).toFunctor.obj T := by
    simpa [T', c, v2, F.map_comp] using he
  let f := eqToHom hs.symm ≫ (F.map (d ≫ e)).toFunctor.map a'.hom ≫ eqToHom ht
  refine ⟨q, c, f, ?_⟩
  dsimp only [f]
  simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp,
    Arrow.arrow_mk_comp_eqToHom]
  exact (congrArg (fun H ↦ H.mapArrow.obj a')
    (congrArg Cat.Hom.toFunctor (V.w (d ≫ e)))).trans harr

private theorem one_section_lift
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
    (t0 : Under i) (Z : F.obj t0.right)
    (x : (ColimitSiteStageImage.presheaf F P V Q i G α).obj
      (op ((V.ι.app t0.right).toFunctor.obj Z))) :
    ∃ q : Under t0, ∀ (q' : Under t0) (_b : q ⟶ q'),
      ∃ y : ((sheafPullback (F.map q'.right.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P q'.right.right).toGrothendieck).obj G).obj.obj
          (op ((F.map q'.hom.right).toFunctor.obj Z)),
        ((α q'.right).hom.app (op ((F.map q'.hom.right).toFunctor.obj Z)) ≫
          eqToHom (congrArg (fun X =>
            (ColimitSiteStageImage.target F P V Q i G).obj.obj (op X))
            (congrArg (fun K : F.obj t0.right ⟶ V.pt => K.toFunctor.obj Z)
              (V.w q'.hom.right)))) y = x.val := by
  classical
  let H := ColimitSiteStageImage.target F P V Q i G
  let L (t : Under i) :=
    (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G
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
  have hcone (t t' : Under i) (b : t ⟶ t') (T : F.obj t.right) :
      Arrow.mk ((θ t t' b).hom.app (op T) ≫
        (α t').hom.app (op ((F.map b.right).toFunctor.obj T))) =
      Arrow.mk ((α t).hom.app (op T)) := by
    exact sheaf_triangle_comp (P i).toGrothendieck (P t.right).toGrothendieck
      (P t'.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (V.ι.app t'.right).toFunctor
      (F.map t'.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
      (by change (F.map t.hom ≫ F.map b.right).toFunctor = _
          rw [← F.map_comp, Under.w b])
      (congrArg Cat.Hom.toFunctor (V.w t'.hom))
      (congrArg Cat.Hom.toFunctor (V.w b.right)) G
      (θ t t' b) (α t') (α t) (hθ t t' b) (hα t') (hα t) T
  let W (q : Under t0) := (F.map q.hom.right).toFunctor.obj Z
  let A (q : Under t0) := (L q.right).obj.obj (op (W q))
  have hvo (q : Under t0) :
      (V.ι.app q.right.right).toFunctor.obj (W q) =
        (V.ι.app t0.right).toFunctor.obj Z :=
    congrArg (fun K : F.obj t0.right ⟶ V.pt => K.toFunctor.obj Z) (V.w q.hom.right)
  let k (q : Under t0) : A q ⟶ H.obj.obj (op ((V.ι.app t0.right).toFunctor.obj Z)) :=
    (α q.right).hom.app (op (W q)) ≫
      eqToHom (congrArg (fun X ↦ H.obj.obj (op X)) (hvo q))
  have ww (q q' : Under t0) (b : q ⟶ q') :
      (F.map q.hom.right).toFunctor ⋙ (F.map b.right.right).toFunctor =
        (F.map q'.hom.right).toFunctor := by
    change (F.map q.hom.right ≫ F.map b.right.right).toFunctor = _
    rw [← F.map_comp]
    exact congrArg (fun c : t0 ⟶ q'.right => (F.map c.right).toFunctor) (Under.w b)
  have hw (q q' : Under t0) (b : q ⟶ q') :
      (F.map b.right.right).toFunctor.obj (W q) = W q' :=
    congrArg (fun K ↦ K.obj Z) (ww q q' b)
  let m (q q' : Under t0) (b : q ⟶ q') : A q ⟶ A q' :=
    (θ q.right q'.right b.right).hom.app (op (W q)) ≫
      eqToHom (congrArg (fun X ↦ (L q'.right).obj.obj (op X)) (hw q q' b))
  have hmk (q q' : Under t0) (b : q ⟶ q') : m q q' b ≫ k q' = k q := by
    apply Arrow.mk_injective
    have hn := (α q'.right).hom.naturality (eqToHom (congrArg op (hw q q' b)))
    simp only [eqToHom_map] at hn
    dsimp only [m, k]
    rw [Category.assoc, ← Category.assoc (eqToHom _) _ _, hn]
    simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    exact hcone q.right q'.right b.right (W q)
  have hgen {z : H.obj.obj (op ((V.ι.app t0.right).toFunctor.obj Z))}
      (hz : z ∈ ColimitSiteStageImage.generators F P V Q i G α
        (op ((V.ι.app t0.right).toFunctor.obj Z))) :
      ∃ q : Under t0, ∃ y : A q, k q y = z := by
    rcases hz with ⟨t, T, r, y, rfl⟩
    obtain ⟨q, c, f, hf⟩ := restriction_at_stage J F V hobjects harrows i t0 t Z T r
    let z' := (θ t q.right c).hom.app (op T) y
    let y' : A q := (L q.right).obj.map f.op z'
    refine ⟨q, y', ?_⟩
    have hc := hcone t q.right c T
    have hn := NatTrans.naturality_apply (α q.right).hom f.op z'
    change (α q.right).hom.app (op (W q)) y' =
      H.obj.map ((V.ι.app q.right.right).toFunctor.map f).op
        ((α q.right).hom.app (op ((F.map c.right).toFunctor.obj T)) z') at hn
    dsimp only [k]
    rw [AddCommGrpCat.comp_apply, hn]
    have hmap : Arrow.mk (H.obj.map ((V.ι.app q.right.right).toFunctor.map f).op) =
        Arrow.mk (H.obj.map r.op) :=
      congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.obj.map a.hom.op)) hf
    have htotal : (θ t q.right c).hom.app (op T) ≫
        (α q.right).hom.app (op ((F.map c.right).toFunctor.obj T)) ≫
        H.obj.map ((V.ι.app q.right.right).toFunctor.map f).op ≫
        eqToHom (congrArg (fun X ↦ H.obj.obj (op X)) (hvo q)) =
        (α t).hom.app (op T) ≫ H.obj.map r.op := by
      apply Arrow.mk_injective
      rw [← Category.assoc, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
      exact arrow_comp_congr _ _ _ _ hc hmap
    exact ConcreteCategory.congr_hom htotal y
  have hmem : ∃ q : Under t0, ∃ y : A q, k q y = x.val := by
    have hx := x.property
    generalize x.val = xv at hx ⊢
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact hgen hz
    | zero => exact ⟨Under.mk (𝟙 t0), 0, map_zero _⟩
    | add z w _ _ hz hw =>
      obtain ⟨q, y, hy⟩ := hz
      obtain ⟨s, v, hv⟩ := hw
      let r := IsFiltered.max q s
      let b := IsFiltered.leftToMax q s
      let c := IsFiltered.rightToMax q s
      refine ⟨r, m q r b y + m s r c v, ?_⟩
      rw [map_add]
      exact congrArg₂ (fun a b ↦ a + b)
        ((ConcreteCategory.congr_hom (hmk q r b) y).trans hy)
        ((ConcreteCategory.congr_hom (hmk s r c) v).trans hv)
    | neg z _ hz =>
      obtain ⟨q, y, hy⟩ := hz
      exact ⟨q, -y, by rw [map_neg, hy]⟩
  obtain ⟨q, y, hy⟩ := hmem
  refine ⟨q, ?_⟩
  intro q' b
  exact ⟨m q q' b y, (ConcreteCategory.congr_hom (hmk q q' b) y).trans hy⟩

private theorem untransport_section
    {C : Type u} [SmallCategory C] (H : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    {X Y : C} (h : X = Y) (z : H.obj (op X)) (x : H.obj (op Y))
    (hz : eqToHom (congrArg (fun T ↦ H.obj (op T)) h) z = x) :
    z = H.map (eqToHom h).op x := by
  subst Y
  simpa using hz

/-- Finitely many generated sections over prescribed stage objects lift after one refinement.
Source: Stacks Project, Sites, Tag 0A35, general-object presentation and adjunction
paragraphs; Modules on Sites, Tag 03CO, for additive coefficients.
(blueprint: lem-weil-pbc-colimit-site-abelian-finite-object-section-lift).

Proof: Each section belongs to the additive subgroup generated by restrictions of
stage images. Induct on additive closure, or expand each section into a finite
sum of signed generators. For every generator choose its stage, its section and
its restriction arrow. There are finitely many such data across the finite index
set. The arrow colimit presents each restriction arrow at a stage. Filteredness
moves these stages, the source stage t0 and all section stages together. Eventual
equality in the object colimit aligns the endpoints of the lifted restrictions
with the transported prescribed objects and generator objects. Equalize the
finitely many paths out of i as well. These refinements provide a morphism in
Under i from t0 to the final stage.

For a morphism of stages, transpose the unit of the composite inverse image
under the earlier stage adjunction. This defines a map from the earlier inverse
image to the direct image of the later one. Its defining unit equation and the
componentwise h-alpha equation identify alpha after transition with the earlier
alpha, by injectivity of the adjunction hom equivalence. Naturality along the
lifted restriction arrow therefore turns each signed generator into the image
of a section over the forward image of its prescribed source. The source
transport is exactly the equality obtained by evaluating V.w on that object.
Add the lifted sections and negate as appropriate. Additivity of alpha and of
restriction gives the required equations for the original sections. Further
transitions preserve these equations by the same unit argument, so filteredness
puts the finite family at one final stage. For the empty index set take t = t0
and e = identity with the empty section family. For zero take the zero section.
No covering presieve, compatibility, or sheaf amalgamation is used.
-/
theorem colimit_site_abelian_finite_object_section_lift
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
    (t0 : Under i) {κ : Type u} [Finite κ] (Z : κ → F.obj t0.right)
    (x : ∀ k, (ColimitSiteStageImage.presheaf F P V Q i G α).obj
      (op ((V.ι.app t0.right).toFunctor.obj (Z k)))) :
    ∃ (t : Under i) (e : t0 ⟶ t)
      (y : ∀ k, ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map e.right).toFunctor.obj (Z k)))),
      ∀ k, (α t).hom.app (op ((F.map e.right).toFunctor.obj (Z k))) (y k) =
        (ColimitSiteStageImage.target F P V Q i G).obj.map
          (eqToHom (congrArg (fun H : F.obj t0.right ⟶ V.pt =>
            H.toFunctor.obj (Z k)) (V.w e.right))).op (x k).val := by
  classical
  have hlift (k : κ) := one_section_lift J F P V hobjects harrows Q i G α hα
    t0 (Z k) (x k)
  choose q hq using hlift
  let _ : Fintype κ := Fintype.ofFinite κ
  let O : Finset (Under t0) := Finset.univ.image q
  obtain ⟨s, hs⟩ := IsFiltered.sup_objs_exists O
  have hb (k : κ) : Nonempty (q k ⟶ s) := hs (by simp [O])
  let b (k : κ) : q k ⟶ s := (hb k).some
  have hy (k : κ) := hq k s (b k)
  choose y hy using hy
  refine ⟨s.right, s.hom, y, ?_⟩
  intro k
  have he := hy k
  rw [AddCommGrpCat.comp_apply] at he
  exact untransport_section (ColimitSiteStageImage.target F P V Q i G).obj
    _ _ _ he

end CategoryTheory
