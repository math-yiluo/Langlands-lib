/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImage
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteAbelianUnitKernelBound
import all WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageRefinement

/-! # One eventual matching equation

Source: Stacks Project, Sites, Tag 0A35, section formula and adjunction paragraphs.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- A unit-characterized comparison has the kernel of the second adjunction unit. -/
private theorem comparison_kernel_iff.{v}
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    [HasWeakSheafify S AddCommGrpCat.{max u v}]
    [HasWeakSheafify R AddCommGrpCat.{max u v}]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{max u v})
    (a : (sheafPullback f AddCommGrpCat.{max u v} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{max u v} S R).obj
        ((sheafPullback h AddCommGrpCat.{max u v} T R).obj G))
    (ha : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{max u v} T S).unit.app G).hom.app
        (op X) ≫ a.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{max u v} T R).unit.app G).hom.app
        (op X))) (Y : D)
    (x y : ((sheafPullback f AddCommGrpCat.{max u v} T S).obj G).obj.obj (op Y)) :
    a.hom.app (op Y) x = a.hom.app (op Y) y ↔
      ((sheafAdjunctionContinuous g AddCommGrpCat.{max u v} S R).unit.app
        ((sheafPullback f AddCommGrpCat.{max u v} T S).obj G)).hom.app (op Y) x =
      ((sheafAdjunctionContinuous g AddCommGrpCat.{max u v} S R).unit.app
        ((sheafPullback f AddCommGrpCat.{max u v} T S).obj G)).hom.app (op Y) y := by
  subst h
  let L := sheafPullback f AddCommGrpCat.{max u v} T S
  let Rf := f.sheafPushforwardContinuous AddCommGrpCat.{max u v} T S
  let Rg := g.sheafPushforwardContinuous AddCommGrpCat.{max u v} S R
  let A := sheafAdjunctionContinuous f AddCommGrpCat.{max u v} T S
  let B := sheafAdjunctionContinuous g AddCommGrpCat.{max u v} S R
  let H := sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{max u v} T R
  let e := (A.comp B).leftAdjointUniq H
  let b := B.unit.app (L.obj G) ≫ Rg.map (e.hom.app G)
  have hab : a = b := by
    apply (A.homEquiv G _).injective
    rw [A.homEquiv_unit]
    have he := (A.comp B).unit_leftAdjointUniq_hom_app H G
    rw [A.comp_unit_app B G] at he
    change A.unit.app G ≫ Rf.map (B.unit.app (L.obj G)) ≫
      Rf.map (Rg.map (e.hom.app G)) = H.unit.app G at he
    rw [← Rf.map_comp] at he
    change A.unit.app G ≫ Rf.map a = A.unit.app G ≫ Rf.map b
    rw [he]
    ext1
    apply NatTrans.ext
    funext X
    exact (Arrow.mk_inj _ _).mp (ha (unop X))
  rw [hab]
  change (e.hom.app G).hom.app (op (g.obj Y))
      ((B.unit.app (L.obj G)).hom.app (op Y) x) =
    (e.hom.app G).hom.app (op (g.obj Y))
      ((B.unit.app (L.obj G)).hom.app (op Y) y) ↔ _
  exact (ConcreteCategory.bijective_of_isIso
    ((e.hom.app G).hom.app (op (g.obj Y)))).1.eq_iff


/-- Composition of continuous inverse images enlarges the source-unit kernel. -/
private theorem unit_kernel_mono
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u}) (X : C) :
    (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
      (op X)).hom.ker ≤
    (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
      (op X)).hom.ker := by
  subst h
  obtain ⟨a, ha⟩ := exists_transition T S R f g (f ⋙ g) rfl G
  intro z hz
  have he := (Arrow.mk_inj _ _).mp (ha X)
  have hez := ConcreteCategory.congr_hom he z
  change a.hom.app (op (f.obj X))
    (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
      (op X) z) = _ at hez
  change (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
    (op X)) z = 0 at hz
  change (((sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R).unit.app G).hom.app
    (op X)) z = 0
  rw [hz, map_zero] at hez
  exact hez.symm

/-- One pair of restrictions with matching colimit images agrees at a later stage.
Source: Stacks Project, Sites, Tag 0A35, section formula and finite-cover equalizer
and adjunction paragraphs; Modules on Sites, Tag 03CO, abelian interpretation.
(blueprint: lem-weil-pbc-colimit-site-abelian-pairwise-eventual-matching)

Proof: Put A = F(t.hom) inverse image of G and let x and z be the two restrictions
along gs and gr. Compatibility hy and naturality of alpha imply alpha_t(x) =
alpha_t(z). The composite adjunction for F(t.hom) and V_t and the direct V_i
adjunction have the same right adjoint. Their unique left-adjoint isomorphism,
compatible with their units, identifies alpha_t with the V_t unit on A followed
by that isomorphism. Each component of the isomorphism is injective. Thus the
V_t unit kills x - z in A(Z).

Use the section formula of Tag 0A35 for the source stage t.right, sheaf A, and
object Z: the sections of V_t inverse image of A at V_t(Z) are the filtered
colimit of sections of the later inverse images at the images of Z. The formula
is proved independently by constructing the presheaf of filtered section
colimits over presentations of each colimit-site object. The object and arrow
set colimits lift finite object, arrow, and relation data to a common stage and
make presentation refinements filtered and the refinements of any presentation
final. Restriction maps are induced by those lifts and independent of lifts by
eventual equality. Every covering family is the image of a finite stage cover;
preserved covering pullbacks and commutation of filtered abelian colimits with
finite limits give the sheaf equalizer, also for an empty cover. Transposing maps
out of this sheaf through the stage adjunctions identifies it with V_t inverse
image of A, compatibly with the source unit. This is a raw section-colimit
construction, not the already assembled stage-image sheaf that needs the present
finite-family stabilization theorem.

In this filtered colimit the representative x - z from the identity stage equals
zero. Equality of representatives is witnessed by a transition d : t.right to k;
unit compatibility says that the d adjunction unit kills x - z. Take t' to be
Under.mk(t.hom followed by d) and b its morphism with right component d. Apply
left-adjoint uniqueness once more to F(t.hom), F(d), and F(t'.hom): htheta
identifies the kernel of theta_b with that of the d unit. Therefore theta_b(x)
equals theta_b(z). This concerns one prescribed pair and one prescribed test
object only. It supplies neither a simultaneous transition for all pairs nor
compatibility at every object of a later stage nor descent to an image presieve.
-/
theorem colimit_site_abelian_pairwise_eventual_matching
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
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶
      ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G))
    (hα : ∀ (t : Under i) (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ (α t).hom.app
        (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)))
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)))
    (t : Under i) (W : F.obj t.right) (T : Presieve W) (hT : T ∈ P t.right W)
    (y : T.FamilyOfElements
      (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⋙
          forget AddCommGrpCat.{u}))
    (hy : (show T.FamilyOfElements
        ((V.ι.app t.right).toFunctor.op ⋙
          (ColimitSiteStageImage.target F P V Q i G).obj ⋙ forget AddCommGrpCat.{u}) from
        fun {Z} g hg ↦ (α t).hom.app (op Z) (y g hg)).Compatible)
    (Z : F.obj t.right) (s r : T.uncurry)
    (gs : Z ⟶ s.val.1) (gr : Z ⟶ r.val.1)
    (heq : gs ≫ s.val.2 = gr ≫ r.val.2) :
    ∃ (t' : Under i) (b : t ⟶ t'),
      (θ t t' b).hom.app (op Z)
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.map gs.op
              (y s.val.2 s.property)) =
        (θ t t' b).hom.app (op Z)
          (((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
            (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.map gr.op
              (y r.val.2 r.property)) := by
  classical
  have _hcover : T ∈ P t.right W := hT
  let H := (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck (P t.right).toGrothendieck).obj G
  let x := H.obj.map gs.op (y s.val.2 s.property)
  let z := H.obj.map gr.op (y r.val.2 r.property)
  have hxy : (α t).hom.app (op Z) x = (α t).hom.app (op Z) z := by
    have he := hy gs gr s.property r.property heq
    have hs := ConcreteCategory.congr_hom ((α t).hom.naturality gs.op)
      (y s.val.2 s.property)
    have hr := ConcreteCategory.congr_hom ((α t).hom.naturality gr.op)
      (y r.val.2 r.property)
    exact hs.trans (he.trans hr.symm)
  have hv := comparison_kernel_iff (P i).toGrothendieck (P t.right).toGrothendieck
    Q.toGrothendieck (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor
    (V.ι.app i).toFunctor (congrArg Cat.Hom.toFunctor (V.w t.hom))
    G (α t) (hα t) Z x z
  have hz : ((sheafAdjunctionContinuous (V.ι.app t.right).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck Q.toGrothendieck).unit.app H).hom.app (op Z)
        (x - z) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hv.mp hxy
  let K (a : Under t.right) : AddSubgroup (H.obj.obj (op Z)) :=
    (((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app
        (op Z)).hom.ker
  have hmono {a a' : Under t.right} (b : a ⟶ a') : K a ≤ K a' := by
    apply unit_kernel_mono (P t.right).toGrothendieck (P a.right).toGrothendieck
      (P a'.right).toGrothendieck (F.map a.hom).toFunctor (F.map b.right).toFunctor
      (F.map a'.hom).toFunctor _ H Z
    change (F.map a.hom ≫ F.map b.right).toFunctor = _
    rw [← F.map_comp, Under.w b]
  have : Nonempty (Under t.right) := ⟨Under.mk (𝟙 t.right)⟩
  have hdir : Directed (· ≤ ·) K := by
    intro a a'
    exact ⟨IsFiltered.max a a', hmono (IsFiltered.leftToMax a a'),
      hmono (IsFiltered.rightToMax a a')⟩
  have hmem : x - z ∈ ⨆ a, K a :=
    colimit_site_abelian_unit_kernel_bound
      J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
      t.right H Z hz
  obtain ⟨a, ha⟩ := (AddSubgroup.mem_iSup_of_directed hdir).mp hmem
  let t' : Under i := Under.mk (t.hom ≫ a.hom)
  let b : t ⟶ t' := Under.homMk a.hom
  refine ⟨t', b, ?_⟩
  apply (comparison_kernel_iff (P i).toGrothendieck (P t.right).toGrothendieck
    (P t'.right).toGrothendieck (F.map t.hom).toFunctor (F.map b.right).toFunctor
    (F.map t'.hom).toFunctor (by
      change (F.map t.hom ≫ F.map b.right).toFunctor = _
      rw [← F.map_comp, Under.w b]) G (θ t t' b) (hθ t t' b) Z x z).mpr
  change ((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
    (P t.right).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app (op Z)
      x =
    ((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
      (P t.right).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app (op Z)
      z
  change ((sheafAdjunctionContinuous (F.map a.hom).toFunctor AddCommGrpCat.{u}
    (P t.right).toGrothendieck (P a.right).toGrothendieck).unit.app H).hom.app (op Z)
      (x - z) = 0 at ha
  simpa only [map_sub, sub_eq_zero] using ha

end CategoryTheory
