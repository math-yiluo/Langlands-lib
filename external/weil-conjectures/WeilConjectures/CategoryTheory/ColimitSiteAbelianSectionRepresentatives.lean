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
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageSheaf
import WeilConjectures.CategoryTheory.ColimitSiteAbelianStageImageRefinement

/-! # Stage representatives of abelian inverse-image sections

Source: Stacks Project, Sites, Tag 0A35, and Modules on Sites, Tag 03CO.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, the general-object section construction,
finite-cover sheaf equalizers and adjunction paragraphs; abelian extension by
Modules on Sites, Tag 03CO.
(blueprint: lem-weil-pbc-colimit-site-abelian-section-representatives).

Proof: Construct the additive subpresheaf B of the canonical inverse image H
whose sections are finite sums of restrictions of stage images. Restrictions
preserve its explicitly defined subgroups. The finite-cover descent lemma says
B is a sheaf. Factor the adjunction unit G to V i restriction of H through B:
for each source section, the h-alpha equation at the identity presentation
expresses its unit image as a generator, transported by cocone naturality.
This gives a sheaf map G to V i restriction of B. Transpose it to b : H to B.
The composite of b with the inclusion B to H has the same adjunct as the
identity of H, hence equals the identity. Thus every section of H belongs
to B. At V i U the finite-expression refinement lemma turns this subgroup
membership into one stage representative. That lemma uses only the object
and arrow colimit hypotheses and filteredness, not finite-cover descent.
All transports are explicit, and the conclusion retains the original HEq.
For empty covers the sheaf condition enforces the zero group. If a source
stage is empty there is no U; zero has the zero stage representative.
-/
theorem colimit_site_abelian_section_representatives
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
    (U : F.obj i)
    (x : ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
        (op ((V.ι.app i).toFunctor.obj U))) :
    ∃ (t : Under i)
      (y : ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U))),
      HEq ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) y) x := by
  classical
  let H := ColimitSiteStageImage.target F P V Q i G
  let B := ColimitSiteStageImage.presheaf F P V Q i G α
  have hB : Presheaf.IsSheaf Q.toGrothendieck B :=
    colimit_site_abelian_stage_image_isSheaf J F P hfinite hcover hpullback
      V hobjects harrows Q hQ hVpullback i G α hα
  let S : Sheaf Q.toGrothendieck AddCommGrpCat.{u} := ⟨B, hB⟩
  let m : S ⟶ H := ⟨ColimitSiteStageImage.inclusion F P V Q i G α⟩
  let adj := sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
    (P i).toGrothendieck Q.toGrothendieck
  have hunit (X : F.obj i) (z : G.obj.obj (op X)) :
      (adj.unit.app G).hom.app (op X) z ∈
        ColimitSiteStageImage.subgroup F P V Q i G α
          (op ((V.ι.app i).toFunctor.obj X)) := by
    let t : Under i := Under.mk (𝟙 i)
    let W := (F.map t.hom).toFunctor.obj X
    have hw : (V.ι.app t.right).toFunctor.obj W = (V.ι.app i).toFunctor.obj X :=
      congrArg (fun f ↦ f.obj X) (congrArg Cat.Hom.toFunctor (V.w t.hom))
    let η := ((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
      (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X)
    have he : η ≫ (α t).hom.app (op W) ≫ H.obj.map (eqToHom hw.symm).op =
        (adj.unit.app G).hom.app (op X) := by
      apply Arrow.mk_injective
      simpa only [eqToHom_op, eqToHom_map, ← Category.assoc,
        Arrow.arrow_mk_comp_eqToHom] using hα t X
    apply AddSubgroup.subset_closure
    refine ⟨t, W, eqToHom hw.symm, η z, ?_⟩
    exact ConcreteCategory.congr_hom he z
  let η : G ⟶ ((V.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
      (P i).toGrothendieck Q.toGrothendieck).obj S := ⟨{
    app := fun X ↦ AddCommGrpCat.ofHom
      { toFun := fun z ↦ ⟨(adj.unit.app G).hom.app X z, hunit X.unop z⟩
        map_zero' := by apply Subtype.ext; exact map_zero _
        map_add' := by intro z w; apply Subtype.ext; exact map_add _ _ _ }
    naturality := by
      intro X Y f
      ext z
      apply Subtype.ext
      exact NatTrans.naturality_apply (adj.unit.app G).hom f z }⟩
  let b : H ⟶ S := (adj.homEquiv G S).symm η
  have hb : b ≫ m = 𝟙 H := by
    apply (adj.homEquiv G H).injective
    rw [adj.homEquiv_naturality_right, adj.homEquiv_id]
    change (adj.homEquiv G S) ((adj.homEquiv G S).symm η) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hx : x ∈ ColimitSiteStageImage.subgroup F P V Q i G α
      (op ((V.ι.app i).toFunctor.obj U)) := by
    let y := b.hom.app (op ((V.ι.app i).toFunctor.obj U)) x
    have hy : y.val = x :=
      congrArg (fun k : H ⟶ H ↦ k.hom.app (op ((V.ι.app i).toFunctor.obj U)) x) hb
    exact hy ▸ y.property
  exact colimit_site_abelian_stage_image_refinement J F P V hobjects harrows
    Q i G α hα U x hx

end CategoryTheory
