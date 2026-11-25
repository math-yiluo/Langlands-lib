/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ExactFunctorAffinePullbackSections
import WeilConjectures.AlgebraicGeometry.GlobalSectionsLimitComparison
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Global-section continuity for inverse systems of affine schemes -/

@[expose] public section

universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem a4_scalar_continuity
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] {S : Scheme.{u}}
    [IsAffine S]
    (D : Jᵒᵖ ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (π : D ⟶ (Functor.const Jᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ j : J, p = c.π.app (op j) ≫ π.app (op j))
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (H : J ⥤ AddCommGrpCat.{u + 1})
    (e : ∀ j : J, H.obj j ≅ (Sheaf.Γ (D.obj (op j)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} (π.app (op j))).obj G))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f ≫ (e k).hom =
      (e j).hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (D.map f.op)
        ((upperStar AddCommGrpCat.{u + 1} (π.app (op j))).obj G) ≫
      (Sheaf.Γ (D.obj (op k)).smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1} (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id] using (π.naturality f.op).symm)).inv.app G))
    (K : Cocone H) (eK : K.pt ≅ (Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} p).obj G))
    (hK : ∀ j : J, K.ι.app j ≫ eK.hom =
      (e j).hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (c.π.app (op j))
        ((upperStar AddCommGrpCat.{u + 1} (π.app (op j))).obj G) ≫
      (Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (π.app (op j)) p
          (hp j)).inv.app G)) :
    Nonempty (IsColimit K) := by
  classical
  let : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨hlift, hzero⟩ := globalSections_limit_comparison D π c p
    (fun j ↦ hp j.unop) hc G
  have ht_apply (j : J) (s : H.obj j) :
      pullbackSectionMap G (c.π.app (op j)) (π.app (op j)) p (hp j) ((e j).hom s) =
        eK.hom (K.ι.app j s) := by
    exact (ConcreteCategory.congr_hom (hK j) s).symm
  have hm_apply {j k : J} (f : j ⟶ k) (s : H.obj j) :
      pullbackSectionMap G (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simp) ((e j).hom s) =
        (e k).hom (H.map f s) := by
    exact (ConcreteCategory.congr_hom (hH j k f) s).symm
  let d := colimit.desc H K
  have hd (j : J) (s : H.obj j) : d (colimit.ι H j s) = K.ι.app j s :=
    ConcreteCategory.congr_hom (colimit.ι_desc K j) s
  have hsurj : Function.Surjective d := by
    intro t
    obtain ⟨j, s, hs⟩ := hlift (eK.hom t)
    refine ⟨colimit.ι H j.unop ((e j.unop).inv s), ?_⟩
    apply (ConcreteCategory.bijective_of_isIso eK.hom).injective
    rw [hd, ← ht_apply]
    have he : (e j.unop).hom ((e j.unop).inv s) = s :=
      ConcreteCategory.congr_hom (e j.unop).inv_hom_id s
    rw [he]
    simpa only [pullbackSectionMap, op_unop] using hs
  have hinj : Function.Injective d := by
    apply (injective_iff_map_eq_zero d.hom).2
    intro x hx
    obtain ⟨j, s, rfl⟩ := Concrete.colimit_exists_rep H x
    have hs : pullbackSectionMap G (c.π.app (op j)) (π.app (op j)) p (hp j)
        ((e j).hom s) = 0 := by
      rw [ht_apply, ← hd, hx, eK.hom.hom.map_zero]
    obtain ⟨k, f, hf⟩ := hzero (op j) ((e j).hom s) hs
    have hsf : H.map f.unop s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (e k.unop).hom).injective
      rw [(e k.unop).hom.hom.map_zero, ← hm_apply]
      exact hf
    calc
      colimit.ι H j s = colimit.ι H k.unop (H.map f.unop s) :=
        (colimit.w_apply H f.unop s).symm
      _ = 0 := by rw [hsf, (colimit.ι H k.unop).hom.map_zero]
  have : IsIso d := (ConcreteCategory.isIso_iff_bijective d).2 ⟨hinj, hsurj⟩
  exact ⟨(colimit.isColimit H).ofIsoColimit
    (Cocone.ext (asIso d) (fun j ↦ colimit.ι_desc K j))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem a4_module_continuity (R : Type (u + 1)) [Ring R]
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] {S : Scheme.{u}}
    [IsAffine S]
    (D : Jᵒᵖ ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (π : D ⟶ (Functor.const Jᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ j : J, p = c.π.app (op j) ≫ π.app (op j))
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) (H : J ⥤ (ModuleCat.{u + 1} R))
    (e : ∀ j : J, H.obj j ≅ (Sheaf.Γ (D.obj (op j)).smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      ((upperStar (ModuleCat.{u + 1} R) (π.app (op j))).obj G))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f ≫ (e k).hom =
      (e j).hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} R) (D.map f.op)
        ((upperStar (ModuleCat.{u + 1} R) (π.app (op j))).obj G) ≫
      (Sheaf.Γ (D.obj (op k)).smallEtaleTopology (ModuleCat.{u + 1} R)).map
        ((upperStarComp (ModuleCat.{u + 1} R) (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id] using (π.naturality f.op).symm)).inv.app G))
    (K : Cocone H) (eK : K.pt ≅ (Sheaf.Γ c.pt.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      ((upperStar (ModuleCat.{u + 1} R) p).obj G))
    (hK : ∀ j : J, K.ι.app j ≫ eK.hom =
      (e j).hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} R) (c.π.app (op j))
        ((upperStar (ModuleCat.{u + 1} R) (π.app (op j))).obj G) ≫
      (Sheaf.Γ c.pt.smallEtaleTopology (ModuleCat.{u + 1} R)).map
        ((upperStarComp (ModuleCat.{u + 1} R) (c.π.app (op j)) (π.app (op j)) p
          (hp j)).inv.app G)) :
    Nonempty (IsColimit K) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let L := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let U := ModuleCat.coinduce R
  let adj : L ⊣ U := ModuleCat.forget₂CoinduceAdj R
  let F := (Sheaf.composeAndSheafify S.smallEtaleTopology L).obj G
  let θ := fun {X : Scheme.{u}} [IsAffine X] (f : X ⟶ S) ↦
    coefficientPullbackSectionsIso L U adj f G
  let e' := fun j : J ↦ L.mapIso (e j) ≪≫ θ (π.app (op j))
  let eK' := L.mapIso eK ≪≫ θ p
  have hH' : ∀ (j k : J) (f : j ⟶ k),
      (H ⋙ L).map f ≫ (e' k).hom =
        (e' j).hom ≫ pullbackSectionMap F (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simp) := by
    intro j k f
    dsimp only [e', Functor.mapIso_hom, Iso.trans_hom, Functor.comp_map]
    rw [← L.map_comp_assoc, hH j k f, L.map_comp, Category.assoc]
    simpa only [Category.assoc, pullbackSectionMap, θ, F, Functor.comp_obj,
      Functor.const_obj_obj] using congrArg (fun m ↦ L.map (e j).hom ≫ m)
      (coefficientPullbackSectionsIso_comp L U adj G (D.map f.op)
        (π.app (op j)) (π.app (op k))
        (by simp))
  have hK' : ∀ j : J, (L.mapCocone K).ι.app j ≫ eK'.hom =
      (e' j).hom ≫ pullbackSectionMap F (c.π.app (op j)) (π.app (op j)) p (hp j) := by
    intro j
    dsimp only [e', eK', Functor.mapIso_hom, Iso.trans_hom, Functor.mapCocone_ι_app]
    rw [← L.map_comp_assoc, hK j, L.map_comp, Category.assoc]
    simpa only [Category.assoc, pullbackSectionMap, θ, F, Functor.comp_obj,
      Functor.const_obj_obj] using congrArg (fun m ↦ L.map (e j).hom ≫ m)
      (coefficientPullbackSectionsIso_comp L U adj (X := c.pt) (Y := D.obj (op j)) G
        (c.π.app (op j))
        (π.app (op j)) p (hp j))
  have hc' := a4_scalar_continuity D π c hc p hp F (H ⋙ L) e' hH'
    (L.mapCocone K) eK' hK'
  exact ⟨isColimitOfReflects L hc'.some⟩

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Global sections of a fixed sheaf pulled back to affine schemes commute with directed inverse
limits over a fixed affine base. The supplied diagram and cocone are normalized by the displayed
unit/composition equations; no objects are chosen from an existence assertion. Source: Stacks
Project, Etale Cohomology, Tag 09YQ, degree zero; Sites, Tag 0738(4); blueprint
etale-cohomology-continuity, detailed proof, paragraph 2.

Proof: first convert the existing abelian-group section continuity theorem to the colimit
universal property, using stage representatives and eventual vanishing to prove bijectivity of
the comparison from the colimit. For module coefficients, apply the exact forgetful functor to
abelian groups, use its coinduction right adjoint to compare inverse images, and reflect colimits.

For general coefficients choose a separator T and the Gabriel-Popescu adjunction L ⊣ U from
modules over End(T) opposite. Its right adjoint is fully faithful and L is exact. Objectwise
application of U lifts G to a module-valued sheaf M, and the counit identifies L#M with G.
The module-valued pullback sections form a canonical diagram and colimit cocone. Exactness of L
preserves the finite matching diagrams on the affine etale basis, so affine sections of L#F
are L applied to sections of F. Uniqueness of left adjoints gives the coefficient/pullback
comparison. Its unit equation and composition coherence identify every transition and leg.
Apply the colimit-preserving L to the module cocone and transport it along these comparisons
and the supplied e and eK. This gives the colimit property of K with its original normalization.
(auxiliary; not a blueprint node) -/
theorem affine_globalSections_limit_isColimit_of_directed
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J] {S : Scheme.{u}}
    [IsAffine S]
    (D : Jᵒᵖ ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (π : D ⟶ (Functor.const Jᵒᵖ).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ j : J, p = c.π.app (op j) ≫ π.app (op j))
    (G : Sheaf S.smallEtaleTopology A) (H : J ⥤ A)
    (e : ∀ j : J, H.obj j ≅ (Sheaf.Γ (D.obj (op j)).smallEtaleTopology A).obj
      ((upperStar A (π.app (op j))).obj G))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f ≫ (e k).hom =
      (e j).hom ≫ globalSectionsUpperStarMap A (D.map f.op)
        ((upperStar A (π.app (op j))).obj G) ≫
      (Sheaf.Γ (D.obj (op k)).smallEtaleTopology A).map
        ((upperStarComp A (D.map f.op) (π.app (op j)) (π.app (op k))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id] using (π.naturality f.op).symm)).inv.app G))
    (K : Cocone H) (eK : K.pt ≅ (Sheaf.Γ c.pt.smallEtaleTopology A).obj
      ((upperStar A p).obj G))
    (hK : ∀ j : J, K.ι.app j ≫ eK.hom =
      (e j).hom ≫ globalSectionsUpperStarMap A (c.π.app (op j))
        ((upperStar A (π.app (op j))).obj G) ≫
      (Sheaf.Γ c.pt.smallEtaleTopology A).map
        ((upperStarComp A (c.π.app (op j)) (π.app (op j)) p (hp j)).inv.app G)) :
    Nonempty (IsColimit K) := by
  classical
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let T := separator A
  let L := IsGrothendieckAbelian.tensorObj T
  let U := preadditiveCoyonedaObj T
  let adj : L ⊣ U := IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction T
  have : U.Full := IsGrothendieckAbelian.GabrielPopescu.full T (isSeparator_separator A)
  have : U.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj T).mp
    (isSeparator_separator A)
  have : PreservesFiniteLimits L :=
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits T (isSeparator_separator A)
  let M := (sheafCompose S.smallEtaleTopology U).obj G
  let eG : (Sheaf.composeAndSheafify S.smallEtaleTopology L).obj M ≅ G :=
    asIso ((Sheaf.adjunction S.smallEtaleTopology adj).counit.app G)
  let F : J ⥤ ModuleCat.{u + 1} (End T)ᵐᵒᵖ :=
    { obj := fun j ↦ (Sheaf.Γ (D.obj (op j)).smallEtaleTopology _).obj
        ((upperStar _ (π.app (op j))).obj M)
      map := fun {j k} f ↦ pullbackSectionMap M (D.map f.op) (π.app (op j))
        (π.app (op k)) (by simp)
      map_id := fun j ↦ by
        dsimp
        simpa only [D.map_id] using pullbackSectionMap_id M (π.app (op j))
      map_comp := fun {i j k} f g ↦ by
        dsimp
        simpa only [D.map_comp] using
          (pullbackSectionMap_comp M (D.map g.op) (D.map f.op)
            (π.app (op i)) (π.app (op j)) (π.app (op k))
            (by simp)
            (by simp)).symm }
  let B : Cocone F :=
    { pt := (Sheaf.Γ c.pt.smallEtaleTopology _).obj ((upperStar _ p).obj M)
      ι :=
        { app := fun j ↦ pullbackSectionMap (X := c.pt) (Y := D.obj (op j)) M
              (c.π.app (op j)) (π.app (op j)) p (hp j)
          naturality := fun j k f ↦ by
            simp only [Functor.const_obj_map]
            dsimp only [F]
            simpa only [c.w f.op, Functor.const_obj_obj, Category.comp_id] using
              pullbackSectionMap_comp M (c.π.app (op k)) (D.map f.op)
                (π.app (op j)) (π.app (op k)) p
                (by simp) (hp k) } }
  have hB : IsColimit B := (a4_module_continuity (End T)ᵐᵒᵖ D π c hc p hp M F
    (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by simp [F, pullbackSectionMap]) B (Iso.refl _)
    (fun _ ↦ by simp [B, pullbackSectionMap])).some
  let ε := fun {X : Scheme.{u}} [IsAffine X] (f : X ⟶ S) ↦
    coefficientPullbackSectionsIso L U adj f M ≪≫
      (Sheaf.Γ X.smallEtaleTopology A).mapIso ((upperStar A f).mapIso eG)
  have hε {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
      (h : X ⟶ Y) (f : Y ⟶ S) (g : X ⟶ S) (w : g = h ≫ f) :
      L.map (pullbackSectionMap M h f g w) ≫ (ε g).hom =
        (ε f).hom ≫ pullbackSectionMap G h f g w := by
    dsimp only [ε, Iso.trans_hom, Functor.mapIso_hom]
    rw [reassoc_of% (coefficientPullbackSectionsIso_comp L U adj M h f g w)]
    rw [← pullbackSectionMap_naturality]
    simp only [Category.assoc]
  let n : F ⋙ L ≅ H := NatIso.ofComponents
    (fun j ↦ ε (π.app (op j)) ≪≫ (e j).symm) (by
      intro j k f
      simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom]
      change L.map (pullbackSectionMap M (D.map f.op) _ _ _) ≫ _ ≫ _ = _
      rw [reassoc_of% (hε (D.map f.op) (π.app (op j)) (π.app (op k))
        (by simp))]
      simp only [Category.assoc]
      congr 1
      apply (cancel_mono (e k).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hH, Iso.inv_hom_id_assoc]
      rfl)
  let eB : (L.mapCocone B).pt ≅ K.pt := ε p ≪≫ eK.symm
  have wB : ∀ j, (L.mapCocone B).ι.app j ≫ eB.hom = n.hom.app j ≫ K.ι.app j := by
    intro j
    simp only [n, eB, Iso.trans_hom, Iso.symm_hom, NatIso.ofComponents_hom_app]
    change L.map (pullbackSectionMap M (c.π.app (op j)) _ _ _) ≫ _ ≫ _ = _
    rw [reassoc_of% (hε (X := c.pt) (Y := D.obj (op j))
      (c.π.app (op j)) (π.app (op j)) p (hp j))]
    simp only [Category.assoc]
    congr 1
    apply (cancel_mono eK.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hK, Iso.inv_hom_id_assoc]
    rfl
  have hLK : IsColimit ((Cocone.precompose n.hom).obj K) :=
    (isColimitOfPreserves L hB).ofIsoColimit (Cocone.ext eB wB)
  exact ⟨(IsColimit.precomposeHomEquiv n K) hLK⟩


end AlgebraicGeometry.Etale
