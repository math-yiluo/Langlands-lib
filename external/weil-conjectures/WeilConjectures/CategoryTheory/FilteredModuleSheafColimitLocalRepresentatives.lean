/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Local representatives in filtered colimits of module sheaves

Source: Stacks Project, Sites, Tag 0738, proof of (4).
-/

@[expose] public section

universe u v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Every section of a filtered sheaf colimit locally comes from a diagram stage.
Source: Stacks Project, Sites, Tag 0738, proof of (4), local representability before
finite selection (blueprint: lem-weil-pbc-filtered-module-sheaf-colimit-local-representatives).

Proof (the local-image argument written out by Y2): Inside the colimit sheaf H, take
the sectionwise union of the images of all
coprojections. This is a subpresheaf of modules: filteredness places any two images
in one common stage, where addition and scalar multiplication preserve the image.
Close this subpresheaf under local membership. The resulting subpresheaf K is a
subsheaf of H: restrictions preserve local membership, and gluing in H followed by
transitivity of covering sieves proves local membership of each amalgamation.
All coprojections factor through K. The colimit universal property gives H → K
whose composite with the inclusion K → H is the identity, since this composite
agrees with the identity on every coprojection. Thus every section of H belongs
locally to a coprojection image. The sieve of arrows admitting such a representative
is closed under precomposition by naturality of the coprojections and is covering.
Use this sieve as S. This argument uses only subsets of H's section modules, so
requires no relation between the site universe and the module universe and no
sheafification existence assumption. To pass between the module and type sheaf
conditions in independent universes, identify the module forgetful functor with
Hom from the lifted rank-one module ULift Λ. This represents it by a module in
the section universe and proves preservation of limits of the size of the site.
Reflection follows by factoring through additive groups. -/
theorem filtered_module_sheaf_colimit_local_representatives
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type r) [CommRing Λ]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf J (ModuleCat.{max r w} Λ))
    (c : Cocone G) (hc : IsColimit c) (U : C) (t : c.pt.obj.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ (i : I) (s : (G.obj i).obj.obj (op V)),
          ((c.ι.app i).hom.app (op V)).hom s = (c.pt.obj.map f.op).hom t := by
  classical
  have fac {i j : I} (f : i ⟶ j) (W : Cᵒᵖ) (s : (G.obj i).obj.obj W) :
      ((c.ι.app j).hom.app W).hom (((G.map f).hom.app W).hom s) =
        ((c.ι.app i).hom.app W).hom s := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun q ↦ q.hom) (c.w f)) W) s
    exact h
  let R : Subfunctor (c.pt.obj ⋙ forget (ModuleCat.{max r w} Λ)) :=
    { obj W := {s | ∃ (i : I) (x : (G.obj i).obj.obj W),
          ((c.ι.app i).hom.app W).hom x = s}
      map := by
        rintro W W' f s ⟨i, x, rfl⟩
        refine ⟨i, ((G.obj i).obj.map f).hom x, ?_⟩
        have h := congrArg (fun q ↦ q.hom x) ((c.ι.app i).hom.naturality f)
        exact h }
  have hz (W : Cᵒᵖ) : (0 : c.pt.obj.obj W) ∈ R.obj W := by
    exact ⟨Classical.choice IsFiltered.nonempty, 0, map_zero _⟩
  have ha (W : Cᵒᵖ) {x y : c.pt.obj.obj W}
      (hx : x ∈ R.obj W) (hy : y ∈ R.obj W) : x + y ∈ R.obj W := by
    obtain ⟨i, a, rfl⟩ := hx
    obtain ⟨j, b, rfl⟩ := hy
    refine ⟨IsFiltered.max i j,
      ((G.map (IsFiltered.leftToMax i j)).hom.app W).hom a +
        ((G.map (IsFiltered.rightToMax i j)).hom.app W).hom b, ?_⟩
    rw [map_add, fac, fac]
  have hm (W : Cᵒᵖ) (a : Λ) {x : c.pt.obj.obj W}
      (hx : x ∈ R.obj W) : a • x ∈ R.obj W := by
    obtain ⟨i, b, rfl⟩ := hx
    exact ⟨i, a • b, map_smul _ _ _⟩
  let M (W : Cᵒᵖ) : Submodule Λ (c.pt.obj.obj W) :=
    { carrier := (R.sheafify J).obj W
      zero_mem' := (R.le_sheafify J) W (hz W)
      add_mem' := by
        intro x y hx hy
        apply J.superset_covering _ (J.intersection_covering hx hy)
        intro V f hf
        change ((c.pt.obj.map f.op).hom (x + y)) ∈ R.obj (op V)
        rw [map_add]
        exact ha _ hf.1 hf.2
      smul_mem' := by
        intro a x hx
        apply J.superset_covering _ hx
        intro V f hf
        change ((c.pt.obj.map f.op).hom (a • x)) ∈ R.obj (op V)
        rw [map_smul]
        exact hm _ a hf }
  let K : Cᵒᵖ ⥤ ModuleCat.{max r w} Λ :=
    { obj W := ModuleCat.of Λ (M W)
      map f := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨(c.pt.obj.map f).hom s.val, (R.sheafify J).map f s.property⟩
          map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intro a x; apply Subtype.ext; exact map_smul _ _ _ }
      map_id := by
        intro W
        ext x
        change (c.pt.obj.map (𝟙 W)).hom x.val = x.val
        rw [Functor.map_id]
        rfl
      map_comp := by
        intro W W' W'' f g
        ext x
        change (c.pt.obj.map (f ≫ g)).hom x.val =
          (c.pt.obj.map g).hom ((c.pt.obj.map f).hom x.val)
        rw [Functor.map_comp]
        rfl }
  have : ReflectsLimitsOfSize.{v, max v u} (forget (ModuleCat.{max r w} Λ)) :=
    inferInstanceAs (ReflectsLimitsOfSize.{v, max v u}
      (forget₂ (ModuleCat.{max r w} Λ) AddCommGrpCat ⋙ forget AddCommGrpCat))
  let L : ModuleCat.{max r w} Λ := ModuleCat.of Λ (ULift.{w} Λ)
  let eval : coyoneda.obj (op L) ≅ forget (ModuleCat.{max r w} Λ) :=
    NatIso.ofComponents (fun N ↦ Equiv.toIso
      { toFun := fun f ↦ f.hom ⟨1⟩
        invFun := fun x ↦ ModuleCat.ofHom
          { toFun := fun a ↦ a.down • x
            map_add' := by intro a b; exact add_smul _ _ _
            map_smul' := by intro a b; exact mul_smul _ _ _ }
        left_inv := by
          intro f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro a
          change a.down • f.hom ⟨1⟩ = f.hom a
          calc
            _ = f.hom (a.down • (⟨1⟩ : ULift.{w} Λ)) := (map_smul _ _ _).symm
            _ = f.hom a := congrArg f.hom (by apply ULift.ext; simp)
        right_inv := by intro x; exact one_smul Λ x })
      (by intro N N' f; ext g; rfl)
  have : PreservesLimitsOfSize.{v, max v u} (forget (ModuleCat.{max r w} Λ)) :=
    preservesLimits_of_natIso eval
  have hK : Presheaf.IsSheaf J K := by
    apply Presheaf.isSheaf_of_isSheaf_comp J K (forget (ModuleCat.{max r w} Λ))
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf J (R.sheafify J).toFunctor
    apply R.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact Presheaf.isSheaf_comp_of_isSheaf J c.pt.obj _ c.pt.property
  let H : Sheaf J (ModuleCat.{max r w} Λ) := ⟨K, hK⟩
  let m : H ⟶ c.pt :=
    ⟨{ app W := ModuleCat.ofHom (M W).subtype
       naturality := by intros; rfl }⟩
  let d : Cocone G :=
    { pt := H
      ι :=
        { app i :=
            ⟨{ app W := ModuleCat.ofHom (((c.ι.app i).hom.app W).hom.codRestrict
                  (M W) (fun x ↦ (R.le_sheafify J) W ⟨i, x, rfl⟩))
               naturality := by
                 intro W W' f
                 ext x
                 apply Subtype.ext
                 have h := congrArg (fun q ↦ q.hom x) ((c.ι.app i).hom.naturality f)
                 exact h }⟩
          naturality := by
            intro i j f
            ext W x
            apply Subtype.ext
            exact fac f W x } }
  have hd (i : I) : d.ι.app i ≫ m = c.ι.app i := by rfl
  have hdesc : hc.desc d ≫ m = 𝟙 c.pt := by
    apply hc.hom_ext
    intro i
    rw [← Category.assoc, hc.fac, hd, Category.comp_id]
  have ht : ((hc.desc d).hom.app (op U) t).val = t := by
    have h := congrArg (fun q ↦ (q.hom.app (op U)).hom t) hdesc
    exact h
  have hmem : t ∈ (R.sheafify J).obj (op U) := by
    rw [← ht]
    exact ((hc.desc d).hom.app (op U) t).property
  exact ⟨R.sieveOfSection t, hmem, fun V f hf ↦ hf⟩

end CategoryTheory
