/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace CategoryTheory

/-- Core algebra-colimit construction for a sectionwise colimit cocone.
The proof constructs the sectionwise filtered ring colimit, sheafifies it, and verifies the
algebra cocone universal property from the sheafification adjunction.
Source: Stacks Project, Sheaves, Sections 009D and 009E
(blueprint: stage3-sheaf-algebras-directed-colimit-algebra-core). -/
theorem sheafAlgebras_directed_colimit_algebra_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p))) :
    ∃ (σP : O.obj ⟶ p.pt)
      (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
      (ι : F ⟶ (Functor.const I).obj (Under.mk σ)),
      (∀ i : I, (F.obj i).hom.hom ≫ p.ι.app i = σP) ∧
      σ.hom = σP ≫ toSheafify (Opens.grothendieckTopology X) p.pt ∧
      (∀ i : I, (ι.app i).right.hom =
        p.ι.app i ≫ toSheafify (Opens.grothendieckTopology X) p.pt) ∧
      Nonempty (IsColimit (Cocone.mk (Under.mk σ) ι)) := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  let i₀ : I := Classical.arbitrary I
  let σP : O.obj ⟶ p.pt := (F.obj i₀).hom.hom ≫ p.ι.app i₀
  have hσP : ∀ i : I, (F.obj i).hom.hom ≫ p.ι.app i = σP := by
    intro i
    obtain ⟨k, hik, h₀k⟩ := exists_ge_ge i i₀
    have hcomp : ∀ (j : I) (hjk : j ≤ k),
        (F.obj j).hom.hom ≫ p.ι.app j = (F.obj k).hom.hom ≫ p.ι.app k := by
      intro j hjk
      rw [← p.w (homOfLE hjk)]
      change (F.obj j).hom.hom ≫ (F.map (homOfLE hjk)).right.hom ≫ p.ι.app k = _
      rw [← Category.assoc]
      have hw := congrArg (fun f ↦ f.hom) (Under.w (F.map (homOfLE hjk)))
      change (F.obj j).hom.hom ≫ (F.map (homOfLE hjk)).right.hom =
        (F.obj k).hom.hom at hw
      rw [hw]
    exact (hcomp i hik).trans (hcomp i₀ h₀k).symm
  let σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt :=
    ⟨σP ≫ toSheafify (Opens.grothendieckTopology X) p.pt⟩
  let c : Cocone (F ⋙ Under.forget O) := Sheaf.sheafifyCocone p
  have hc : IsColimit c := Sheaf.isColimitSheafifyCocone (F := F ⋙ Under.forget O) p
    (evaluationJointlyReflectsColimits p (fun U ↦ (hp U.unop).some))
  have hσ : ∀ i : I, (F.obj i).hom ≫ c.ι.app i = σ := by
    intro i
    apply Sheaf.hom_ext
    change (F.obj i).hom.hom ≫ (c.ι.app i).hom = _
    rw [Sheaf.sheafifyCocone_ι_app_val, ← Category.assoc, hσP]
  let ι : F ⟶ (Functor.const I).obj (Under.mk σ) :=
    { app := fun i ↦ Under.homMk (c.ι.app i) (hσ i)
      naturality := by
        intro i j f
        apply Under.UnderMorphism.ext
        exact c.w f }
  have hcolim : IsColimit (Cocone.mk (Under.mk σ) ι) :=
    { desc := fun s ↦ Under.homMk (hc.desc ((Under.forget O).mapCocone s)) (by
        change σ ≫ hc.desc ((Under.forget O).mapCocone s) = s.pt.hom
        rw [← hσ i₀, Category.assoc, hc.fac]
        exact Under.w (s.ι.app i₀))
      fac := by
        intro s i
        apply Under.UnderMorphism.ext
        exact hc.fac ((Under.forget O).mapCocone s) i
      uniq := by
        intro s m hm
        apply Under.UnderMorphism.ext
        apply hc.hom_ext
        intro i
        exact (congrArg (fun f ↦ f.right) (hm i)).trans
          (hc.fac ((Under.forget O).mapCocone s) i).symm }
  refine ⟨σP, σ, ι, hσP, rfl, ?_, ⟨hcolim⟩⟩
  intro i
  exact Sheaf.sheafifyCocone_ι_app_val (F := F ⋙ Under.forget O) p i


end CategoryTheory
