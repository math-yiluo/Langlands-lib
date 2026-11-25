/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RouteInverseImageConstantRingOperations

/-! # Ring-operation assembly. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Ring-object assembly from a canonical underlying comparison.
Source: Stacks Project, `sites.tex`, Tag 00YV
(auxiliary; not a blueprint node). -/
 theorem constantRingComparisonAssembly
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (hL : PreservesFiniteLimits L)
    (rings : Sheaf JC CommRingCat.{u} ⥤ Sheaf JD CommRingCat.{u})
    (e : ∀ R : Sheaf JC CommRingCat.{u}, RingInverseImage L R (rings.obj R))
    (enat : ∀ {R S : Sheaf JC CommRingCat.{u}} (φ : R ⟶ S),
      L.map ((sheafCompose JC (forget CommRingCat)).map φ) ≫
          (e S).ringUnderlying.hom =
        (e R).ringUnderlying.hom ≫
          (sheafCompose JD (forget CommRingCat)).map (rings.map φ))
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u)) :
      ∃ (constants : constantSheaf JC CommRingCat.{u} ⋙ rings ≅
        constantSheaf JD CommRingCat.{u}),
        ∀ A : CommRingCat.{u},
          (sheafCompose JD (forget CommRingCat)).map
              ((constants.app A).hom) =
            (e ((constantSheaf JC CommRingCat.{u}).obj A)).ringUnderlying.inv ≫
              ((constantRingSetComparison JC JD L kappa).app A).hom := by
  classical
  let k := constantRingSetComparison JC JD L kappa
  let f (A : CommRingCat.{u}) :=
    (e ((constantSheaf JC CommRingCat.{u}).obj A)).ringUnderlying.inv ≫ k.hom.app A
  let g (A : CommRingCat.{u}) :
      rings.obj ((constantSheaf JC CommRingCat.{u}).obj A) ⟶
        (constantSheaf JD CommRingCat.{u}).obj A :=
    ⟨{ app := fun U ↦ CommRingCat.ofHom
          (show (rings.obj ((constantSheaf JC CommRingCat.{u}).obj A)).obj.obj U →+*
            ((constantSheaf JD CommRingCat.{u}).obj A).obj.obj U from
          { toFun := (f A).hom.app U
            map_zero' := (constantComparison_ring_operations JC JD L hL kappa A _ (e _) U).1
            map_one' := (constantComparison_ring_operations JC JD L hL kappa A _ (e _) U).2.1
            map_add' := (constantComparison_ring_operations JC JD L hL kappa A _ (e _) U).2.2.1
            map_mul' := (constantComparison_ring_operations JC JD L hL kappa A _ (e _) U).2.2.2 })
       naturality := by
         intro U V a
         ext x
         exact congrArg (fun h ↦ h x) ((f A).hom.naturality a) }⟩
  have hg (A : CommRingCat.{u}) : (sheafCompose JD (forget CommRingCat)).map (g A) = f A := by
    rfl
  have hgi (A : CommRingCat.{u}) : IsIso (g A) := by
    have : IsIso (f A) := by dsimp [f]; infer_instance
    have : IsIso ((sheafCompose JD (forget CommRingCat)).map (g A)) := by rw [hg]; infer_instance
    exact isIso_of_reflects_iso (g A) (sheafCompose JD (forget CommRingCat))
  let constants : constantSheaf JC CommRingCat.{u} ⋙ rings ≅
      constantSheaf JD CommRingCat.{u} :=
    NatIso.ofComponents (fun A ↦ asIso (g A)) (by
      intro A B a
      apply (sheafCompose JD (forget CommRingCat)).map_injective
      simp only [Functor.map_comp, asIso_hom, hg]
      change (sheafCompose JD (forget CommRingCat)).map
        (rings.map ((constantSheaf JC CommRingCat.{u}).map a)) ≫ f B =
        f A ≫ (sheafCompose JD (forget CommRingCat)).map
          ((constantSheaf JD CommRingCat.{u}).map a)
      have he := enat ((constantSheaf JC CommRingCat.{u}).map a)
      have hk := k.hom.naturality a
      dsimp only [Functor.comp_map] at hk
      dsimp only [f]
      -- Rewrite naturality of the inverse comparison before using naturality of k.
      have hei : (sheafCompose JD (forget CommRingCat)).map
          (rings.map ((constantSheaf JC CommRingCat.{u}).map a)) ≫
            (e ((constantSheaf JC CommRingCat.{u}).obj B)).ringUnderlying.inv =
          (e ((constantSheaf JC CommRingCat.{u}).obj A)).ringUnderlying.inv ≫
            L.map ((sheafCompose JC (forget CommRingCat)).map
              ((constantSheaf JC CommRingCat.{u}).map a)) := by
        apply (cancel_mono (e ((constantSheaf JC CommRingCat.{u}).obj B)).ringUnderlying.hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [he, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hei, Category.assoc, hk]
      simp only [Category.assoc])
  exact ⟨constants, hg⟩

end CategoryTheory
