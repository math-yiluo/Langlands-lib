/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section
universe uMain wMain
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Inverses of compatible augmentations are compatible with the transition maps. -/
private theorem koszulOpenHom_inverse_naturality
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {X Y S : C} (m : Y ⟶ X) (u : X ⟶ S) (u' : Y ⟶ S)
    (v : R.obj S ⟶ R.obj X) (v' : R.obj S ⟶ R.obj Y)
    (hu : R.map u ≫ v = 𝟙 _) (hu' : v' ≫ R.map u' = 𝟙 _)
    (hm : m ≫ u = u') : v' ≫ R.map m = v := by
  calc
    v' ≫ R.map m = v' ≫ R.map m ≫ R.map u ≫ v := by rw [hu, Category.comp_id]
    _ = v' ≫ R.map u' ≫ v := by rw [← Category.assoc (R.map m), ← R.map_comp, hm]
    _ = v := by rw [← Category.assoc, hu', Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Intermediate representability and colimit assertion; source Tags 08DC and 08DD.
(blueprint: lem-sc-affine-perfect-open-represent-cohomology-colimit) -/
theorem affine_perfect_open_represent_cohomology_colimit
    (A : Type uMain) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{wMain}
      (SheafOfModules.{uMain} (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    ∃ v : ∀ e : ℕ,
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenStructure A) ⟶
      ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                (koszulOpen A r f)) ⋙
              Equivalence.functor
                (C := SheafOfModules.{uMain}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                (D := SheafOfModules.{uMain}
                  (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
        (koszulOpenObject A r f e),
      (∀ e : ℕ,
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) ≫ v e = 𝟙 _) ∧
      (∀ e : ℕ, v e ≫
        ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                  (koszulOpen A r f)) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{uMain}
                    ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                  (D := SheafOfModules.{uMain}
                    (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map
          (koszulOpenUnit A r f e) = 𝟙 _) ∧
      ∃ ι : koszulOpenHomDiagram A r f E.1 ⟶
        (Functor.const ℕ).obj
          (((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj
              (koszulOpenStructure A) ⟶
           ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                     (koszulOpen A r f)) ⋙
                   Equivalence.functor
                     (C := SheafOfModules.{uMain}
                       ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                     (D := SheafOfModules.{uMain}
                       (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                     (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.obj E.1),
        (∀ (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1),
          ι.app e φ = v e ≫
            ((SheafOfModules.overFunctor.{uMain} (moduleRings (Spec (.of A)).toRingedSpace)
                      (koszulOpen A r f)) ⋙
                    Equivalence.functor
                      (C := SheafOfModules.{uMain}
                        ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
                      (D := SheafOfModules.{uMain}
                        (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
                      (Scheme.Modules.overEquiv (koszulOpen A r f))).mapDerivedCategory.map φ) ∧
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  classical
  let F := SheafOfModules.overFunctor.{uMain}
    (moduleRings (Spec (.of A)).toRingedSpace) (koszulOpen A r f)
  let G := Equivalence.functor
    (C := SheafOfModules.{uMain}
      ((moduleRings (Spec (.of A)).toRingedSpace).over (koszulOpen A r f)))
    (D := SheafOfModules.{uMain}
      (moduleRings (koszulOpen A r f).toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv (koszulOpen A r f))
  let R := (F ⋙ G).mapDerivedCategory
  change ∃ v : ∀ e : ℕ,
      R.obj (koszulOpenStructure A) ⟶ R.obj (koszulOpenObject A r f e),
    (∀ e, R.map (koszulOpenUnit A r f e) ≫ v e = 𝟙 _) ∧
    (∀ e, v e ≫ R.map (koszulOpenUnit A r f e) = 𝟙 _) ∧
    ∃ ι : koszulOpenHomDiagram A r f E.1 ⟶
        (Functor.const ℕ).obj (R.obj (koszulOpenStructure A) ⟶ R.obj E.1),
      (∀ e φ, ι.app e φ = v e ≫ R.map φ) ∧ Nonempty (IsColimit (Cocone.mk _ ι))
  have hi (e : ℕ) : IsIso (F.mapDerivedCategory.map (koszulOpenUnit A r f e)) := by
    have hU : (⨆ i : Fin r, (Spec (.of A)).basicOpen
        ((Scheme.ΓSpecIso (.of A)).inv (f i))) = koszulOpen A r f := by
      unfold koszulOpen
      congr 1
      funext i
      exact basicOpen_eq_of_affine (R := .of A) (f i)
    let P := fun U : (Spec (.of A)).Opens ↦
      IsIso ((SheafOfModules.overFunctor.{uMain}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.map
          (koszulOpenUnit A r f e))
    exact Eq.mp (congrArg P hU)
      (affine_perfect_koszul_principal_unit A r f (e + 1) (Nat.le_add_left 1 e)).2
  have hiso (e : ℕ) : IsIso (R.map (koszulOpenUnit A r f e)) := by
    have := hi e
    apply (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIso F G)
      (koszulOpenUnit A r f e)).1
    change IsIso (G.mapDerivedCategory.map
      (F.mapDerivedCategory.map (koszulOpenUnit A r f e)))
    infer_instance
  let v := fun e ↦ @inv _ _ _ _ (R.map (koszulOpenUnit A r f e)) (hiso e)
  have : R.Additive := by
    change (F ⋙ G).mapDerivedCategory.Additive
    infer_instance
  have hv₁ (e : ℕ) : R.map (koszulOpenUnit A r f e) ≫ v e = 𝟙 _ := by
    have := hiso e
    exact IsIso.hom_inv_id (R.map (koszulOpenUnit A r f e))
  have hv₂ (e : ℕ) : v e ≫ R.map (koszulOpenUnit A r f e) = 𝟙 _ := by
    have := hiso e
    exact IsIso.inv_hom_id (R.map (koszulOpenUnit A r f e))
  have hmap := (affine_perfect_open_represent_cohomology_core A r f).2.2
  have hvmap (a b : ℕ) (h : a ≤ b) :
      v b ≫ R.map (koszulOpenMap A r f a b h) = v a := by
    exact koszulOpenHom_inverse_naturality R (koszulOpenMap A r f a b h)
      (koszulOpenUnit A r f a) (koszulOpenUnit A r f b) (v a) (v b)
      (hv₁ a) (hv₂ b) (hmap a b h)
  let ι : koszulOpenHomDiagram A r f E.1 ⟶
      (Functor.const ℕ).obj (R.obj (koszulOpenStructure A) ⟶ R.obj E.1) :=
    { app := fun e ↦ TypeCat.ofHom (fun φ ↦ v e ≫ R.map φ)
      naturality := by
        intro a b h
        ext φ
        change v b ≫ R.map (koszulOpenMap A r f a b (leOfHom h) ≫ φ) =
          v a ≫ R.map φ
        rw [R.map_comp, ← Category.assoc, hvmap] }
  have hι (e : ℕ) (φ : koszulOpenObject A r f e ⟶ E.1) :
      ι.app e φ = v e ≫ R.map φ := rfl
  have hsurj := koszulOpenHom_restriction_surjective A r f E v hv₁ hv₂
  have hzero := koszulOpenHom_restriction_eventually_zero A r f E
  refine ⟨v, hv₁, hv₂, ι, hι, ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩⟩
  · intro ψ
    obtain ⟨e, φ, hφ⟩ := hsurj ψ
    exact ⟨e, φ, (hι e φ).trans hφ |>.symm⟩
  · intro e φ ψ heq
    change (koszulOpenObject A r f e ⟶ E.1) at φ ψ
    have := hiso e
    have hz : R.map (φ - ψ) = 0 :=
      (R.map_sub (f := φ) (g := ψ)).trans
        (sub_eq_zero.mpr ((cancel_epi (v e)).mp heq))
    obtain ⟨b, h, hb⟩ := hzero e (φ - ψ) hz
    refine ⟨b, homOfLE h, ?_⟩
    change koszulOpenMap A r f e b h ≫ φ = koszulOpenMap A r f e b h ≫ ψ
    simpa only [Preadditive.comp_sub, sub_eq_zero] using hb

end AlgebraicGeometry
