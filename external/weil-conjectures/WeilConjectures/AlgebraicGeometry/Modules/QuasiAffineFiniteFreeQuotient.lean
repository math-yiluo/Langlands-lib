/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.LocalFiniteFreeGlobalMaps

/-! # Finite free quotients on Noetherian quasi-affine opens

## References

* Stacks Project, Tag 0EKP, the global-generation step of (2) to (3)
* Stacks Project, Tag 0EKP, the global-generation step of (2) to (3), with the ample invertible
  module the structure sheaf
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module on an open of a Noetherian affine scheme is
an epimorphic image of a finite free module. -/
theorem exists_epi_free_of_isFiniteLocallyFree
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsFiniteLocallyFree] :
    ∃ (r : ℕ) (β : free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ N),
      Epi β := by
  classical
  choose U hx r φ hφ using exists_free_map_isIso_near_of_isFiniteLocallyFree V N
  have : IsNoetherianRing (CommRingCat.of R) := ‹IsNoetherianRing R›
  have : TopologicalSpace.NoetherianSpace (Spec (.of R)) := inferInstance
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    TopologicalSpace.NoetherianSpace.set (V : Set (Spec (.of R)))
  have : CompactSpace V.toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set V.toScheme)) (fun x ↦ (U x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let I := Σ x : t, ULift.{u} (Fin (r x))
  let β : free (R := V.toScheme.ringCatSheaf) I ⟶ N :=
    N.freeHomEquiv.symm (fun i ↦ N.freeHomEquiv (φ i.1) i.2)
  have hfactor (x : t) : freeMap (fun i ↦ (⟨x, i⟩ : I)) ≫ β = φ x := by
    apply N.freeHomEquiv.injective
    funext i
    change sectionsMap β (sectionsMap (freeMap (fun i ↦ (⟨x, i⟩ : I)))
      (freeSection i)) = _
    rw [sectionMap_freeMap_freeSection, sectionsMap_freeHomEquiv_symm_freeSection]
  have hβ : Epi β := by
    apply epi_of_surjective_stalk
    intro y
    obtain ⟨x, hy⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
    obtain ⟨hxt, hy⟩ := Set.mem_iUnion.mp hy
    let j : t := ⟨x, hxt⟩
    have : IsIso ((restrictFunctor (U x).ι).map (φ x)) := hφ x
    have hs := (bijective_stalk_of_isIso_restrict (φ x) y hy).surjective
    let F := toPresheaf V.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have heq : F.map (freeMap (fun i ↦ (⟨j, i⟩ : I))) ≫ F.map β = F.map (φ x) := by
      rw [← F.map_comp, hfactor]
    change Function.Surjective (F.map (φ x)) at hs
    rw [← heq] at hs
    exact Function.Surjective.of_comp hs
  let _ := Fintype.ofFinite I
  let e := (SheafOfModules.freeFunctor (R := V.toScheme.ringCatSheaf)).mapIso
    ((Equiv.ulift.trans (Fintype.equivFin I).symm).toIso)
  exact ⟨Fintype.card I, e.hom ≫ β, by infer_instance⟩

end AlgebraicGeometry.Scheme.Modules
