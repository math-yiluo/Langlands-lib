/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueLimit
import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Compatible finite-level bases for the integral root tower

## References

* Bhatt--Scholze, Section 6.8
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def freePullIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Mod.freeFunctor R ⋙ (upperStar Ab.{u + 1} f).mapMod R ≅
      upperStar Ab.{u + 1} f ⋙ Mod.freeFunctor ((upperStar Ab.{u + 1} f).obj R) := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  exact ((Mod.freeForgetAdjunction R).comp (adj.mapModAdjunction R)).leftAdjointUniq
    (adj.comp (Mod.freeForgetAdjunction ((upperStar Ab.{u + 1} f).obj R)))

private noncomputable def tateSystemFreeIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    tateModuleSystem X ℓ ≅ tateRootsSystem X ℓ ⋙
      Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) := by
  let t : tateModuleSystem X ℓ ⟶ tateRootsSystem X ℓ ⋙
      Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [Functor.comp_map, tateModuleSystem, tateRootsSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, Category.comp_id]
      rfl)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- A single pro-étale cover identifies the actual free root tower with the residue tower. -/
theorem exists_tateModule_residue_diagram_iso
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : Γ(X, ⊤))) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty
        (tateModuleSystem X ℓ ⋙ (upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X) ≅
        tateResidueModuleSystem X ℓ ⋙ (upperStar Ab.{u + 1} (𝒰.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_compatible_roots_diagram_basis X ℓ hℓ
  obtain ⟨eQ⟩ := constantTateResidueSystem_free_iso X ℓ
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨eRoots⟩ := h𝒰 i
  let R := condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X
  let F := upperStar Ab.{u + 1} (𝒰.f i)
  let Φ := F.mapMod R
  let P := Mod.freeFunctor R
  let Q := Mod.freeFunctor (F.obj R)
  let e := freePullIso (𝒰.f i) R
  exact ⟨Functor.isoWhiskerRight (tateSystemFreeIso X ℓ) Φ ≪≫
    Functor.associator (tateRootsSystem X ℓ) P Φ ≪≫
    Functor.isoWhiskerLeft (tateRootsSystem X ℓ) e ≪≫
    (Functor.associator (tateRootsSystem X ℓ) F Q).symm ≪≫
    Functor.isoWhiskerRight eRoots Q ≪≫
    Functor.associator (constantTateResidueSystem X ℓ) F Q ≪≫
    Functor.isoWhiskerLeft (constantTateResidueSystem X ℓ) e.symm ≪≫
    (Functor.associator (constantTateResidueSystem X ℓ) P Φ).symm ≪≫
    Functor.isoWhiskerRight eQ Φ⟩

end AlgebraicGeometry.ProEtale
