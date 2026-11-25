/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.PerfectNoetherianCohomology
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationExtension
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Affine locally free models

## References

* Stacks Project, Tags 0G41(2), 0EY6
-/

@[expose] public section
universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme
/-- Finite locally free data extends across an affine open with finite affine sections. -/
theorem exists_affine_locally_free_model_core
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (P : W.toScheme.Modules) [P.IsFiniteLocallyFree] :
    ∃ H : (Spec A).Modules,
      H.IsQuasicoherent ∧
      (∀ V : (Spec A).Opens, IsAffineOpen V →
        Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) ∧
      Nonempty (Modules.restrict H W.ι ≅ P) := by
  let G := (Modules.overEquiv W).inverse.obj P
  have : G.IsFinitePresentation := finitePresentation_overEquiv_inverse (Spec A) W P
  let F : (Spec A).Modules := SheafOfModules.unit (Spec A).ringCatSheaf
  have : F.IsQuasicoherent := by
    dsimp only [F]
    apply SheafOfModules.isQuasicoherent_unit
  obtain ⟨H, hH, φ, e, _⟩ := Modules.exists_finitePresentation_extension
    (Spec A) W (TopologicalSpace.NoetherianSpace.isCompact _) F G 0
  let _ := hH
  refine ⟨H, inferInstance, ?_, ?_⟩
  · intro V hV
    have : Module.FinitePresentation ((Spec A).presheaf.obj (op V))
        (H.val.obj (op V)) :=
      Modules.finitePresentation_sections_of_isFinitePresentation H hV
    infer_instance
  · exact ⟨((Modules.overFunctorEquiv W).app H).symm ≪≫
      (Modules.overEquiv W).functor.mapIso e ≪≫ (Modules.overEquiv W).counitIso.app P⟩
end AlgebraicGeometry.Scheme
