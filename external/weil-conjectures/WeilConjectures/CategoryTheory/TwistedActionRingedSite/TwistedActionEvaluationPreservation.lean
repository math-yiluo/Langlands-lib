/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionEvaluationUnique

/-! # Preservation of the specified sheaf-Hom evaluations

Source: the normalized tensor and evaluation formulas of the twisted action-site
presentation; Stacks 03EK, 03EL and 03EO. No native or derived category occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

attribute [local irreducible] SheafOfModules.monoidalCategory sigma pureTensor evaluationMap
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric

private theorem forgetPairs_obj {A : Type (u + 1)} [Category.{u} A]
    (T : A ⥤ A) (M : Pairs T) :
    (forgetPairs T).obj M = M.obj.a := rfl

private theorem forgetPairs_map {A : Type (u + 1)} [Category.{u} A]
    (T : A ⥤ A) {M N : Pairs T} (f : M ⟶ N) :
    (forgetPairs T).map f = f.hom.f := rfl

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

omit [s.functor.IsContinuous J J] in
/-- The specified tensor and Hom components preserve right sheaf-Hom evaluation.

Source: Stacks 03EK and 03EO; the specified presentation evaluation and symmetry
(blueprint: lem-sf-twisted-action-evaluation-preservation).

Proof: the complete pure-tensor characterization of each evaluation identifies it
with braiding followed by canonical left evaluation. Braiding naturality moves the
specified Hom comparison across the braiding. The presentation symmetry moves the
tensor comparison across it as well. The given left-evaluation square then proves
the required right-evaluation square. -/
theorem specified_evaluation_square (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ (M N : Modules P.coefficient)
      (eB : tensorObj (SheafOfModules.homObj (R := P.coefficient) M N) M ⟶ N)
      (eA : tensorObj (SheafOfModules.homObj (R := R) (U.obj M) (U.obj N)) (U.obj M) ⟶
        U.obj N),
      RingedForgetTensorTransposition.IsSheafEvaluation.{u, u, u}
        P.topology P.coefficient M N eB →
      RingedForgetTensorTransposition.IsSheafEvaluation.{u, u, u}
        J R (U.obj M) (U.obj N) eA →
      (P.tensor (SheafOfModules.homObj (R := P.coefficient) M N) M).hom ≫
        tensorMap (P.hom M N).hom (𝟙 (U.obj M)) ≫ eA = U.map eB := by
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  dsimp only
  intro M N eB eA hB hA
  rw [right_evaluation_eq M N eB hB, right_evaluation_eq (U.obj M) (U.obj N) eA hA,
    Functor.map_comp]
  change (P.tensor (SheafOfModules.homObj (R := P.coefficient) M N) M).hom ≫
      tensorMap (P.hom M N).hom (𝟙 (U.obj M)) ≫
        (β_ (SheafOfModules.homObj (R := R) (U.obj M) (U.obj N)) (U.obj M)).hom ≫
          evaluationMap (U.obj M) (U.obj N) = _
  dsimp only [tensorMap]
  erw [BraidedCategory.braiding_naturality_assoc (P.hom M N).hom (𝟙 (U.obj M)),
    ← Category.assoc,
    ← P.symmetry (SheafOfModules.homObj (R := P.coefficient) M N) M, Category.assoc]
  simpa only [U, Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
    forgetPairs_map, forgetPairs_obj, tensorMap, tensorObj] using
    congrArg (fun f ↦ (P.modules.functor.map
      (β_ (SheafOfModules.homObj (R := P.coefficient) M N) M).hom).hom.f ≫ f)
        (P.evaluation M N).symm

end CategoryTheory.TwistedActionRingedSite
