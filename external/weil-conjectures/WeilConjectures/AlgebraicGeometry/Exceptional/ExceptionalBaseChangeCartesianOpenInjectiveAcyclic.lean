/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Proper acyclicity after extension by zero on a Cartesian open

Source: blueprint `proposition-composition-open-restriction-compactifications-f--5`, Steps 2--4;
Stacks Project, Tag 0F7B (the etale analogue), and proetale Tags 09AE and 09BN
(blueprint: lem-exc-proetale-cartesian-open-injective-acyclic).
-/

open CategoryTheory CategoryTheory.Limits

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

namespace AlgebraicGeometry.Scheme

universe u

set_option autoImplicit false

@[expose] public section

private theorem evaluation_higherDirectImage
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (W : Y.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (Opposite.op W))) (q : ℤ) :
    IsZero (((SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A)) (Opposite.op W)) ⋙
        forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleConstantDerivedDirectImage f A).obj (DerivedCategory.Q.obj K)))) ↔
      IsZero ((ProEt.ringHypercohomology X
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing X A)) ((proEtaleBaseChange f).obj W) q).obj K) := by
  let RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)
  let RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let F := proEtaleConstantModuleDirectImage f A
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.evaluation.{u + 1} RY (Opposite.op W) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let : (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)).PreservesHomology :=
    ProEt.weaklyContractible_evaluation_preservesHomology Y (proEtaleConstantRing Y A) W hW
  let : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)) :=
    (ProEt.affine_weaklyContractible_evaluation_colimits Y (proEtaleConstantRing Y A) W hW).1
  let : PreservesFiniteLimits E := comp_preservesFiniteLimits
    (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W))
    (forget₂ (ModuleCat.{u + 1} (RY.obj.obj (Opposite.op W))) AddCommGrpCat.{u + 1})
  let : E.PreservesEpimorphisms := by
    dsimp only [E]
    infer_instance
  let : E.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels E
  let I := (ProEt.ringModuleResolutionFunctor RX).obj K
  have : I.IsKInjective := (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).1
  have : QuasiIso (ProEt.ringModuleResolutionMap RX K) :=
    (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).2
  let e := F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map (ProEt.ringModuleResolutionMap RX K))) ≪≫
    F.rightDerivedFunctorObjQIso I
  let h := (DerivedCategory.homologyFunctorFactors _ q).app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let c := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q).mapIso
    (HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by intros; rfl) :
      (E.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
        ((ProEt.ringModuleModelEvaluation RX ((proEtaleBaseChange f).obj W)).mapHomologicalComplex
          (.up ℤ)).obj ((ProEt.ringModuleModelResolutionFunctor RX).obj K))
  let : E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc q) := inferInstance
  exact (E.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫ h) ≪≫
    ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc q).mapHomologyIso E).symm ≪≫ c).isZero_iff

private theorem detect (T : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A))
    (h : ∀ (W : T.ProEt), IsAffine W.left →
      (∀ (G H : Sheaf (ProEt.topology T) (Type (u + 1))) (e : G ⟶ H),
        Epi e → Function.Surjective (e.hom.app (Opposite.op W))) →
      Subsingleton ((SheafOfModules.evaluation
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T A)) (Opposite.op W)).obj F)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext V x
  change x = 0
  obtain ⟨I, W, f, hc, ha, hw⟩ :=
    Scheme.ProEt.exists_affine_weaklyContractible_covering_family T V.unop
  apply F.isSheaf.isSeparated _ _ (Precoverage.generate_mem_toGrothendieck hc)
  rintro Z g ⟨_, a, _, ⟨j⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ ((h (W j) (ha j) (hw j)).elim _ _)

end

end AlgebraicGeometry.Scheme
