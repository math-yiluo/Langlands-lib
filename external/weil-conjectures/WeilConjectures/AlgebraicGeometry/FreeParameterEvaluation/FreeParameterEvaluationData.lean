/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceDerivedHom
public import WeilConjectures.AlgebraicGeometry.PointDerivedHom.PointPullbackDerivedHom
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluationData

/-! # Evaluation coherence for free profinite parameters

Source: Stacks Project, Tags 08J7, 08J9 and 07A7; the generator and scalar
adjunction calculations in the node
(blueprint: def-sfb-free-parameter-evaluation-data).

All Hom objects are the recorded closed derived Hom. Gamma is the recorded
ProfiniteFreeSlice.Comparison.gamma. The maps below precede all coherence claims.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The relative parameter scheme from the recorded test-object functor.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
abbrev testScheme (X : Scheme.{u}) (P : Profinite.{u}) := (ProfiniteFreeSlice.test X P).left

/-- Its structural projection.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
abbrev projection (X : Scheme.{u}) (P : Profinite.{u}) := (ProfiniteFreeSlice.test X P).hom

/-- The free parameter in degree zero.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
abbrev parameterD (P : Profinite.{u}) :=
  (DerivedCategory.singleFunctor (PointModules R) 0).obj (freeParameter R P)

/-- F uses the existing closed derived Hom of the condensed module category.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
abbrev functions (P : Profinite.{u}) := ihom (parameterD R P)

/-- H is exactly the source functor of Comparison.gamma.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
abbrev schemeFunctions (X : Scheme.{u}) (P : Profinite.{u}) :=
  (CondensedRing.derivedHom R.X X).obj (op (ProfiniteFreeSlice.derivedFree R.X X P))

/-- Identify the two standard degree-zero pullback presentations.
Source: exact termwise pullback (blueprint: def-sfb-free-parameter-evaluation-data). -/
def pulledParameter (X : Scheme.{u}) (P : Profinite.{u}) :
    (pointPullD R X).obj (parameterD R P) ≅ ProfiniteFreeSlice.derivedFree R.X X P :=
  (pointPull R X).mapDerivedCategorySingleFunctor 0 |>.app (freeParameter R P)

/-- Beta is the transpose of pulled-back evaluation, followed by the canonical
single-complex identification, with no use of c or gamma.
Source: Stacks 08J9 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def beta (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) :
    (pointPullD R X).obj ((functions R P).obj N) ⟶
      (schemeFunctions R X P).obj ((pointPullD R X).obj N) :=
  PointDerivedHom.comparison R.X X (parameterD R P) N ≫
    (MonoidalClosed.pre (pulledParameter R X P).inv).app ((pointPullD R X).obj N)

/-- An actual regular-module map from a compatible family of sections: apply the
section-module equivalence to the ordinary unitHomEquiv, whose map sends r to r s.
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-evaluation-data). -/
def sectionMap (X : Scheme.{u}) (M : Modules R X)
    (s : ((CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology X) (condensedRingObj R.X X)).obj M).sections) :
    𝟙_ (Modules R X) ⟶ M :=
  (CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (Scheme.ProEt.topology X) (condensedRingObj R.X X)).preimage
      (SheafOfModules.unitHomEquiv _ |>.symm s)

/-- The universal P-section from the unit at id_P, restricted along its graph.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def universalSection (X : Scheme.{u}) (P : Profinite.{u}) :
    ((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj.obj
      (op (Scheme.ProEt.mk (𝟙 (testScheme X P)))) :=
  (((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj.map
    (MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst _ _) (𝟙 _)
        (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _)).op)
    ((((ProfiniteFreeSlice.abelianAdjunction (testScheme X P)).unit.app
      (freeParameter R P).X).hom.app (op P)) (ProfiniteFreeSlice.pointGenerator R.X P))

/-- The terminal arrow of the small pro-etale site.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def terminalArrow {X : Scheme.{u}} (V : X.ProEt) : V ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk V.hom (Category.comp_id V.hom)

/-- The universal generator as a section of the section-module presheaf.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def universalValue (X : Scheme.{u}) (P : Profinite.{u})
    (V : (testScheme X P).ProEtᵒᵖ) :
    (((CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology (testScheme X P)) (condensedRingObj R.X (testScheme X P))).obj
      ((pointPull R (testScheme X P)).obj (freeParameter R P))).val.obj V) :=
  (((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj.map
    (terminalArrow V.unop).op) (universalSection R X P)

/-- Restriction compatibility of the tautological generator.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data).
Proof: compose the terminal arrow with the given test arrow and use uniqueness of
terminal arrows. Presheaf functoriality identifies the two restrictions. -/
theorem universalSection_compatible (X : Scheme.{u}) (P : Profinite.{u})
    {V W : (testScheme X P).ProEtᵒᵖ} (f : V ⟶ W) :
    (((CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor
      (Scheme.ProEt.topology (testScheme X P)) (condensedRingObj R.X (testScheme X P))).obj
      ((pointPull R (testScheme X P)).obj (freeParameter R P))).val.map f)
        (universalValue R X P V) = universalValue R X P W := by
  let F := ((pointPull R (testScheme X P)).obj (freeParameter R P)).X.obj
  change F.map f (F.map (terminalArrow V.unop).op (universalSection R X P)) =
    F.map (terminalArrow W.unop).op (universalSection R X P)
  rw [← ConcreteCategory.comp_apply, ← F.map_comp]
  have h : (terminalArrow V.unop).op ≫ f = (terminalArrow W.unop).op := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change f.unop.left ≫ V.unop.hom = W.unop.hom
    exact MorphismProperty.Over.w f.unop
  rw [h]

/-- The universal generator, constructed by the ordinary regular-module adjunction.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def parameterGenerator (X : Scheme.{u}) (P : Profinite.{u}) :
    𝟙_ (Modules R (testScheme X P)) ⟶
      (pointPull R (testScheme X P)).obj (freeParameter R P) :=
  sectionMap R (testScheme X P) _
    ⟨universalValue R X P, fun f ↦ universalSection_compatible R X P f⟩

/-- The same generator in the ordinary derived category, using the fixed unit and
single-complex pullback identifications.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def generatorD (X : Scheme.{u}) (P : Profinite.{u}) :
    𝟙_ (DerivedCategory (Modules R (testScheme X P))) ⟶
      (pointPullD R (testScheme X P)).obj (parameterD R P) :=
  (DerivedCategory.singleFunctorObjUnitIso (Modules R (testScheme X P))).inv ≫
    (DerivedCategory.singleFunctor (Modules R (testScheme X P)) 0).map
      (parameterGenerator R X P) ≫
    ((pointPull R (testScheme X P)).mapDerivedCategorySingleFunctor 0).inv.app
      (freeParameter R P)

/-- Derived evaluation on the universal generator: insert it in the first tensor
factor, use the canonical K-flat tensor comparison, then pull back the closed counit.
Source: Stacks 08J7, 08J9 (blueprint: def-sfb-free-parameter-evaluation-data). -/
def derivedEvaluation (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) :
    (pointPullD R (testScheme X P)).obj ((functions R P).obj N) ⟶
      (pointPullD R (testScheme X P)).obj N :=
  (λ_ _).inv ≫ (generatorD R X P ⊗ₘ 𝟙 _) ≫
    (PointDerivedHom.tensorComparison R.X (testScheme X P)
      (parameterD R P) ((functions R P).obj N)).inv ≫
    (pointPullD R (testScheme X P)).map ((ihom.ev (parameterD R P)).app N)

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
