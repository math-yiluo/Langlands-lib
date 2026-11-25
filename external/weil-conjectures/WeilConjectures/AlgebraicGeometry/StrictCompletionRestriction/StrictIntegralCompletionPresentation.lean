/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
/-! # StrictIntegralCompletionPresentation -/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open WeilConjectures
open CategoryTheory.InternalAbelianSheafModule
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
attribute [local instance] AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def adjunctionStep {C D A : Type*} [Category C] [Category D] [Category A]
    (R : C ⥤ D) (U : D ⥤ C) (T : C ⥤ A) (V : A ⥤ C)
    {F : D ⥤ A} {G : A ⥤ D} (adj : F ⊣ G) (e : R ⋙ F ≅ T) (c : G ⋙ U ≅ V) :
    R ⋙ U ⟶ T ⋙ V :=
  { app := fun K ↦ U.map (adj.unit.app (R.obj K) ≫ G.map (e.hom.app K)) ≫
        c.hom.app (T.obj K)
    naturality := by
      intro K L f
      dsimp only [Functor.comp_map]
      rw [← U.map_comp_assoc]
      have hu := adj.unit.naturality (R.map f)
      dsimp only [Functor.id_map, Functor.comp_map] at hu
      erw [← Category.assoc, hu, Category.assoc, ← G.map_comp, e.hom.naturality]
      simp only [Functor.map_comp, Category.assoc]
      erw [c.hom.naturality] }

private def integralReductionStep (X : Scheme.{u}) (n : ℕ) :
    PrincipalReduction.reductionFunctor l E X (n + 1) ⟶
      PrincipalReduction.reductionFunctor l E X n :=
  adjunctionStep (AdicCompletion.derivedReduction l E X (n + 1))
    (AdicCompletion.restrict l E X (n + 1)) (AdicCompletion.derivedReduction l E X n)
    (AdicCompletion.restrict l E X n)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E X n))
    (AdicCompletion.reductionComp l E X n) (AdicCompletion.restrictComp l E X n)

private theorem integralReductionStep_app (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (integralReductionStep l E X n).app K = AdicCompletion.integralStep l E X K n := rfl

private def scalarEnd (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    End (𝟭 (AdicCompletion.Modules l E X)) :=
  .of (DerivedNakayama.scalarOnModules l E X d)

private theorem functor_conjugate_pow {C D A : Type*}
    [Category C] [Category D] [Category A]
    (G : C ⥤ D) {R : C} {S : D} (e : G.obj R ≅ S)
    (H : D ⥤ A) {U : A} (η : U ≅ H.obj S) (d : End R) (n : ℕ) :
    η.hom ≫ H.map (e.inv ≫ G.map (d ^ n).asHom ≫ e.hom) ≫ η.inv =
      (End.of (η.hom ≫ H.map (e.inv ≫ G.map d.asHom ≫ e.hom) ≫ η.inv) ^ n).asHom := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, End.mul_asHom, G.map_comp, pow_succ, End.mul_asHom, ← ih]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      simp only [← H.map_comp_assoc, Iso.hom_inv_id_assoc]

private theorem scalarOnModules_pow (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (n : ℕ) :
    DerivedNakayama.scalarOnModules l E X (d ^ n) =
      (scalarEnd l E X d ^ n).asHom := by
  exact functor_conjugate_pow (DerivedNakayama.pullback l E X)
    (DerivedNakayama.regularPullbackIso l E X)
    (tensoringLeft (AdicCompletion.Modules l E X))
    (leftUnitorNatIso (AdicCompletion.Modules l E X)).symm d n

private theorem coordinates_cast_congr {A : Type*} [Category A] [Abelian A]
    (M U : CochainComplex A ℤ) (f g : M ⟶ M) (h : f = g)
    (hf : U = CochainComplex.mappingCone f) (hg : U = CochainComplex.mappingCone g)
    (q : ℤ) :
    eqToIso (congrArg (fun K ↦ K.X q) hf) ≪≫ principalConeCoordinates f q =
      eqToIso (congrArg (fun K ↦ K.X q) hg) ≪≫ principalConeCoordinates g q := by
  subst g
  rfl

-- Unpacking the normalized cone and Roos comparison involves many dependent fields.
/-- The canonical integral completion has a Presentation with all strict coordinates
and derived units fixed by the completion-triangle comparison.

Source: blueprint first-reduction Cones paragraph; Stacks Tags 014E and 08TC
(blueprint: lem-sfb-strict-integral-completion-presentation).

Proof: Extract the canonical cone datum and its coordinate, transition, augmentation
and localization equalities from completion_triangle_comparison. Express the scalar
of the datum as an endomorphism of the identity functor. Functoriality and cancellation
of the regular-module comparison identify its powers with the given cone powers.
Use the canonical scalar-extension adjunction to assemble the reduction transitions
as natural transformations. The supplied descent equalities give every reduction
field. The completion and its unit are precisely those of the input theorem. -/
theorem strictIntegralCompletionPresentation (X : Scheme.{u}) :
    ∃ S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X),
      IsIntegral l E X S := by
  classical
  obtain ⟨data, hdata, aug, F, cF, κF, sF, hadd, haug, hcF, hcompare, hrest⟩ :=
    CompletionTriangle.completion_triangle_comparison l E X
  obtain ⟨sD, sR, κR, Φ, hχ, hmap, hT, hj, hjT, hq, htri, hκT, hκj, hrestR⟩ :=
    (hdata (op (Profinite.of (ULift.{u} Unit))) 0 ⟨()⟩).2
  clear hrest hrestR sD sR Φ hjT hq htri
  let tower := CompletionTriangle.tower l E X data
  have hobj (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
      (tower.obj M).asFunctor.obj (op n) = (data.D n).obj M := by
    rfl
  have hstep (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
      (tower.obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op = (data.T n).app M := by
    ext1 q
    change (((Functor.ofOpSequence data.T).map
      (homOfLE (Nat.le_succ n)).op).app M).f q = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  have heval (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
      aug.app M ≫ roosEval (tower.obj M) n = (data.j n).app M := by
    ext1 q
    obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    change p + 1 = q at hp
    subst q
    change (aug.app M).f (p + 1) ≫ (roosEval (tower.obj M) n).f (p + 1) = _
    rw [roosEval_f, ← Category.assoc, ← Category.assoc, haug, biprod.lift_snd]
    exact congrArg (fun f ↦ f.f (p + 1)) (Pi.lift_comp_π
      (fun n : ℕ ↦ (data.j n).app M) n)
  have hcone (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
      (tower.obj M).asFunctor.obj (op n) = CochainComplex.mappingCone
        ((NatTrans.mapHomologicalComplex
          (scalarEnd l E X data.d ^ (n + 1)).asHom (.up ℤ)).app M) := by
    rw [hobj, data.hobj]
    congr 1
    dsimp only [PrincipalReduction.scalar, DerivedNakayama.scalarOnComplex]
    rw [scalarOnModules_pow]
  let S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X) :=
    { scalar := scalarEnd l E X data.d
      tower := tower
      cone := hcone
      coordinates := fun M n q ↦ data.χ n M q
      coordinates_eq := by
        intro M n q
        exact (hχ n M q).trans (coordinates_cast_congr M _ _ _ (by
          ext1 i
          exact congrArg (fun τ ↦ τ.app (M.X i))
            (scalarOnModules_pow l E X data.d (n + 1)))
          (data.hobj n M) (hcone M n) q)
      diagonal := fun f n q ↦ hmap n f q
      transition := by
        intro M n q
        rw [hstep]
        exact hT n M q
      augmentation := aug
      augmentation_zero := by
        intro M p
        have hh := congrArg (fun f ↦ f ≫ biprod.fst) (haug M p)
        exact (Category.assoc _ _ _).symm.trans hh |>.trans (biprod.lift_fst _ _)
      augmentation_level := by
        intro M n p
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc, haug]
        erw [biprod.lift_snd]
        erw [← HomologicalComplex.comp_f, Pi.lift_comp_π]
        exact hj n M (p + 1)
      reduction := PrincipalReduction.reductionFunctor l E X
      reduction_descent := fun n ↦ (κR n).symm
      reduction_step := integralReductionStep l E X
      reduction_unit := fun n ↦
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit
      reduction_step_descent := by
        intro n M
        rw [integralReductionStep_app]
        change AdicCompletion.integralStep l E X (DerivedCategory.Q.obj M) n ≫
          (κR n).inv.app M = _
        rw [hstep]
        apply (cancel_mono ((κR n).hom.app M)).mp
        simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
        have hh := congrArg (fun k ↦ (κR (n + 1)).inv.app M ≫ k) (hκT n M)
        simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
        simpa using hh.symm
      reduction_unit_descent := by
        intro n M
        rw [heval]
        apply (cancel_mono ((κR n).hom.app M)).mp
        simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
        simpa using (hκj n M).symm
      completion := F
      unit := cF
      descent := κF
      unit_descent := hcF }
  refine ⟨S, data, hdata, rfl, rfl, (fun _ ↦ rfl), ?_, hcompare⟩
  intro n K
  exact ⟨heq_of_eq rfl, heq_of_eq (integralReductionStep_app l E X n K)⟩

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
