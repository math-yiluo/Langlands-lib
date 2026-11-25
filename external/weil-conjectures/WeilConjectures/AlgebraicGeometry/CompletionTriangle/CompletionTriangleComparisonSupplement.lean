/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.PrincipalReductionDerivedNormalization
public import WeilConjectures.AlgebraicGeometry.PrincipalConeTensorNormalization
public import WeilConjectures.Algebra.Homology.ReductionIsoShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
public import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Localization.Predicate
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
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Exact principal completion and its canonical triangle map

Source: blueprint main-20261015, chap-The-pro-etale-site,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`,
Cones paragraph and shifts sentence; Stacks Tag 05RU
(blueprint: lem-pe-completion-triangle-comparison).

## Main definitions and statement

* `CompletionTriangle.tower` assembles the specified strict principal reductions.
* `CompletionTriangle.complexCompletion` applies the existing Roos functor.
* `CompletionTriangle.completion_triangle_comparison` gives the augmented exact descent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CochainComplex Pretriangulated
set_option backward.isDefEq.respectTransparency.types false
universe vT
namespace ScalarCone
variable {A : Type u} [Category.{vT} A] [Abelian A] [IsGrothendieckAbelian.{vT} A]
  [HasDerivedCategory.{vT} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {R : Type*} [CommRing R] [Linear R A] [MonoidalLinear R A]
private local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
variable (P : CochainComplex A ℤ) (r : R) {B : A} (p : 𝟙_ A ⟶ B)
  (w : (r • 𝟙 (𝟙_ A)) ≫ p = 0)
private def unit : P ⟶ ((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex
    ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map p) (.up ℤ)).app P
include w in
omit [IsGrothendieckAbelian.{vT} A] [HasDerivedCategory A] [MonoidalClosed A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem scalar_unit_zero : (r • 𝟙 P) ≫ unit P p = 0 := by
  ext1 q
  change (r • 𝟙 (P.X q)) ≫ ((ρ_ (P.X q)).inv ≫ P.X q ◁ p) = 0
  have hh : (r • 𝟙 (P.X q ⊗ 𝟙_ A)) ≫ P.X q ◁ p = 0 := by
    calc
      _ = r • (P.X q ◁ p) := by simp
      _ = P.X q ◁ ((r • 𝟙 (𝟙_ A)) ≫ p) := by simp
      _ = 0 := by simp only [w, MonoidalPreadditive.whiskerLeft_zero]
  simpa [Linear.smul_comp, Linear.comp_smul, Category.assoc] using
    congrArg (fun f ↦ (ρ_ (P.X q)).inv ≫ f) hh
private def simpleDesc : mappingCone (r • 𝟙 P) ⟶
    ((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P :=
  mappingCone.descShortComplex (ShortComplex.mk _ _ (scalar_unit_zero P r p w))
omit [IsGrothendieckAbelian.{vT} A] [HasDerivedCategory A]
  [Abelian.HasFunctorialFlatResolution A] in
private theorem flat_shortExact
    (hs : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)
    (hP : ∀ q, ObjectProperty.flat (P.X q)) :
    (ShortComplex.mk _ _ (scalar_unit_zero P r p w)).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro q
  have : PreservesFiniteLimits (tensorLeft (P.X q)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).mp (hP q)
  have : PreservesFiniteColimits (tensorLeft (P.X q)) := inferInstance
  have hsq := hs.map_of_exact (tensorLeft (P.X q))
  change (ShortComplex.mk (r • 𝟙 (P.X q))
    ((ρ_ (P.X q)).inv ≫ P.X q ◁ p) _).ShortExact
  apply ShortComplex.shortExact_of_iso (S₁ := (ShortComplex.mk _ _ w).map
    (tensorLeft (P.X q))) _ hsq
  refine ShortComplex.isoMk (ρ_ (P.X q)) (ρ_ (P.X q)) (Iso.refl _) ?_ ?_
  · change (ρ_ (P.X q)).hom ≫ (r • 𝟙 (P.X q)) =
      (P.X q ◁ (r • 𝟙 (𝟙_ A))) ≫ (ρ_ (P.X q)).hom
    simp only [MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  · dsimp [unit]
    simp
omit [Linear R A] [MonoidalLinear R A] [HasDerivedCategory A] in
private theorem tensor_quasiIso {P P' : CochainComplex A ℤ} (f : P ⟶ P')
    [QuasiIso f] (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P') (B : A) :
    QuasiIso (((tensorRight B).mapHomologicalComplex (.up ℤ)).map f) := by
  have (Y : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj Y) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z) (by intros; simp [curriedTensor]))
  have ht := MorphismProperty.whiskerRight_of_kFlat
    (HomologicalComplex.quasiIso A (.up ℤ)) f
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance) hP hP'
    ((HomologicalComplex.single A (.up ℤ) 0).obj B)
  exact ((HomologicalComplex.quasiIso A (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (map₂HomologicalComplexFlipObjSingleIso (curriedTensor A) B)
      (Arrow.mk f))).1 ht

omit [IsGrothendieckAbelian.{vT} A] [HasDerivedCategory A] [MonoidalClosed A]
  [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A] in
private theorem simpleDesc_natural {P P' : CochainComplex A ℤ} (f : P ⟶ P') :
    mappingCone.map (r • 𝟙 P) (r • 𝟙 P') f f (by simp) ≫ simpleDesc P' r p w =
      simpleDesc P r p w ≫ ((tensorRight B).mapHomologicalComplex (.up ℤ)).map f := by
  apply mappingCone.map_descShortComplex
    (ShortComplex.mk _ _ (scalar_unit_zero P r p w))
    (ShortComplex.mk _ _ (scalar_unit_zero P' r p w))
    (ShortComplex.homMk f f _ (by simp) (by
      exact (NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso A).inv ≫ (tensoringRight A).map p) (.up ℤ)).naturality f))

-- First calculate on a flat replacement, then transfer to every K-flat complex.
private theorem simpleDesc_quasiIso
    (hs : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
    QuasiIso (simpleDesc P r p w) := by
  obtain ⟨P', f, hf, hflat, hP'⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  have : QuasiIso f := hf
  have hd : QuasiIso (simpleDesc P' r p w) :=
    mappingCone.quasiIso_descShortComplex (flat_shortExact P' r p w hs hflat)
  have ht := tensor_quasiIso f hP' hP B
  let m := mappingCone.map (r • 𝟙 P') (r • 𝟙 P) f f
    (by simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id])
  have hm : QuasiIso m :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
      (isIso₃_of_isIso₁₂
        (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap
          (r • 𝟙 P') (r • 𝟙 P) f f
            (by simp only [Linear.smul_comp, Linear.comp_smul,
              Category.id_comp, Category.comp_id])))
        (DerivedCategory.mappingCone_triangle_distinguished _)
        (DerivedCategory.mappingCone_triangle_distinguished _)
        (inferInstance : IsIso (DerivedCategory.Q.map f))
        (inferInstance : IsIso (DerivedCategory.Q.map f)))
  have hc : QuasiIso (m ≫ simpleDesc P r p w) := by
    dsimp only [m]
    rw [simpleDesc_natural]
    infer_instance
  exact (quasiIso_iff_comp_left m (simpleDesc P r p w)).mp hc

private theorem simpleDesc_quasiIso_of_eq
    (hs : (ShortComplex.mk (r • 𝟙 (𝟙_ A)) p w).ShortExact)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (f : P ⟶ P) (hf : f = r • 𝟙 P) (hw : f ≫ unit P p = 0) :
    QuasiIso (mappingCone.descShortComplex (ShortComplex.mk f (unit P p) hw)) := by
  subst hf
  exact simpleDesc_quasiIso P r p w hs hP

end ScalarCone

namespace CoefficientCone
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.DerivedNakayama
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
private theorem quotientUnit_eq (n : ℕ) :
    quotientUnit l E n = reductionHom l E (n + 1) := by
  apply Mod.Hom.ext
  rfl
private theorem scalar_eq (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X) : data.d = uniformizerEnd l E := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  apply End.ext
  apply Mod.Hom.ext
  apply (sheafToPresheaf _ _).map_injective
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  ext a
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  exact ((hdata S a s).1).trans (uniformizerEnd_apply l E S a s).symm
private theorem coefficient_ses (n : ℕ) :
    ∃ w : (unitEndOnX l E X (uniformizerEnd l E ^ (n + 1)) •
        𝟙 (𝟙_ (Modules l E X))) ≫ finiteUnit l E X n = 0,
      (ShortComplex.mk _ _ w).ShortExact := by
  let e := regularPullbackIso l E X
  let d := (pullback l E X).map (uniformizerEnd l E ^ (n + 1)).asHom
  let p := (pullback l E X).map (reductionHom l E (n + 1))
  let S := (ShortComplex.mk (uniformizerEnd l E ^ (n + 1)).asHom (reductionHom l E (n + 1))
    (reduction_zero l E (n + 1))).map (pullback l E X)
  have hs : S.ShortExact := (pointResolution l E (n + 1)).map_of_exact (pullback l E X)
  have hscalar : unitEndOnX l E X (uniformizerEnd l E ^ (n + 1)) •
      𝟙 (𝟙_ (Modules l E X)) = e.inv ≫ d ≫ e.hom := by
    rw [UnitScalar.smul_eq, unitEndAction_unit, Category.comp_id]
    rfl
  have hp : finiteUnit l E X n = e.inv ≫ p := by
    dsimp only [finiteUnit, p, e]
    rw [quotientUnit_eq]
  have w : (unitEndOnX l E X (uniformizerEnd l E ^ (n + 1)) •
      𝟙 (𝟙_ (Modules l E X))) ≫ finiteUnit l E X n = 0 := by
    rw [hscalar, hp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change e.inv ≫ S.f ≫ S.g = 0
    rw [S.zero, comp_zero]
  refine ⟨w, ?_⟩
  apply ShortComplex.shortExact_of_iso (S₁ := S) _ hs
  refine ShortComplex.isoMk e e (Iso.refl _) ?_ ?_
  · dsimp only []
    change e.hom ≫ (unitEndOnX l E X (uniformizerEnd l E ^ (n + 1)) •
      𝟙 (𝟙_ (Modules l E X))) = d ≫ e.hom
    rw [hscalar]
    simp
  · dsimp only []
    change e.hom ≫ finiteUnit l E X n = p ≫ 𝟙 _
    rw [hp]
    simp
private theorem coneToTensor_zero
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    PrincipalReduction.scalar l E X data.d n P ≫ levelUnit l E X P n = 0 := by
  dsimp only [PrincipalReduction.scalar]
  rw [scalar_eq l E X data hdata, scalarOnComplex_eq]
  exact ScalarCone.scalar_unit_zero P _ (finiteUnit l E X n)
    (coefficient_ses l E X n).choose
private def coneToTensor (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X) (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (data.D n).obj P ⟶ (level l E X n).obj P :=
  (eqToIso (data.hobj n P)).hom ≫ mappingCone.descShortComplex
    (ShortComplex.mk _ _ (coneToTensor_zero l E X data hdata P n))
private theorem coneToTensor_quasiIso (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X) (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P) (n : ℕ) :
    QuasiIso (coneToTensor l E X data hdata P n) := by
  have hs : PrincipalReduction.scalar l E X data.d n P =
      unitEndOnX l E X (uniformizerEnd l E ^ (n + 1)) • 𝟙 P := by
    dsimp only [PrincipalReduction.scalar]
    rw [scalar_eq l E X data hdata, scalarOnComplex_eq]
  have hh := ScalarCone.simpleDesc_quasiIso_of_eq P _ (finiteUnit l E X n)
    (coefficient_ses l E X n).choose (coefficient_ses l E X n).choose_spec hP
    _ hs (coneToTensor_zero l E X data hdata P n)
  dsimp only [coneToTensor]
  have : QuasiIso (mappingCone.descShortComplex
      (ShortComplex.mk _ _ (coneToTensor_zero l E X data hdata P n))) := hh
  infer_instance
private theorem cone_projection_eqToIso {A : Type*} [Category A] [Abelian A]
    {P : CochainComplex A ℤ} {f g : P ⟶ P} (h : f = g) (q : ℤ) :
    (eqToIso (congrArg (fun k : P ⟶ P ↦ mappingCone k) h)).hom.f q ≫
      (mappingCone.snd g).v q q (add_zero q) =
        (principalConeCoordinates f q).hom ≫ biprod.fst := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.id_comp]
  simp only [principalConeCoordinates, Iso.trans_hom, Category.assoc,
    biprod.braiding_hom, biprod.lift_fst]
  apply mappingCone.ext_from f (q + 1) q rfl
  · rw [mappingCone.inl_v_snd_v]
    change 0 = HomologicalComplex.homotopyCofiber.inlX f (q + 1) q rfl ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl).hom ≫ biprod.snd
    simp
  · rw [mappingCone.inr_f_snd_v]
    change 𝟙 _ = HomologicalComplex.homotopyCofiber.inrX f q ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl).hom ≫ biprod.snd
    simp

private theorem cone_transport_coordinates {A : Type*} [Category A] [Abelian A]
    {K P L : CochainComplex A ℤ} {f g : P ⟶ P} (hK : K = mappingCone f) (hf : f = g)
    (τ : mappingCone g ⟶ L) (q : ℤ) (z : P.X q ⟶ L.X q)
    (hτ : τ.f q = (mappingCone.snd g).v q q (add_zero q) ≫ z) :
    ((eqToIso hK).hom ≫
      (eqToIso (congrArg (fun k : P ⟶ P ↦ mappingCone k) hf)).hom ≫ τ).f q =
      (eqToIso (congrArg (fun K ↦ K.X q) hK) ≪≫ principalConeCoordinates f q).hom ≫
        biprod.fst ≫ z := by
  subst hK
  subst hf
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Iso.refl_trans]
  rw [hτ]
  have hp := cone_projection_eqToIso (rfl : f = f) q
  simp only [eqToIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.id_comp] at hp
  rw [hp, Category.assoc]
private theorem coneToTensor_coordinates
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hχ : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (PrincipalReduction.scalar l E X data.d n M) q)
    (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) (q : ℤ) :
    (coneToTensor l E X data hdata P n).f q =
      (data.χ n P q).hom ≫ biprod.fst ≫ (levelUnit l E X P n).f q := by
  have he : (mappingCone.descShortComplex
      (ShortComplex.mk _ _ (coneToTensor_zero l E X data hdata P n))).f q =
        (mappingCone.snd (PrincipalReduction.scalar l E X data.d n P)).v q q (add_zero q) ≫
          (levelUnit l E X P n).f q := by
    dsimp only [mappingCone.descShortComplex]
    rw [mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
    simp only [HomComplex.Cochain.zero_v, comp_zero, zero_add]
  rw [hχ]
  have ht := cone_transport_coordinates
    (K := (data.D n).obj P) (P := P) (L := (level l E X n).obj P)
    (data.hobj n P) (rfl : PrincipalReduction.scalar l E X data.d n P = _)
    (mappingCone.descShortComplex
      (ShortComplex.mk _ _ (coneToTensor_zero l E X data hdata P n)))
    q ((levelUnit l E X P n).f q) he
  simpa only [coneToTensor, eqToIso_refl, Iso.refl_hom, Category.id_comp] using ht

private theorem coneToTensor_step
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hχ : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (PrincipalReduction.scalar l E X data.d n M) q)
    (hT : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      ((data.T n).app M).f q ≫ (data.χ n M q).hom =
        (data.χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E X data.d M).f (q + 1)))
    (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (data.T n).app P ≫ coneToTensor l E X data hdata P n =
      coneToTensor l E X data hdata P (n + 1) ≫ levelStep l E X P n := by
  ext1 q
  simp only [HomologicalComplex.comp_f, coneToTensor_coordinates l E X data hdata hχ,
    Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hT]
  simp only [Category.assoc, biprod.map_fst, Category.id_comp]
  rw [← HomologicalComplex.comp_f, levelUnit_step]
private theorem coneToTensor_unit
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hχ : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (PrincipalReduction.scalar l E X data.d n M) q)
    (hj : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      ((data.j n).app M).f q ≫ (data.χ n M q).hom = biprod.inl)
    (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (data.j n).app P ≫ coneToTensor l E X data hdata P n = levelUnit l E X P n := by
  ext1 q
  simp only [HomologicalComplex.comp_f, coneToTensor_coordinates l E X data hdata hχ]
  rw [← Category.assoc, ← Category.assoc, hj]
  simp
end CoefficientCone

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex RoosConeCalculus
namespace RoosCompletion
attribute [local instance] AlgebraicGeometry.ProEtale.AdicCompletion.modulesNatProducts
  AlgebraicGeometry.ProEtale.AdicCompletion.complexNatProducts
  AlgebraicGeometry.ProEtale.AdicCompletion.complexNatLimit

variable {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
private def signedX (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    (roosF.obj N).X q ≅ (roosP N).X q ⊞ (roosP N).X (q - 1) where
  hom := biprod.lift (v N q) (-ucoord N q (q - 1) rfl)
  inv := biprod.fst ≫ (mappingCocone.inl (roosU N)).v q q (by omega) -
    biprod.snd ≫ (mappingCocone.inr (roosU N)).1.v (q - 1) q (by omega)
  hom_inv_id := by
    change (biprod.lift ((mappingCocone.fst (roosU N)).f q)
      (-ucoord N q (q - 1) rfl)) ≫ _ = 𝟙 _
    simp only [Preadditive.comp_sub, ← Category.assoc, biprod.lift_fst,
      biprod.lift_snd, Preadditive.neg_comp, sub_neg_eq_add]
    exact mappingCocone.id_X (roosU N) q (q - 1) (by omega)
  inv_hom_id := by
    change (biprod.fst ≫ (mappingCocone.inl (roosU N)).v q q (by omega) -
      biprod.snd ≫ (mappingCocone.inr (roosU N)).1.v (q - 1) q (by omega)) ≫
      biprod.lift ((mappingCocone.fst (roosU N)).f q)
        (-ucoord N q (q - 1) rfl) = 𝟙 _
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [ucoord, Preadditive.sub_comp, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
open AlgebraicGeometry.ProEtale.AdicCompletion
private def tensorTower (P : CochainComplex (Modules l E X) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ where
  X q := (Functor.ofOpSequence (X := fun n ↦ (level l E X n).obj P) (levelStep l E X P)) ⋙
    HomologicalComplex.eval (Modules l E X) (.up ℤ) q
  d q r :=
    { app n := ((level l E X n.unop).obj P).d q r
      naturality _ _ f :=
        ((Functor.ofOpSequence (X := fun n ↦ (level l E X n).obj P)
          (levelStep l E X P)).map f).comm q r }
  shape q r h := NatTrans.ext (funext (fun n ↦
    ((level l E X n.unop).obj P).shape q r h))
  d_comp_d' q r t _ _ := NatTrans.ext (funext (fun n ↦
    ((level l E X n.unop).obj P).d_comp_d q r t))
private theorem tower_step (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (tensorTower l E X P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      levelStep l E X P n := by
  ext1 q
  change ((Functor.ofOpSequence (X := fun n ↦ (level l E X n).obj P) (levelStep l E X P)).map
    (homOfLE (Nat.le_succ n)).op).f q = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
private theorem level_eq (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (tensorTower l E X P).asFunctor.obj (op n) = (level l E X n).obj P := rfl
private def productIso (P : CochainComplex (Modules l E X) ℤ) :
    roosP (tensorTower l E X P) ≅ product l E X P :=
  Pi.mapIso (fun n ↦ eqToIso (level_eq l E X P n))
@[reassoc]
private theorem productIso_π (P : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    (productIso l E X P).hom ≫ Pi.π (fun n ↦ (level l E X n).obj P) n =
      Pi.π (fun n ↦ (tensorTower l E X P).asFunctor.obj (op n)) n ≫
        (eqToIso (level_eq l E X P n)).hom :=
  Pi.mapIso_hom_π _ n
private theorem U_eq (P : CochainComplex (Modules l E X) ℤ) :
    roosU (tensorTower l E X P) ≫ (productIso l E X P).hom =
      (productIso l E X P).hom ≫ oneSubShift l E X P := by
  apply Pi.hom_ext
  intro n
  have hu := (towerTransitionEndomorphism_eq_iff
    (K := fun n : ℕ ↦ (tensorTower l E X P).asFunctor.obj (op n))
    (fun n ↦ (tensorTower l E X P).asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
  have hv := (towerTransitionEndomorphism_eq_iff
    (K := fun n : ℕ ↦ (level l E X n).obj P) (levelStep l E X P) _).mp rfl n
  rw [Category.assoc, productIso_π]
  change roosU (tensorTower l E X P) ≫ (_ ≫ _) = _
  rw [← Category.assoc, hu]
  change _ = (productIso l E X P).hom ≫
    (oneSubShift l E X P ≫ Pi.π (fun n ↦ (level l E X n).obj P) n)
  change _ = (productIso l E X P).hom ≫
    (towerTransitionEndomorphism (levelStep l E X P) ≫ _)
  rw [hv]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    productIso_π, productIso_π_assoc]
  simp only [tower_step, eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
@[reassoc]
private theorem hom_transport {B : Type*} [Category B] [HasZeroMorphisms B]
    {K L : CochainComplex B ℤ} (f : K ⟶ L) {i j : ℤ} (h : i = j) :
    f.f i ≫ eqToHom (congrArg L.X h) = eqToHom (congrArg K.X h) ≫ f.f j := by
  subst h
  simp
@[reassoc]
private theorem u_transport (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (p q q' : ℤ) (hp : p - 1 = q) (h : q = q') :
    ucoord N p q hp ≫ eqToHom (congrArg (roosP N).X h) =
      ucoord N p q' (hp.trans h) := by
  subst h
  simp
@[reassoc]
private theorem d_transport {B : Type*} [Category B] [HasZeroMorphisms B]
    (K : CochainComplex B ℤ) (p : ℤ) {q q' : ℤ} (h : q = q') :
    K.d p q ≫ eqToHom (congrArg K.X h) = K.d p q' := by
  subst h
  simp
-- The two Roos conventions differ by negating the shifted product coordinate.
private def signedIso (P : CochainComplex (Modules l E X) ℤ) :
    roosF.obj (tensorTower l E X P) ≅ roos l E X P := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦ signedX _ q ≪≫ biprod.mapIso
    (HomologicalComplex.Hom.isoApp (productIso l E X P) q)
    (HomologicalComplex.Hom.isoApp (productIso l E X P) (q - 1))) ?_
  intro q r h
  obtain rfl : q + 1=r := h
  let N := tensorTower l E X P
  let e := productIso l E X P
  have hv := (differential_coordinates N q).1
  have hu := (differential_coordinates N q).2
  have he := congrArg (fun f ↦ f.f q) (U_eq l E X P)
  have hd := e.hom.comm (q - 1) q
  simp only [HomologicalComplex.comp_f] at he
  apply biprod.hom_ext
  · simp only [Iso.trans_hom, signedX, biprod.mapIso_hom,
      HomologicalComplex.Hom.isoApp_hom, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc]
    simp only [roos, CochainComplex.of_d]
    simp only [roosD, biprod.lift_fst, biprod.lift_fst_assoc,
      biprod.map_fst_assoc, biprod.lift_fst_assoc]
    change (v N q ≫ e.hom.f q) ≫ (product l E X P).d q (q + 1) =
      (roosF.obj N).d q (q + 1) ≫ v N (q + 1) ≫ e.hom.f (q + 1)
    rw [← Category.assoc, hv, Category.assoc]
    exact congrArg (fun f ↦ v N q ≫ f) (e.hom.comm q (q + 1))
  · simp only [Iso.trans_hom, signedX, biprod.mapIso_hom,
      HomologicalComplex.Hom.isoApp_hom, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc]
    simp only [roos, CochainComplex.of_d]
    simp only [roosD, biprod.lift_snd]
    simp only [Preadditive.comp_sub, biprod.map_fst_assoc,
      biprod.map_snd_assoc, biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    change (v N q ≫ e.hom.f q ≫ (oneSubShift l E X P).f q ≫
        eqToHom (congrArg (product l E X P).X (Int.add_sub_cancel q 1).symm)) -
        (-ucoord N q (q - 1) rfl) ≫ e.hom.f (q - 1) ≫ (product l E X P).d (q - 1) (q + 1-1) =
      (roosF.obj N).d q (q + 1) ≫
        (-ucoord N (q + 1) (q + 1-1) rfl) ≫ e.hom.f (q + 1-1)
    have hq : q + 1-1=q := by omega
    apply (cancel_mono (eqToHom (congrArg (product l E X P).X hq))).mp
    simp only [Preadditive.sub_comp, Category.assoc, Preadditive.neg_comp,
      Preadditive.comp_neg, eqToHom_trans]
    rw [hom_transport e.hom hq, d_transport (product l E X P) (q - 1) hq]
    rw [u_transport_assoc N (q + 1) (q + 1-1) q rfl hq]
    simp only [eqToHom_refl, Category.comp_id]
    rw [reassoc_of% hu]
    simp only [Preadditive.neg_comp, Preadditive.sub_comp,
      neg_sub, sub_neg_eq_add, Category.assoc]
    rw [← he, hd]
private theorem signedIso_f (P : CochainComplex (Modules l E X) ℤ) (q : ℤ) :
    (signedIso l E X P).hom.f q =
      (signedX (tensorTower l E X P) q).hom ≫
        biprod.map ((productIso l E X P).hom.f q)
          ((productIso l E X P).hom.f (q - 1)) := rfl
private def tensorCone (P : CochainComplex (Modules l E X) ℤ) :
    Cone (tensorTower l E X P).asFunctor where
  pt := P
  π := NatTrans.ofOpSequence (levelUnit l E X P) (fun n ↦ by
    change levelUnit l E X P n = _
    rw [tower_step]
    exact (levelUnit_step l E X P n).symm)
private theorem augmentation_sign (P : CochainComplex (Modules l E X) ℤ) :
    RoosConeCalculus.augmentation (tensorCone l E X P) ≫ (signedIso l E X P).hom =
      augmentation l E X P := by
  ext1 q
  simp only [HomologicalComplex.comp_f, signedIso_f, signedX,
    AlgebraicGeometry.ProEtale.AdicCompletion.augmentation]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    change (RoosConeCalculus.augmentation (tensorCone l E X P)).f q ≫
      (v (tensorTower l E X P) q ≫ (productIso l E X P).hom.f q) =
        (unitProduct l E X P).f q
    rw [← Category.assoc, (augment_coordinates (tensorCone l E X P) q).1,
      ← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, productIso_π, ← Category.assoc, Pi.lift_comp_π]
    simp only [unitProduct, Pi.lift_comp_π, eqToIso_refl, Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    rw [← Category.assoc, Preadditive.comp_neg, augment_u, neg_zero, zero_comp]

end RoosCompletion

set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.ProEtale.CompletionTriangle

open AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Degreewise assembly of the existing strict reduction tower into a complex of towers.
Source: blueprint first-reduction proof, strict towers in the Cones paragraph
(blueprint: lem-pe-completion-triangle-comparison). -/
def tower (data : PrincipalReductionConeData l E X) : CochainComplex (Modules l E X) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ where
  obj M :=
    { X := fun q ↦ (Functor.ofOpSequence (data.T)).flip.obj M ⋙
        HomologicalComplex.eval (Modules l E X) (.up ℤ) q
      d := fun q r ↦
        { app := fun n ↦ ((data.D n.unop).obj M).d q r
          naturality := fun _n _m f ↦
            (((Functor.ofOpSequence (data.T)).map f).app M).comm q r }
      shape := fun q r h ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).obj M).shape q r h))
      d_comp_d' := fun q r t _ _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).obj M).d_comp_d q r t)) }
  map f :=
    { f := fun q ↦
        { app := fun n ↦ ((data.D n.unop).map f).f q
          naturality := fun _n _m g ↦
            congrArg (fun h ↦ h.f q)
              (((Functor.ofOpSequence (data.T)).map g).naturality f).symm }
      comm' := fun q r _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((data.D n.unop).map f).comm q r)) }
  map_id M := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((data.D n.unop).map_id M)))))
  map_comp f g := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((data.D n.unop).map_comp f g)))))

/-- The actual composite of the principal tower and the published strict Roos functor.
Source: blueprint first-reduction proof, Cones paragraph
(blueprint: lem-pe-completion-triangle-comparison). -/
abbrev complexCompletion (data : PrincipalReductionConeData l E X) :
    CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ :=
  tower l E X data ⋙ roosF

open scoped CategoryTheory.Obj in
private theorem countableExact : CountableAB4Star (Modules l E X) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

private theorem tower_additive (data : PrincipalReductionConeData l E X)
    (hmap : ∀ n {M N : CochainComplex (Modules l E X) ℤ} (f : M ⟶ N) (q : ℤ),
      ((data.D n).map f).f q ≫ (data.χ n N q).hom =
        (data.χ n M q).hom ≫ biprod.map (f.f q) (f.f (q + 1))) :
    (tower l E X data).Additive := by
  constructor
  intro M N f g
  ext1 q
  apply NatTrans.ext
  funext n
  apply (cancel_mono (data.χ n.unop N q).hom).mp
  change ((data.D n.unop).map (f + g)).f q ≫ _ =
    (((data.D n.unop).map f).f q + ((data.D n.unop).map g).f q) ≫ _
  simp only [Preadditive.add_comp, hmap, HomologicalComplex.add_f_apply]
  rw [← Preadditive.comp_add]
  congr 1
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

private theorem descended_additive
    (G : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
    [G.Additive]
    (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
    (κ : DerivedCategory.Q ⋙ F ≅ G ⋙ DerivedCategory.Q) : F.Additive := by
  have : (DerivedCategory.Q ⋙ F).Additive := Functor.additive_of_iso κ.symm
  have : ((HomotopyCategory.quotient (Modules l E X) (.up ℤ)) ⋙
      (DerivedCategory.Qh ⋙ F)).Additive :=
    Functor.additive_of_iso
      ((Functor.isoWhiskerRight
        (DerivedCategory.quotientCompQhIso (Modules l E X)) F).symm ≪≫
        Functor.associator _ _ _)
  have : (DerivedCategory.Qh ⋙ F).Additive :=
    Functor.additive_of_full_essSurj_comp
      (HomotopyCategory.quotient (Modules l E X) (.up ℤ)) _
  exact (Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic (Modules l E X)).trW F).mpr inferInstance

private def strictAugmentation (data : PrincipalReductionConeData l E X)
    (h : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (M : CochainComplex (Modules l E X) ℤ) :
    M ⟶ (complexCompletion l E X data).obj M :=
  roosAugment (X := (tower l E X data).obj M) (fun n ↦ (data.j n).app M)
    (fun n ↦ by
      have he : ((tower l E X data).obj M).asFunctor.map
          (homOfLE (Nat.le_succ n)).op = (data.T n).app M := by
        ext1 q
        change (((Functor.ofOpSequence data.T).map
          (homOfLE (Nat.le_succ n)).op).app M).f q = _
        rw [Functor.ofOpSequence_map_homOfLE_succ]
      rw [he]
      exact h n M)

private theorem strictAugmentation_coordinates (data : PrincipalReductionConeData l E X)
    (h : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (M : CochainComplex (Modules l E X) ℤ) (p : ℤ) :
    (strictAugmentation l E X data h M).f (p + 1) ≫
        (roosχ ((tower l E X data).obj M) p).hom =
      biprod.lift 0 ((Pi.lift
        (f := fun n : ℕ ↦ ((tower l E X data).obj M).asFunctor.obj (op n))
        (fun n : ℕ ↦ (data.j n).app M)).f (p + 1)) :=
  roosAugment_χ _ _ p

private def strictAugmentationNat (data : PrincipalReductionConeData l E X)
    (h : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M) :
    𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ complexCompletion l E X data where
  app := strictAugmentation l E X data h
  naturality := by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro q
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    apply (cancel_mono (roosχ ((tower l E X data).obj N) p).hom).mp
    change (f.f (p + 1) ≫ (strictAugmentation l E X data h N).f (p + 1)) ≫ _ =
      ((strictAugmentation l E X data h M).f (p + 1) ≫
        (roosF.map ((tower l E X data).map f)).f (p + 1)) ≫ _
    simp only [Category.assoc, roosF_map_χ]
    rw [strictAugmentation_coordinates, ← Category.assoc,
      strictAugmentation_coordinates]
    apply biprod.hom_ext
    · simp
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc]
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
      congr 1
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Pi.lift_comp_π, roosPmap, Pi.map_π,
        Pi.lift_comp_π_assoc]
      exact (data.j n).naturality f

namespace TowerAssembly
universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
private def assemble {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N.asFunctor ⟶ N'.asFunctor) : N ⟶ N' where
  f q := { app n := (f.app n).f q
           naturality _ _ g := congrArg (fun k ↦ k.f q) (f.naturality g) }
  comm' q r _ := NatTrans.ext (funext (fun n ↦ (f.app n).comm q r))
private def assembleIso {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : N.asFunctor ≅ N'.asFunctor) : N ≅ N' where
  hom := assemble f.hom
  inv := assemble f.inv
  hom_inv_id := by
    ext1 q
    apply NatTrans.ext
    funext n
    exact congrArg (fun k ↦ k.f q) (f.hom_inv_id_app n)
  inv_hom_id := by
    ext1 q
    apply NatTrans.ext
    funext n
    exact congrArg (fun k ↦ k.f q) (f.inv_hom_id_app n)
end TowerAssembly

namespace EvalCone
universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
open CochainComplex RoosConeCalculus
private abbrev eval (n : ℕᵒᵖ) :=
  ((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)
private def coneIso {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N') (n : ℕᵒᵖ) :
    (mappingCone f).asFunctor.obj n ≅ mappingCone ((eval n).map f) :=
  mappingCone.mapHomologicalComplexIso f ((evaluation ℕᵒᵖ A).obj n)
@[reassoc]
private theorem target {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (n : ℕᵒᵖ) (q : ℤ) :
    (coneIso f n).hom.f q ≫ coneTarget ((eval n).map f) q = (coneTarget f q).app n := by
  change (mappingCone.mapHomologicalComplexXIso' f ((evaluation ℕᵒᵖ A).obj n)
    q (q + 1) rfl).hom ≫ _ = _
  simp only [mappingCone.mapHomologicalComplexXIso'_hom,
    evaluation_obj_obj, evaluation_obj_map, Preadditive.add_comp, Category.assoc,
    mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, comp_zero, zero_add]
  exact Category.comp_id _
@[reassoc]
private theorem source {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    (n : ℕᵒᵖ) (q : ℤ) :
    (coneIso f n).hom.f q ≫ coneSource ((eval n).map f) q (q + 1) rfl =
      (coneSource f q (q + 1) rfl).app n := by
  change (mappingCone.mapHomologicalComplexXIso' f ((evaluation ℕᵒᵖ A).obj n)
    q (q + 1) rfl).hom ≫ _ = _
  simp only [mappingCone.mapHomologicalComplexXIso'_hom, evaluation_obj_obj,
    evaluation_obj_map, Int.reduceNeg, Preadditive.add_comp, Category.assoc,
    mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v, comp_zero, add_zero]
  exact Category.comp_id _
private theorem natural {N N' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : N ⟶ N')
    {n m : ℕᵒᵖ} (g : n ⟶ m) :
    (mappingCone f).asFunctor.map g ≫ (coneIso f m).hom =
      (coneIso f n).hom ≫ mappingCone.map ((eval n).map f) ((eval m).map f)
        (N.asFunctor.map g) (N'.asFunctor.map g)
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality g).symm := by
  ext1 q
  apply mappingCone.ext_to _ q (q + 1) rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc, source,
      RoosConeCalculus.coneMap_source]
    rw [← Category.assoc, source]
    exact (coneSource f q (q + 1) rfl).naturality g
  · simp only [HomologicalComplex.comp_f, Category.assoc, target,
      RoosConeCalculus.coneMap_target]
    rw [← Category.assoc, target]
    exact (coneTarget f q).naturality g
end EvalCone

-- Keep assembly and coherence calculations independent of the coefficient category.
namespace TowerCalculus

universe uTower vTower
variable {C : Type uTower} [Category.{vTower} C] [Abelian C]
set_option backward.isDefEq.respectTransparency.types false

private def functor (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n) : CochainComplex (C) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ C) ℤ where
  obj M :=
    { X := fun q ↦ (Functor.ofOpSequence (T)).flip.obj M ⋙
        HomologicalComplex.eval (C) (.up ℤ) q
      d := fun q r ↦
        { app := fun n ↦ ((D n.unop).obj M).d q r
          naturality := fun _n _m f ↦
            (((Functor.ofOpSequence (T)).map f).app M).comm q r }
      shape := fun q r h ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((D n.unop).obj M).shape q r h))
      d_comp_d' := fun q r t _ _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((D n.unop).obj M).d_comp_d q r t)) }
  map f :=
    { f := fun q ↦
        { app := fun n ↦ ((D n.unop).map f).f q
          naturality := fun _n _m g ↦
            congrArg (fun h ↦ h.f q)
              (((Functor.ofOpSequence (T)).map g).naturality f).symm }
      comm' := fun q r _ ↦ NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
        ((D n.unop).map f).comm q r)) }
  map_id M := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((D n.unop).map_id M)))))
  map_comp f g := HomologicalComplex.Hom.ext (funext (fun q ↦
    NatTrans.ext (funext (fun (n : ℕᵒᵖ) ↦
      congrArg (fun h ↦ h.f q) ((D n.unop).map_comp f g)))))

private theorem tower_step (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (M : CochainComplex (C) ℤ) (n : ℕ) :
    ((functor D T).obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (T n).app M := by
  ext1 q
  change (((Functor.ofOpSequence T).map
    (homOfLE (Nat.le_succ n)).op).app M).f q = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
private def towerShiftIso (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (sD : ∀ n, (D n).CommShift ℤ)
    (h : ∀ n r M, (T n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
      (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
      ((T n).app M)⟦r⟧')
    (r : ℤ) (M : CochainComplex (C) ℤ) :
    (functor D T).obj (M⟦r⟧) ≅ ((functor D T).obj M)⟦r⟧ := by
  apply TowerAssembly.assembleIso
  refine NatIso.ofComponents (fun n ↦
    (Functor.commShiftIso (self := sD n.unop) (D n.unop) r).app M) ?_
  intro n m f
  exact (NatTrans.ofOpSequence
    (F := ((functor D T).obj (M⟦r⟧)).asFunctor)
    (G := (((functor D T).obj M)⟦r⟧).asFunctor)
    (fun n ↦ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M)
    (fun n ↦ by
      rw [tower_step]
      change _ = _ ≫ (((functor D T).obj M).asFunctor.map
        (homOfLE (Nat.le_succ n)).op)⟦r⟧'
      rw [tower_step]
      exact h n r M)).naturality f

private def towerConeIso (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (Φ : ∀ n {A B : CochainComplex (C) ℤ} (f : A ⟶ B),
      (D n).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((D n).map f))
    (hTΦ : ∀ n {A B : CochainComplex (C) ℤ} (f : A ⟶ B),
      (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
          ((D (n + 1)).map f) ((D n).map f)
          ((T n).app A) ((T n).app B) ((T n).naturality f))
    {A B : CochainComplex (C) ℤ} (f : A ⟶ B) :
    (functor D T).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((functor D T).map f) := by
  let e (n : ℕᵒᵖ) :
      ((functor D T).obj (CochainComplex.mappingCone f)).asFunctor.obj n ≅
        (CochainComplex.mappingCone ((functor D T).map f)).asFunctor.obj n :=
    Φ n.unop f ≪≫ (EvalCone.coneIso ((functor D T).map f) n).symm
  have hsucc (n : ℕ) :
      (((functor D T).obj (CochainComplex.mappingCone f)).asFunctor.map
        (homOfLE (Nat.le_succ n)).op) ≫ (e (op n)).hom =
      (e (op (n + 1))).hom ≫
        (CochainComplex.mappingCone ((functor D T).map f)).asFunctor.map
          (homOfLE (Nat.le_succ n)).op := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    apply (cancel_mono
      (EvalCone.coneIso ((functor D T).map f) (op n)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [EvalCone.natural]
    simp only [Iso.inv_hom_id_assoc]
    rw [tower_step]
    have he := hTΦ n f
    have hA := tower_step D T A n
    have hB := tower_step D T B n
    simpa only [hA, hB, Category.assoc] using! he
  exact TowerAssembly.assembleIso (NatIso.ofComponents e
    (fun {n m} g ↦ (NatTrans.ofOpSequence (fun n ↦ (e (op n)).hom) hsucc).naturality g))

private theorem towerConeIso_hom_app (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (Φ : ∀ n {A B : CochainComplex (C) ℤ} (f : A ⟶ B),
      (D n).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((D n).map f))
    (hTΦ : ∀ n {A B : CochainComplex (C) ℤ} (f : A ⟶ B),
      (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
          ((D (n + 1)).map f) ((D n).map f)
          ((T n).app A) ((T n).app B) ((T n).naturality f))
    {A B : CochainComplex (C) ℤ} (f : A ⟶ B) (q : ℤ) (n : ℕᵒᵖ) :
    ((towerConeIso D T Φ hTΦ f).hom.f q).app n =
      (Φ n.unop f).hom.f q ≫
        (EvalCone.coneIso ((functor D T).map f) n).inv.f q := rfl

private theorem tower_level_eq (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (M : CochainComplex (C) ℤ) (n : ℕᵒᵖ) :
    ((functor D T).obj M).asFunctor.obj n = (D n.unop).obj M := rfl

private theorem tower_map_app (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    {M N : CochainComplex (C) ℤ} (f : M ⟶ N) (q : ℤ) (n : ℕᵒᵖ) :
    (((functor D T).map f).f q).app n = ((D n.unop).map f).f q := rfl

private theorem eval_XIso {A : Type*} [Category A] [HasZeroMorphisms A]
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) {q p : ℤ} (h : q = p) (n : ℕᵒᵖ) :
    (N.XIsoOfEq h).hom.app n = ((N.asFunctor.obj n).XIsoOfEq h).hom := by
  subst h
  rfl

@[instance_reducible]
private def towerCommShift (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (sD : ∀ n, (D n).CommShift ℤ)
    (h : ∀ n r M, (T n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
      (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
      ((T n).app M)⟦r⟧') : (functor D T).CommShift ℤ where
  commShiftIso r := NatIso.ofComponents (towerShiftIso D T sD h r) (by
    intro M N f
    ext1 q
    apply NatTrans.ext
    funext n
    exact congrArg (fun k ↦ k.f q)
      ((Functor.commShiftIso (self := sD n.unop) (D n.unop) r).hom.naturality f))
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext1 q
    apply NatTrans.ext
    funext n
    have hh := congrArg (fun k ↦ (k.hom.app M).f q)
      (Functor.commShiftIso_zero (self := sD n.unop) (D n.unop) ℤ)
    simpa only [Functor.CommShift.isoZero_hom_app, HomologicalComplex.comp_f,
      CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
      towerShiftIso, TowerAssembly.assembleIso, TowerAssembly.assemble,
      NatIso.ofComponents_hom_app, Iso.app_hom, NatTrans.comp_app, tower_map_app,
      eval_XIso, tower_level_eq] using hh
  commShiftIso_add r t := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext1 q
    apply NatTrans.ext
    funext n
    have hh := congrArg (fun k ↦ (k.hom.app M).f q)
      (Functor.commShiftIso_add (self := sD n.unop) (D n.unop) r t)
    simpa only [Functor.CommShift.isoAdd_hom_app, HomologicalComplex.comp_f,
      CochainComplex.shiftFunctorAdd_inv_app_f, CochainComplex.shiftFunctorAdd_hom_app_f,
      CochainComplex.shiftFunctor_map_f', towerShiftIso, TowerAssembly.assembleIso,
      TowerAssembly.assemble, NatIso.ofComponents_hom_app, Iso.app_hom,
      NatTrans.comp_app, tower_map_app,
      eval_XIso, tower_level_eq] using hh

private def coneTriangleIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (G : CochainComplex C ℤ ⥤ CochainComplex D ℤ)
    [G.CommShift ℤ] {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (e : G.obj (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone (G.map f))
    (hi : G.map (CochainComplex.mappingCone.inr f) ≫ e.hom =
      CochainComplex.mappingCone.inr (G.map f))
    (hb : G.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (Functor.commShiftIso G (1 : ℤ)).hom.app M =
        e.hom ≫ (CochainComplex.mappingCone.triangle (G.map f)).mor₃) :
    G.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
      CochainComplex.mappingCone.triangle (G.map f) := by
  dsimp only [CochainComplex.mappingCone.triangle, Functor.mapTriangle_obj]
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · change G.map f ≫ 𝟙 _ = 𝟙 _ ≫ G.map f
    simp only [Category.comp_id, Category.id_comp]
  · change G.map (CochainComplex.mappingCone.inr f) ≫ e.hom =
      𝟙 _ ≫ CochainComplex.mappingCone.inr (G.map f)
    rw [Category.id_comp]
    exact hi
  · change (G.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (Functor.commShiftIso G (1 : ℤ)).hom.app M) ≫
      (𝟙 (G.obj M))⟦(1 : ℤ)⟧' = _
    rw [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans hb

set_option backward.isDefEq.respectTransparency.types false in
private def towerTriangleIso (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (sD : ∀ n, (D n).CommShift ℤ)
    (hTs : ∀ n r M, (T n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
      (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
      ((T n).app M)⟦r⟧')
    (Φ : ∀ n {K L : CochainComplex C ℤ} (f : K ⟶ L),
      (D n).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((D n).map f))
    (hTΦ : ∀ n {K L : CochainComplex C ℤ} (f : K ⟶ L),
      (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
          ((D (n + 1)).map f) ((D n).map f)
          ((T n).app K) ((T n).app L) ((T n).naturality f))
    (hinc : ∀ n {K L : CochainComplex C ℤ} (f : K ⟶ L),
      (D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
        CochainComplex.mappingCone.inr ((D n).map f))
    (hb : ∀ n {K L : CochainComplex C ℤ} (f : K ⟶ L),
      (D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          (Functor.commShiftIso (self := sD n) (D n) (1 : ℤ)).hom.app K =
        (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((D n).map f)).mor₃)
    [_hadd : (functor D T).Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    letI := towerCommShift D T sD hTs
    (functor D T).mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
      CochainComplex.mappingCone.triangle ((functor D T).map f) := by
  let := towerCommShift D T sD hTs
  apply coneTriangleIso (functor D T) f (towerConeIso D T Φ hTΦ f)
  · change (functor D T).map (CochainComplex.mappingCone.inr f) ≫
      (towerConeIso D T Φ hTΦ f).hom =
        CochainComplex.mappingCone.inr ((functor D T).map f)
    ext1 q
    apply NatTrans.ext
    funext n
    have hh := congrArg (fun k ↦ k.f q) (hinc n.unop f)
    apply (cancel_mono ((EvalCone.coneIso ((functor D T).map f) n).hom.f q)).mp
    simp only [HomologicalComplex.comp_f, NatTrans.comp_app,
      towerConeIso_hom_app, Category.assoc, tower_map_app]
    have he := congrArg (fun k ↦ k.f q)
      (EvalCone.coneIso ((functor D T).map f) n).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
    erw [he]
    erw [Category.comp_id]
    rw [← HomologicalComplex.comp_f]
    change _ = (((EvalCone.eval n).map (CochainComplex.mappingCone.inr
      ((functor D T).map f))) ≫
      (EvalCone.coneIso ((functor D T).map f) n).hom).f q
    erw [CochainComplex.mappingCone.map_inr]
    exact hh
  · change ((functor D T).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (towerShiftIso D T sD hTs (1 : ℤ) K).hom) =
      (towerConeIso D T Φ hTΦ f).hom ≫
        (CochainComplex.mappingCone.triangle ((functor D T).map f)).mor₃
    ext1 q
    apply NatTrans.ext
    funext n
    have hh := congrArg (fun k ↦ k.f q) (hb n.unop f)
    have hd := congrArg (fun k ↦ k.f q)
      (CochainComplex.mappingCone.map_δ ((functor D T).map f)
        ((evaluation ℕᵒᵖ C).obj n))
    simp only [HomologicalComplex.comp_f] at hh hd
    have hd' : (EvalCone.coneIso ((functor D T).map f) n).inv.f q ≫
        ((CochainComplex.mappingCone.triangle ((functor D T).map f)).mor₃.f q).app n =
        (CochainComplex.mappingCone.triangle ((D n.unop).map f)).mor₃.f q := by
      apply (cancel_epi
        ((EvalCone.coneIso ((functor D T).map f) n).hom.f q)).mp
      have he := congrArg (fun k ↦ k.f q)
        (EvalCone.coneIso ((functor D T).map f) n).hom_inv_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
      erw [← Category.assoc, he, Category.id_comp]
      simp only [CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f] at hd
      erw [Category.comp_id] at hd
      exact hd
    simp only [HomologicalComplex.comp_f, NatTrans.comp_app, tower_map_app,
      towerConeIso_hom_app]
    dsimp only [towerShiftIso, TowerAssembly.assembleIso, TowerAssembly.assemble,
      NatIso.ofComponents_hom_app, Iso.app_hom]
    erw [Category.assoc, hd']
    exact hh

private def principalCone (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (J : ∀ n, 𝟭 (CochainComplex C ℤ) ⟶ D n)
    (h : ∀ n M, (J (n + 1)).app M ≫ (T n).app M = (J n).app M)
    (M : CochainComplex (C) ℤ) : Cone ((functor D T).obj M).asFunctor where
  pt := M
  π := NatTrans.ofOpSequence (fun n ↦ (J n).app M) (fun n ↦ by
    simp only [Functor.const_obj_map]
    rw [tower_step]
    erw [Category.id_comp]
    exact (h n M).symm)

private theorem augmentation_shift [HasCountableProducts C]
    (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (T : ∀ n, D (n + 1) ⟶ D n)
    (sD : ∀ n, (D n).CommShift ℤ)
    (hTs : ∀ n r M, (T n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
      (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
      ((T n).app M)⟦r⟧')
    (J : ∀ n, 𝟭 (CochainComplex C ℤ) ⟶ D n)
    (hjT : ∀ n M, (J (n + 1)).app M ≫ (T n).app M = (J n).app M)
    (haugs : ∀ n r M, (J n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
      ((J n).app M)⟦r⟧')
    (cs : (roosF (A := C)).CommShift ℤ) (hnat : RoosConeCalculus.AugmentationNaturality (C))
    (hshift : RoosConeCalculus.ShiftAugmentation cs) (M : CochainComplex (C) ℤ)
    (r : ℤ) :
    letI : (functor D T).CommShift ℤ := towerCommShift D T sD hTs
    letI : roosF.CommShift ℤ := cs
    letI : (functor D T ⋙ roosF).CommShift ℤ := Functor.CommShift.comp (functor D T) roosF
    (RoosConeCalculus.augmentation (principalCone D T J hjT (M⟦r⟧))) ≫
      (Functor.commShiftIso (functor D T ⋙ roosF) r).hom.app M =
      (RoosConeCalculus.augmentation (principalCone D T J hjT M))⟦r⟧' := by
  let : (functor D T).CommShift ℤ := towerCommShift D T sD hTs
  let : roosF.CommShift ℤ := cs
  let : (functor D T ⋙ roosF).CommShift ℤ := Functor.CommShift.comp (functor D T) roosF
  let j := principalCone D T J hjT M
  let js : Cone (((functor D T).obj M)⟦r⟧).asFunctor :=
    { pt := M⟦r⟧
      π := (principalCone D T J hjT (M⟦r⟧)).π ≫
        HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (towerShiftIso D T sD hTs r M).hom }
  have hn := hnat (towerShiftIso D T sD hTs r M).hom
    (principalCone D T J hjT (M⟦r⟧)) js (𝟙 _) (by intro n; simp [js])
  have hs := hshift ((functor D T).obj M) j r js (𝟙 _) (by
    intro q n
    dsimp only [js, j, NatTrans.comp_app, HomologicalComplex.comp_f,
      HomologicalComplex.id_f]
    dsimp only [principalCone, NatTrans.ofOpSequence_app,
      towerShiftIso, TowerAssembly.assembleIso, TowerAssembly.assemble,
      NatIso.ofComponents_hom_app, Iso.app_hom, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq, eqToIso,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f]
    simp only [eqToHom_refl, NatTrans.id_app]
    erw [Category.comp_id, Category.id_comp]
    erw [Category.id_comp]
    simpa only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] using!
      congrArg (fun k ↦ k.f q) (haugs n r M))
  simp only [Category.id_comp] at hn hs
  rw [Functor.commShiftIso_comp_hom_app]
  dsimp only [Functor.commShiftIso, towerCommShift, NatIso.ofComponents_hom_app,
    Functor.comp_map]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ (Functor.commShiftIso (self := cs) (roosF (A := C)) r).hom.app
      ((functor D T).obj M)) hn).trans hs)

end TowerCalculus

private theorem tower_step (data : PrincipalReductionConeData l E X)
    (M : CochainComplex (Modules l E X) ℤ) (n : ℕ) :
    ((tower l E X data).obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (data.T n).app M := by
  ext1 q
  change (((Functor.ofOpSequence data.T).map
    (homOfLE (Nat.le_succ n)).op).app M).f q = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private def principalCone (data : PrincipalReductionConeData l E X)
    (h : ∀ n M, (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (M : CochainComplex (Modules l E X) ℤ) : Cone ((tower l E X data).obj M).asFunctor where
  pt := M
  π := NatTrans.ofOpSequence (fun n ↦ (data.j n).app M) (fun n ↦ by
    change (data.j n).app M = _
    rw [tower_step]
    exact (h n M).symm)

private theorem strictAugmentation_eq (data : PrincipalReductionConeData l E X)
    (h : ∀ n M, (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (M : CochainComplex (Modules l E X) ℤ) :
    strictAugmentation l E X data h M =
      RoosConeCalculus.augmentation (principalCone l E X data h M) := rfl

set_option backward.isDefEq.respectTransparency.types false in
private def tensorTowerMap
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hχ : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (PrincipalReduction.scalar l E X data.d n M) q)
    (hT : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      ((data.T n).app M).f q ≫ (data.χ n M q).hom =
        (data.χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E X data.d M).f (q + 1)))
    (P : CochainComplex (Modules l E X) ℤ) :
    ((tower l E X data).obj P) ⟶ RoosCompletion.tensorTower l E X P := by
  let f : ((tower l E X data).obj P).asFunctor ⟶
      (RoosCompletion.tensorTower l E X P).asFunctor :=
    NatTrans.ofOpSequence (CoefficientCone.coneToTensor l E X data hdata P) (fun n ↦ by
      rw [tower_step, RoosCompletion.tower_step]
      exact CoefficientCone.coneToTensor_step l E X data hdata hχ hT P n)
  exact
    { f := fun q ↦
        { app := fun n ↦ (f.app n).f q
          naturality := fun _ _ g ↦ congrArg (fun k ↦ k.f q) (f.naturality g) }
      comm' := fun q r _ ↦ NatTrans.ext (funext (fun n ↦ (f.app n).comm q r)) }

set_option backward.isDefEq.respectTransparency.types false in
private theorem strict_tensor_comparison
    (data : PrincipalReduction.PrincipalReductionConeData l E X)
    (hdata : data.IsCanonical l E X)
    (hχ : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (PrincipalReduction.scalar l E X data.d n M) q)
    (hT : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      ((data.T n).app M).f q ≫ (data.χ n M q).hom =
        (data.χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E X data.d M).f (q + 1)))
    (hj : ∀ n (M : CochainComplex (Modules l E X) ℤ) q,
      ((data.j n).app M).f q ≫ (data.χ n M q).hom = biprod.inl)
    (hjT : ∀ n M, (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (hq : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ} (f : N ⟶ N'),
      (∀ n : ℕ, QuasiIso ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
        (op n))) → QuasiIso (roosF.map f))
    (hnat : RoosConeCalculus.AugmentationNaturality (Modules l E X))
    (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P) :
    ∃ ρ : DerivedCategory.Q.obj ((complexCompletion l E X data).obj P) ≅
        DerivedCategory.Q.obj (roos l E X P),
      DerivedCategory.Q.map (strictAugmentation l E X data hjT P) ≫ ρ.hom =
        DerivedCategory.Q.map (augmentation l E X P) := by
  let f := tensorTowerMap l E X data hdata hχ hT P
  have hf : QuasiIso (roosF.map f) := hq f (fun n ↦
    CoefficientCone.coneToTensor_quasiIso l E X data hdata P hP n)
  let e := RoosCompletion.signedIso l E X P
  refine ⟨asIso (DerivedCategory.Q.map (roosF.map f)) ≪≫ DerivedCategory.Q.mapIso e, ?_⟩
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map (roosF.map f) ≫
    DerivedCategory.Q.map e.hom = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg (fun k : P ⟶ roos l E X P ↦ DerivedCategory.Q.map k)
  have hn := hnat f (principalCone l E X data hjT P)
    (RoosCompletion.tensorCone l E X P) (𝟙 P) (by
      intro n
      simpa only [Category.id_comp] using!
        CoefficientCone.coneToTensor_unit l E X data hdata hχ hj P n)
  rw [strictAugmentation_eq]
  rw [reassoc_of% hn]
  erw [Category.id_comp]
  exact RoosCompletion.augmentation_sign l E X P

set_option backward.isDefEq.respectTransparency.types false in
private theorem strictAugmentation_shift (data : PrincipalReductionConeData l E X)
    (sD : ∀ n, (data.D n).CommShift ℤ)
    (hTs : ∀ n r M, (data.T n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
      (Functor.commShiftIso (self := sD (n + 1)) (data.D (n + 1)) r).hom.app M ≫
      ((data.T n).app M)⟦r⟧')
    (hjT : ∀ n M, (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M)
    (haugs : ∀ n r M, (data.j n).app (M⟦r⟧) ≫
      (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
      ((data.j n).app M)⟦r⟧')
    (cs : (roosF (A := Modules l E X)).CommShift ℤ)
    (hnat : RoosConeCalculus.AugmentationNaturality (Modules l E X))
    (hshift : RoosConeCalculus.ShiftAugmentation cs) (M : CochainComplex (Modules l E X) ℤ)
    (r : ℤ) :
    letI : (tower l E X data).CommShift ℤ := TowerCalculus.towerCommShift data.D data.T sD hTs
    letI : roosF.CommShift ℤ := cs
    letI : (complexCompletion l E X data).CommShift ℤ :=
      Functor.CommShift.comp (tower l E X data) roosF
    (strictAugmentation l E X data hjT (M⟦r⟧)) ≫
      (Functor.commShiftIso (complexCompletion l E X data) r).hom.app M =
      (strictAugmentation l E X data hjT M)⟦r⟧' := by
  exact TowerCalculus.augmentation_shift data.D data.T sD hTs data.j hjT haugs
    cs hnat hshift M r

-- Precomposition with Q detects the identity; cancel its shift and descent isomorphisms.
private theorem descended_shift
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : CochainComplex (C) ℤ ⥤ CochainComplex (C) ℤ)
    [G.CommShift ℤ]
    (F : DerivedCategory (C) ⥤ DerivedCategory (C))
    [F.CommShift ℤ] (κ : DerivedCategory.Q ⋙ F ≅ G ⋙ DerivedCategory.Q)
    [NatTrans.CommShift κ.hom ℤ]
    (a : 𝟭 (CochainComplex (C) ℤ) ⟶ G)
    (ha : ∀ (r : ℤ) (M : CochainComplex (C) ℤ),
      a.app (M⟦r⟧) ≫ (Functor.commShiftIso G r).hom.app M =
      (a.app M)⟦r⟧')
    (c : 𝟭 (DerivedCategory (C)) ⟶ F)
    (hc : ∀ M, c.app (DerivedCategory.Q.obj M) ≫ κ.hom.app M =
      DerivedCategory.Q.map (a.app M)) : NatTrans.CommShift c ℤ := by
  constructor
  intro r
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (C) (.up ℤ))
  intro M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.commShiftIso_id_hom_app]
  apply (cancel_epi ((Functor.commShiftIso DerivedCategory.Q r).hom.app M)).mp
  apply (cancel_mono ((κ.hom.app M)⟦r⟧')).mp
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, hc]
  have hn := c.naturality ((Functor.commShiftIso DerivedCategory.Q r).hom.app M)
  dsimp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hk := NatTrans.shift_app_comm κ.hom r M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] at hk
  rw [hk]
  rw [reassoc_of% (hc (M⟦r⟧))]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  rw [ha r M]
  simpa only [Category.comp_id, Category.id_comp, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj] using!
    ((Functor.commShiftIso DerivedCategory.Q r).hom.naturality (a.app M)).symm

private theorem complete_iff_from_comparison
    (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
    (c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F)
    (hc : ∀ (K : DerivedCategory (Modules l E X))
      (P : CochainComplex (Modules l E X) ℤ)
      (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
      (e : DerivedCategory.Q.obj P ≅ K),
      ∃ ψ : F.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
        c.app K ≫ ψ.hom = completionMap l E X K P e)
    (K : DerivedCategory (Modules l E X)) : IsDerivedComplete l E X K ↔ IsIso (c.app K) := by
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨ψ, hψ⟩ := hc K P hP e
  rw [AdicCompletion.isDerivedComplete_iff l E X K P hP e, ← hψ]
  constructor
  · intro h
    have : IsIso (c.app K ≫ ψ.hom) := h
    exact IsIso.of_isIso_comp_right (c.app K) ψ.hom
  · intro h
    have : IsIso (c.app K) := h
    infer_instance

private theorem representative_comparison
    (G : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
    (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
    (c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F)
    (a : 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ G)
    (κ : DerivedCategory.Q ⋙ F ≅ G ⋙ DerivedCategory.Q)
    (hc : ∀ M, c.app (DerivedCategory.Q.obj M) ≫ κ.hom.app M =
      DerivedCategory.Q.map (a.app M))
    (P : CochainComplex (Modules l E X) ℤ)
    (ρ : DerivedCategory.Q.obj (G.obj P) ≅
      DerivedCategory.Q.obj (AdicCompletion.roos l E X P))
    (hρ : DerivedCategory.Q.map (a.app P) ≫ ρ.hom =
      DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))
    (K : DerivedCategory (Modules l E X)) (e : DerivedCategory.Q.obj P ≅ K) :
    ∃ ψ : F.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
      c.app K ≫ ψ.hom = completionMap l E X K P e := by
  refine ⟨F.mapIso e.symm ≪≫ κ.app P ≪≫ ρ, ?_⟩
  change c.app K ≫ F.map e.inv ≫ κ.hom.app P ≫ ρ.hom = _
  rw [← c.naturality_assoc, reassoc_of% (hc P), hρ]
  rfl

private def triangleAugmentation
    (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
    [F.CommShift ℤ] (c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F)
    (hc : ∀ (K : DerivedCategory (Modules l E X)) (r : ℤ),
      c.app (K⟦r⟧) ≫ (Functor.commShiftIso F r).hom.app K = (c.app K)⟦r⟧')
    (T : Triangle (DerivedCategory (Modules l E X))) : T ⟶ F.mapTriangle.obj T where
  hom₁ := c.app T.obj₁
  hom₂ := c.app T.obj₂
  hom₃ := c.app T.obj₃
  comm₁ := c.naturality T.mor₁
  comm₂ := c.naturality T.mor₂
  comm₃ := by
    change _ = c.app T.obj₃ ≫ F.map T.mor₃ ≫ _
    rw [← c.naturality_assoc, hc]
    rfl

private theorem descended_triangulated
    (G : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
    [G.Additive] [G.CommShift ℤ]
    (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
    [F.Additive] [F.CommShift ℤ]
    (κ : DerivedCategory.Q ⋙ F ≅ G ⋙ DerivedCategory.Q)
    [NatTrans.CommShift κ.hom ℤ]
    (hcone : ∀ {M N : CochainComplex (Modules l E X) ℤ} (f : M ⟶ N),
      Nonempty (G.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
        CochainComplex.mappingCone.triangle (G.map f))) : F.IsTriangulated := by
  constructor
  intro T hT
  obtain ⟨M, N, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T).mp hT
  apply isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished (G.map f)) _
  exact F.mapTriangle.mapIso e ≪≫
    (Functor.mapTriangleCompIso DerivedCategory.Q F).symm.app _ ≪≫
    (Functor.mapTriangleIso κ).app _ ≪≫
    (Functor.mapTriangleCompIso G DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (hcone f).some

private def roosTriangleIso
    (cs : (roosF (A := Modules l E X)).CommShift ℤ)
    (Φ : ∀ {N N' : CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ} (f : N ⟶ N'),
      roosF.obj (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone (roosF.map f))
    (hc : RoosConeCalculus.ConeCompatibility cs Φ)
    {N N' : CochainComplex (ℕᵒᵖ ⥤ Modules l E X) ℤ} (f : N ⟶ N') :
    letI := cs
    roosF.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
      CochainComplex.mappingCone.triangle (roosF.map f) := by
  let := cs
  exact TowerCalculus.coneTriangleIso roosF f (Φ f) (hc.2 f).1 (hc.2 f).2

-- The final cone-triangle transport elaborates large mapping-cone triangle isomorphisms.
/-- Principal completion descends with its specified augmentation, coherent shifts,
and morphism of distinguished triangles.

Source: blueprint main-20261015, first-reduction proof, Cones paragraph and shifts
sentence; Stacks Tag 05RU (blueprint: lem-pe-completion-triangle-comparison).

Proof, following the nine steps of the updated DAG node:
1. Assemble the additive principal-reduction tower and apply the Roos functor.
   Their quasi-isomorphism clauses imply that this composite preserves quasi-isomorphisms.
   The compatible principal units give its strict natural augmentation.
2. Descend the composite and augmentation through DerivedCategory.Q with Localization.lift,
   Localization.fac and Localization.liftNatTrans. The application formula gives the
   specified equality between the descended and strict augmentations.
3. Transfer additivity through the descent isomorphism, the homotopy quotient and Qh.
4. Assemble the coherent principal shifts by evaluation and compose with the Roos shifts.
   Roos augmentation naturality and shift compatibility give strict augmentation compatibility.
   Descend both shifts and augmentation compatibility through the localization.
5. Work in the actual internal-module category of the completion definition. Its adopted
   flat K-flat resolution supplies flat representatives without changing coefficient encoding.
6. Pull back the exact coefficient sequence of lemma-reduction-derived-nakayama--1 and
   identify its scalar with the canonical principal scalar. Tensor exactness and the
   cone-to-quotient theorem give the cone-to-tensor quasi-isomorphism for flat complexes.
   Transfer this result to arbitrary K-flat complexes along a flat K-flat resolution,
   using tensor invariance, cone two-out-of-three and naturality. Coordinate formulas
   prove transition compatibility and preservation of the specified units.
7. Apply the Roos quasi-isomorphism clause to this augmented tower map. The explicit
   biproduct sign change (v,u) ↦ (v,-u) identifies its result with AdicCompletion.roos
   and fixes the augmentation. Localizing and transporting along any representative
   gives exactly completionMap by naturality. The recorded completeness criterion
   then identifies completeness with invertibility of the descended augmentation.
8. Assemble the principal cone comparisons by evaluation, including the inclusion and
   signed-boundary equations, and compose with the Roos cone-triangle comparison.
   Thus the strict composite sends a cone triangle to the corresponding cone triangle.
9. Every distinguished derived triangle has a chain-map cone representative. Transport
   step 8 through the descent isomorphism to prove that F preserves distinguished triangles.
   Naturality gives the first two squares of the augmentation morphism; naturality at
   the last arrow followed by augmentation shift compatibility gives its third square. -/
theorem completion_triangle_comparison :
    ∃ data : PrincipalReductionConeData l E X, data.IsCanonical l E X ∧
    ∃ (a : 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ complexCompletion l E X data)
      (F : DerivedCategory (Modules l E X) ⥤ DerivedCategory (Modules l E X))
      (c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F)
      (κ : DerivedCategory.Q ⋙ F ≅ complexCompletion l E X data ⋙ DerivedCategory.Q)
      (sF : F.CommShift ℤ),
      F.Additive ∧
      (∀ (M : CochainComplex (Modules l E X) ℤ) (p : ℤ),
        (a.app M).f (p + 1) ≫ (roosχ ((tower l E X data).obj M) p).hom =
          biprod.lift 0 ((Pi.lift
            (f := fun n : ℕ ↦ ((tower l E X data).obj M).asFunctor.obj (op n))
            (fun n : ℕ ↦ (data.j n).app M)).f (p + 1))) ∧
      (∀ M : CochainComplex (Modules l E X) ℤ,
        c.app (DerivedCategory.Q.obj M) ≫ κ.hom.app M =
          DerivedCategory.Q.map (a.app M)) ∧
      (∀ (K : DerivedCategory (Modules l E X))
        (P : CochainComplex (Modules l E X) ℤ)
        (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
        (e : DerivedCategory.Q.obj P ≅ K),
        ∃ ψ : F.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
          c.app K ≫ ψ.hom = completionMap l E X K P e) ∧
      (∀ K : DerivedCategory (Modules l E X),
        IsDerivedComplete l E X K ↔ IsIso (c.app K)) ∧
      (∀ (K : DerivedCategory (Modules l E X)) (r : ℤ),
        c.app (K⟦r⟧) ≫ (Functor.commShiftIso (self := sF) F r).hom.app K =
          (c.app K)⟦r⟧') ∧
      (∀ (T : Triangle (DerivedCategory (Modules l E X)))
        (_hT : T ∈ distTriang (DerivedCategory (Modules l E X))),
        Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
            (F.map T.mor₃ ≫
              (Functor.commShiftIso (self := sF) F (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (DerivedCategory (Modules l E X)) ∧
        ∃ γ : T ⟶ Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
          (F.map T.mor₃ ≫
            (Functor.commShiftIso (self := sF) F (1 : ℤ)).hom.app T.obj₁),
          γ.hom₁ = c.app T.obj₁ ∧ γ.hom₂ = c.app T.obj₂ ∧ γ.hom₃ = c.app T.obj₃) := by
  classical
  obtain ⟨data, hdata⟩ := principalReductionConeData l E X
  obtain ⟨sD, sR, κR, Φ, hχ, hmap, hT, hj, hjT, hq, htri, hκT, hκj,
      hΦ, hsD, hnatΦ, hTΦ, hTs, hinc, hboundary, haugΦ, haugs, hκs⟩ :=
    (hdata (op (Profinite.of (ULift.{u} Unit))) 0 ⟨()⟩).2
  have : CountableAB4Star (Modules l E X) := countableExact l E X
  obtain ⟨haddH, hcoord, hqH, hderH, csH, ΦH, hnatH, hsH, hΦH, hconeH, haugH, hshiftH⟩ :=
    RoosConeCalculus.assemble_calculus (A := Modules l E X)
  have : (tower l E X data).Additive := tower_additive l E X data hmap
  have : roosF.Additive := haddH
  let a := strictAugmentationNat l E X data hjT
  let G := complexCompletion l E X data
  let Q := DerivedCategory.Q (C := Modules l E X)
  let W := HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)
  have hG : W.IsInvertedBy (G ⋙ Q) := by
    intro M N f hf
    have hQ : QuasiIso f := hf
    have hGf : QuasiIso (G.map f) :=
      hqH ((tower l E X data).map f) (fun n ↦ hq n f hQ)
    change IsIso (DerivedCategory.Q.map (G.map f))
    infer_instance
  let : (tower l E X data).CommShift ℤ := TowerCalculus.towerCommShift data.D data.T sD hTs
  let : roosF.CommShift ℤ := csH
  let : G.CommShift ℤ := inferInstance
  let F := Localization.lift (G ⋙ Q) hG Q
  let κ : Q ⋙ F ≅ G ⋙ Q := Localization.fac (G ⋙ Q) hG Q
  let c : 𝟭 (DerivedCategory (Modules l E X)) ⟶ F :=
    Localization.liftNatTrans Q W Q (G ⋙ Q) (𝟭 _) F (Functor.whiskerRight a Q)
  let sF : F.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (G ⋙ Q) F
  have hc : ∀ M, c.app (Q.obj M) ≫ κ.hom.app M = Q.map (a.app M) := by
    intro M
    dsimp only [c]
    rw [Localization.liftNatTrans_app]
    have hid : (Localization.Lifting.iso Q W Q (𝟭 _)).hom.app M = 𝟙 _ := rfl
    rw [hid, Category.id_comp]
    change (Q.map (a.app M) ≫ κ.inv.app M) ≫ κ.hom.app M = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    dsimp only [Q, Functor.comp_obj]
    exact Category.comp_id _
  have : F.Additive := descended_additive l E X G F κ
  have : NatTrans.CommShift κ.hom ℤ := by
    change NatTrans.CommShift (Localization.Lifting.iso Q W (G ⋙ Q) F).hom ℤ
    exact NatTrans.commShift_iso_hom_of_localization Q W ℤ (G ⋙ Q) F
  have : NatTrans.CommShift c ℤ := descended_shift G F κ a
    (fun r M ↦ strictAugmentation_shift l E X data sD hTs hjT haugs csH hnatH hshiftH M r) c hc
  have hcs (K : DerivedCategory (Modules l E X)) (r : ℤ) :
      c.app (K⟦r⟧) ≫ (Functor.commShiftIso F r).hom.app K = (c.app K)⟦r⟧' := by
    have h := (NatTrans.shift_app_comm c r K).symm
    simp only [Functor.commShiftIso_id_hom_app] at h
    erw [Category.id_comp] at h
    exact h
  have hcompare : ∀ (K : DerivedCategory (Modules l E X))
      (P : CochainComplex (Modules l E X) ℤ)
      (_hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
      (e : DerivedCategory.Q.obj P ≅ K),
      ∃ ψ : F.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
        c.app K ≫ ψ.hom = completionMap l E X K P e := by
    intro K P hP e
    obtain ⟨ρ, hρ⟩ := strict_tensor_comparison l E X data hdata hχ hT hj hjT hqH hnatH P hP
    exact representative_comparison l E X G F c a κ hc P ρ hρ K e
  refine ⟨data, hdata, a, F, c, κ, sF, inferInstance, ?_, hc, ?_, ?_, hcs, ?_⟩
  · exact strictAugmentation_coordinates l E X data hjT
  · exact hcompare
  · exact complete_iff_from_comparison l E X F c hcompare
  · have hGcone : ∀ {M N : CochainComplex (Modules l E X) ℤ} (f : M ⟶ N),
        Nonempty (G.mapTriangle.obj (CochainComplex.mappingCone.triangle f) ≅
          CochainComplex.mappingCone.triangle (G.map f)) := by
      intro M N f
      exact ⟨(Functor.mapTriangleCompIso (tower l E X data) roosF).app _ ≪≫
        roosF.mapTriangle.mapIso
          (TowerCalculus.towerTriangleIso data.D data.T sD hTs Φ hTΦ hinc hboundary
            (_hadd := tower_additive l E X data hmap) f) ≪≫
        roosTriangleIso l E X csH ΦH hconeH ((tower l E X data).map f)⟩
    let := descended_triangulated l E X G F κ hGcone
    intro T hT
    exact ⟨F.map_distinguished T hT, triangleAugmentation l E X F c hcs T, rfl, rfl, rfl⟩

end AlgebraicGeometry.ProEtale.CompletionTriangle
