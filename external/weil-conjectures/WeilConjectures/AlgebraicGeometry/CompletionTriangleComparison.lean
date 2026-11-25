/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

set_option linter.privateModule false

/-! # Exact principal completion and its canonical triangle map

proof.md`,
Cones paragraph and shifts sentence; Stacks Tag 05RU
(auxiliary; not a blueprint node).

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
end CoefficientCone

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
namespace RoosCompletion
variable {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : AlgebraicGeometry.Scheme.{u})
open AlgebraicGeometry.ProEtale.AdicCompletion
end RoosCompletion

set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.ProEtale.CompletionTriangle

open AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

namespace TowerAssembly
universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
end TowerAssembly

namespace EvalCone
universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
open CochainComplex
end EvalCone

-- Keep assembly and coherence calculations independent of the coefficient category.
namespace TowerCalculus

universe uTower vTower
variable {C : Type uTower} [Category.{vTower} C] [Abelian C]
set_option backward.isDefEq.respectTransparency.types false

end TowerCalculus

end AlgebraicGeometry.ProEtale.CompletionTriangle
