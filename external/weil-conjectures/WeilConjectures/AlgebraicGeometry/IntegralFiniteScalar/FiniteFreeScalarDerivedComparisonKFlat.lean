/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! K-flatness part of the finite-free scalar comparison.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

private lemma flat_finite_coproduct
    {B : Type*} [Category* B] [Abelian B] [MonoidalCategory B]
    [BraidedCategory B] [MonoidalClosed B] {I : Type} [Finite I]
    (f : I → B) (hf : ∀ i, ObjectProperty.flat (f i)) :
    ObjectProperty.flat (∐ f) := by
  have : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  have (i : I) : PreservesFiniteLimits (tensorLeft (f i)) := (hf i).1.1
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesColimit (Discrete.functor f) (curriedTensor B) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  have e : tensorLeft (∐ f) ≅
      (Discrete.functor f ⋙ curriedTensor B).flip ⋙ colim :=
    preservesColimitIso (curriedTensor B) (Discrete.functor f) ≪≫
      colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((Discrete.functor f ⋙ curriedTensor B).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (f j.as))))
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := B)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  have := comp_preservesFiniteLimits
    ((Discrete.functor f ⋙ curriedTensor B).flip) (colim (J := Discrete I) (C := B))
  exact preservesFiniteLimits_of_natIso e.symm

private lemma mapped_finite_free_flat
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [MonoidalCategory B] [BraidedCategory B] [MonoidalClosed B]
    [HasFiniteBiproducts A]
    (F : A ⥤ B) [F.Additive] (U P : A) (r : ℕ)
    (e : P ≅ biproduct (fun _ : Fin r ↦ U)) (hU : ObjectProperty.flat (F.obj U)) :
    ObjectProperty.flat (F.obj P) := by
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  apply (ObjectProperty.flat.prop_iff_of_iso
    (F.mapIso e ≪≫ F.mapBiproduct (fun _ : Fin r ↦ U) ≪≫
      biproduct.isoCoproduct (fun _ : Fin r ↦ F.obj U))).2
  exact flat_finite_coproduct _ (fun _ ↦ hU)

private lemma mapped_cone_term_flat
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    (F : A ⥤ B) [F.Additive] {P Q : A} (f : P ⟶ Q)
    (hP : ObjectProperty.flat (F.obj P)) (hQ : ObjectProperty.flat (F.obj Q)) (i : ℤ) :
    ObjectProperty.flat (F.obj ((CochainComplex.monoCokernelComplex f).X i)) := by
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  by_cases hi : i = -1
  · subst i
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod
      ((CochainComplex.singleFunctor A 0).map f) (-1) 0 (by decide) ≪≫
      (isoBiprodZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q (-1) (by decide))).symm ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 P
    exact (ObjectProperty.flat.prop_iff_of_iso (F.mapIso e)).2 hP
  · by_cases hi' : i = 0
    · subst i
      let e := HomologicalComplex.homotopyCofiber.XIsoBiprod
        ((CochainComplex.singleFunctor A 0).map f) 0 1 (by decide) ≪≫
        (isoZeroBiprod
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P 1 (by decide))).symm ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q
      exact (ObjectProperty.flat.prop_iff_of_iso (F.mapIso e)).2 hQ
    · apply ObjectProperty.flat_of_isZero
      apply F.map_isZero
      exact (CochainComplex.mappingCone.isZero_X_iff _ i).2
        ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (i + 1) (by omega),
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q i hi'⟩

private lemma mapped_cone_bounded
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] {P Q : A} (f : P ⟶ Q) :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.monoCokernelComplex f)) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply F.map_isZero
  exact (CochainComplex.mappingCone.isZero_X_iff _ i).2
    ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P (i + 1) (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Q i (by omega)⟩

set_option linter.unusedVariables false in
/-- The sectionwise image of the pulled-back finite-free complex is K-flat.

The theorem's independent-coefficient clause
is transported back along the fixed equivalence, giving the displayed complex.
-/
theorem finiteFreeScalarDerivedComparison_kflat
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (Z : Scheme.{u}) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((ModuleRingedComparison.equivalence Λ.X Z).functor.mapHomologicalComplex
        (.up ℤ)).obj (complex Λ S Z)) := by
  -- The K-flatness component only uses the finite-free terms and their degree bound.
  classical
  let R := ModuleRingedComparison.ring Λ.X Z
  let E := (ModuleRingedComparison.equivalence Λ.X Z).functor
  let F := pointPull Λ Z ⋙ E
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  obtain ⟨_, _, e₀, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology Z) (condensedRingObj Λ.X Z)
  have hu : ObjectProperty.flat (F.obj (Mod.regular Λ.X)) := by
    apply (ObjectProperty.flat.prop_iff_of_iso
      (E.mapIso ((sfbPullbackFromPoint Z).mapModUnitIso (R := Λ.X)).symm ≪≫ e₀)).2
    exact ObjectProperty.prop_unit _
  have h₁ := mapped_finite_free_flat F (Mod.regular Λ.X) S.X₁ r e₁ hu
  have h₂ := mapped_finite_free_flat F (Mod.regular Λ.X) S.X₂ r e₂ hu
  have : CochainComplex.IsStrictlyLE
      ((E.mapHomologicalComplex (.up ℤ)).obj (complex Λ S Z)) 0 :=
    mapped_cone_bounded F S.f
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm
    (mapped_cone_term_flat F S.f h₁ h₂ i).2

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
