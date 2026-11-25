/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import all WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldLocalTensorModel
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Tensoring with a restricted coefficient unit

## References

* Stacks Project, Modules on Sites, Tag 05V4, the balanced tensor identity
* Stacks Project, Modules on Sites, Tag 05V4, the tensor cancellation identity
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme
namespace ResidueLayerTensor

variable (Y : Scheme.{u})
  {R S T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}

private theorem siteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] siteSmall
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private def extensionComp (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T)
    (h : a ≫ b = c) : pbcExtend a ⋙ pbcExtend b ≅ pbcExtend c :=
  Adjunction.leftAdjointCompIso (pbcScalarAdjunction a) (pbcScalarAdjunction b)
    (pbcScalarAdjunction c) (pbcRestrictComp a b c h)

private def tensorUnitCancellation (b : S ⟶ T) :
    let := SheafOfModules.monoidalCategory S
    tensorLeft ((pbcRestrict b).obj (SheafOfModules.unit ((adicLisseForget Y).obj T))) ≅
      FiniteFieldTensor.tensorFunctor b ⋙ pbcRestrict b := by
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory T
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation b).choose
  let U := SheafOfModules.unit ((adicLisseForget Y).obj T)
  let α : FiniteFieldTensor.tensorFunctor b ⋙ tensorLeft U ⋙ pbcRestrict b ≅
      tensorLeft ((pbcRestrict b).obj U) :=
    NatIso.ofComponents (fun M ↦ e U M) (by
      intro M N f
      have hn :=
        (SheafOfModules.exists_changeOfRings_tensorCancellation b).choose_spec (𝟙 U) f
      change (pbcRestrict b).map
          (𝟙 U ⊗ₘ SheafOfModules.changeOfRingsHom b M f) ≫ (e U N).hom =
        (e U M).hom ≫ ((pbcRestrict b).map (𝟙 U) ⊗ₘ f) at hn
      change (pbcRestrict b).map
          (U ◁ SheafOfModules.changeOfRingsHom b M f) ≫ (e U N).hom =
        (e U M).hom ≫ ((pbcRestrict b).obj U ◁ f)
      rw [(pbcRestrict b).map_id U, id_tensorHom] at hn
      simpa only [id_tensorHom] using hn)
  exact α.symm ≪≫ isoWhiskerRight
    (isoWhiskerLeft (FiniteFieldTensor.tensorFunctor b) (leftUnitorNatIso _))
      (pbcRestrict b)

private def tensorRestriction (B : Type (u + 1)) [CommRing B]
    (b : adicLisseConstantRing Y B ⟶ T) (U : ModuleCat.{u + 1} B)
    (e : (adicLisseConstantModules Y B).obj U ≅
      (pbcRestrict b).obj (SheafOfModules.unit ((adicLisseForget Y).obj T))) :
    filteredCoefficientTensorFunctor Y B U ≅ pbcExtend b ⋙ pbcRestrict b := by
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing Y B)
  let := SheafOfModules.symmetricCategory (adicLisseConstantRing Y B)
  exact SheafOfModules.siteSheafTensorRightIso (adicLisseConstantRing Y B) _ ≪≫
    (tensoringRight _).mapIso e ≪≫ (BraidedCategory.tensorLeftIsoTensorRight _).symm ≪≫
      tensorUnitCancellation Y b ≪≫
        isoWhiskerRight (FiniteFieldTensor.pbcTensorIso Y b).symm (pbcRestrict b)

/-- Balanced tensor associativity when the last coefficient module is a restricted unit.
No flatness or condition on the complex is required. -/
theorem comparison (B : Type (u + 1)) [CommRing B]
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (a : R ⟶ adicLisseConstantRing Y B)
    (b : adicLisseConstantRing Y B ⟶ T) (p : R ⟶ A) (f : A ⟶ T)
    (h : p ≫ f = a ≫ b) (U : ModuleCat.{u + 1} B)
    (e : (adicLisseConstantModules Y B).obj U ≅
      (pbcRestrict b).obj (SheafOfModules.unit ((adicLisseForget Y).obj T)))
    (P : CochainComplex (pbcModules Y R) ℤ) :
    Nonempty (filteredCoefficientTensorComplex Y B R a P U ≅
      ((pbcRestrict b).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend f).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend p).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let α : FiniteFieldTensor.tensorFunctor a ⋙ filteredCoefficientTensorFunctor Y B U ≅
      (pbcExtend p ⋙ pbcExtend f) ⋙ pbcRestrict b :=
    isoWhiskerLeft _ (tensorRestriction Y B b U e) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        (isoWhiskerRight (FiniteFieldTensor.pbcTensorIso Y a).symm (pbcExtend b)) _ ≪≫
      isoWhiskerRight (extensionComp Y a b (a ≫ b) rfl) _ ≪≫
      isoWhiskerRight (extensionComp Y p f (a ≫ b) h).symm _
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ α.app (P.X i)) ?_⟩
  intro i j hij
  exact (α.hom.naturality (P.d i j)).symm

end ResidueLayerTensor
end AlgebraicGeometry.Scheme
