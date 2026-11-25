/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumInput
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumOrdinary
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Constant perfect complexes under the normalized stratum comparison

## References

* Bhatt--Scholze, Lemma 6.5.8(1) and Proposition 6.6.11
* Bhatt--Scholze, Lemma 6.5.8(1), Lemma 6.6.8, Proposition 6.6.11
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private instance proEt_small (S : Scheme.{u}) : EssentiallySmall.{u + 1} S.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private noncomputable def moduleLift (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  ModuleCat.uliftFunctor.{u + 1, u} A ⋙
    ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom

private theorem moduleLift_projective_finite (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) [Module.Projective A M] [Module.Finite A M] :
    Module.Projective (ULift.{u + 1} A) ((moduleLift A).obj M) ∧
      Module.Finite (ULift.{u + 1} A) ((moduleLift A).obj M) := by
  let e : A ≃+* ULift.{u + 1} A := ULift.ringEquiv.symm
  let N := (moduleLift A).obj M
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let se : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) M N :=
    { toFun := fun x ↦ ULift.up x
      invFun := fun x ↦ x.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨Module.Projective.of_equiv se,
    Module.Finite.of_surjective se.toLinearMap se.surjective⟩

private theorem completedDerivedModel (S : Scheme.{u})
    {R R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (φ : R ⟶ R')
    (C : CochainComplex (SheafOfModules.{u + 1} ((adicLisseForget S).obj R)) ℤ)
    (hk : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) C) :
    Nonempty ((completedAdicDerivedChange S φ).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (((completedAdicChange S φ).mapHomologicalComplex (.up ℤ)).obj C)) := by
  let X := completedAdicChange S φ
  let DX := completedAdicDerivedChange S φ
  obtain ⟨ε, _, _, hε⟩ := completedChangeModels S φ
  change DerivedCategory.Qh ⋙ DX ⟶ X.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh at ε
  change ∀ B, CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R) B →
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj B)) at hε
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := hε C hk
  exact ⟨DX.mapIso ((DerivedCategory.quotientCompQhIso _).app C).symm ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) ≪≫
    DerivedCategory.Qh.mapIso ((X.mapHomotopyCategoryFactors (.up ℤ)).app C) ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u + 1} ((adicLisseForget S).obj R'))).app
        ((X.mapHomologicalComplex (.up ℤ)).obj C)⟩

attribute [local irreducible] completedAdicDerivedChange

/-- The normalized coefficient comparison carries constant perfect realizations to
constant perfect realizations. No complete input object or residue charts are involved. -/
theorem integralResidueStratum_constant
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (g : S ⟶ T)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S)
    (P : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)))
    (hP : DerivedCategory.IsPerfectRingComplex P) :
    ∃ Q : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)),
      @DerivedCategory.IsPerfectRingComplex (PbcIntegralRing l E) _
        (HasDerivedCategory.standard _) Q ∧
      Nonempty
        ((integralResidueStratumPull T l E S g d c).obj
            ((integralConstantDerived T (pbcIntegralDatum l E)).obj Q) ≅
          (completedAdicDerivedChange S (completedAdicScalar S d)).obj
            ((residueLisseDerivedConstant S (Padic.coefficientExtensionIntegers l E)).obj P)) := by
  obtain ⟨B, a, b, ha, hb, hB, ⟨eP⟩⟩ := hP
  let A := Padic.coefficientExtensionIntegers l E
  let F := moduleLift A
  have : F.Faithful := by dsimp [F, moduleLift]; infer_instance
  have : F.Additive := by dsimp [F, moduleLift]; infer_instance
  have : PreservesFiniteLimits F := by dsimp [F, moduleLift]; infer_instance
  have : PreservesFiniteColimits F := by dsimp [F, moduleLift]; infer_instance
  let B' : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj B
  have hB' (i : ℤ) :
      Module.Projective (PbcIntegralRing l E) (B'.X i) ∧
        Module.Finite (PbcIntegralRing l E) (B'.X i) := by
    have := (hB i).1
    have := (hB i).2
    exact moduleLift_projective_finite A (B.X i)
  have ha' : B'.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff B F a).mpr ha
  have hb' : B'.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff B F b).mpr hb
  refine ⟨DerivedCategory.Q.obj B', ⟨B', a, b, ha', hb', hB', ⟨Iso.refl _⟩⟩, ?_⟩
  let I := integralConstantModule T (pbcIntegralDatum l E)
  let G := proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E))
    ((adicTowerInverseImage g).obj (pbcAdicCompletion T (pbcIntegralDatum l E)))
    (Iso.refl _)
  let H := pbcRestrict (integralResidueStratumCoefficient T l E S g d c).inv
  let K := koszulConstantFunctor S A
  let X := completedAdicChange S (completedAdicScalar S d)
  let DX := completedAdicDerivedChange S (completedAdicScalar S d)
  have : PreservesFiniteLimits I := (integralConstantModule_exact T _).1
  have : PreservesFiniteColimits I := (integralConstantModule_exact T _).2
  obtain ⟨e⟩ := integralResidueStratum_ordinary T l E S g d hd c
  let L := I ⋙ G ⋙ H
  let C : CochainComplex (SheafOfModules.{u + 1} (adicModuleRing S A)) ℤ :=
    (K.mapHomologicalComplex (.up ℤ)).obj B'
  have hbC : C.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff C b).2 fun i hi ↦
      K.map_isZero (B'.isZero_of_isStrictlyLE b i hi)
  have hk : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := adicConstantRing S A) C := by
    apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite.{u + 1, u, u + 1}
      (adicConstantRing S A) C b
    intro i
    have := (hB' i).1
    exact isFlatOnSite_constantModule.{u + 1, u} (ProEt.topology S) (ULift.{u + 1} A)
      (B'.X i) inferInstance
  obtain ⟨rightModel⟩ := completedDerivedModel S (completedAdicScalar S d) C hk
  let leftFactors : L.mapDerivedCategory ≅
      I.mapDerivedCategory ⋙ (G.mapDerivedCategory ⋙ H.mapDerivedCategory) :=
    (Functor.mapDerivedCategoryCompIso I (G ⋙ H)).symm ≪≫
      Functor.isoWhiskerLeft I.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).symm
  let leftModel :
      (integralResidueStratumPull T l E S g d c).obj
          ((integralConstantDerived T (pbcIntegralDatum l E)).obj (DerivedCategory.Q.obj B')) ≅
        DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj B') :=
    (leftFactors.app (DerivedCategory.Q.obj B')).symm ≪≫
      L.mapDerivedCategoryFactors.app B'
  let residueModel : (residueLisseDerivedConstant S A).obj P ≅
      DerivedCategory.Q.obj C :=
    (residueLisseDerivedConstant S A).mapIso eP ≪≫
      (ModuleCat.uliftFunctor.{u + 1, u} A ⋙
        ModuleCat.restrictScalars.{u + 1}
          (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom ⋙ K).mapDerivedCategoryFactors.app B
  exact ⟨leftModel ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (.up ℤ)).app B') ≪≫
    rightModel.symm ≪≫ DX.mapIso residueModel.symm⟩

end AlgebraicGeometry.Scheme
