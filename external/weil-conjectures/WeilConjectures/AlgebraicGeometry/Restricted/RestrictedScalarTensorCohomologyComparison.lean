/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackHomology
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement

/-! # Underlying cohomology of K-flat coefficient change

## References

* Stacks Project, Tags 06YY, 06YU, 03DA and 00YV
-/

@[expose] public section
set_option autoImplicit false
universe u wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The actual constant coefficient map with independently lifted coefficients. -/
noncomputable abbrev restrictedScalarRingMap (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} B ≃+* B).symm.toRingHom.comp
        (f.comp (ULift.ringEquiv : ULift.{u + 1, u} A ≃+* A).toRingHom)))

/-- The target coefficient module, restricted to the source ring and placed in degree zero. -/
noncomputable def restrictedScalarCoefficientComplex (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj
    ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (restrictedScalarRingMap T f))).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T B))))

/-- Standard-universe tensor cohomology, before choosing a localization universe. -/
noncomputable abbrev restrictedScalarTensorCohomology (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (q : ℤ) :=
  (DerivedCategory.homologyFunctor
    (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj
      (derivedTensor T A P (restrictedScalarCoefficientComplex T f)
        P (𝟙 P) (by infer_instance) hP)

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheafComparison
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    Nonempty (SheafOfModules.changeOfRingsPresheaf c M ≅
      SheafOfModules.changeOfRingsPresheafOfUniverses c M) := by
  refine ⟨PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_⟩
  intro U W g
  change SheafOfModules.changeOfRingsMap c M g =
    SheafOfModules.changeOfRingsMapOfUniverses c M g
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  rw [SheafOfModules.changeOfRingsMap_tmul,
    SheafOfModules.changeOfRingsMap_tmulOfUniverses]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackUnderlying {T X : Scheme.{u}} (a : X ⟶ T)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A)) :
    Nonempty (((sheafCompose (ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf _).obj (proEtaleConstantModulePullback a A F))) ≅
      (AlgebraicGeometry.ProEtale.setPullback a).obj
        ((sheafCompose (ProEt.topology T)
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((SheafOfModules.toSheaf _).obj F))) := by
  have := constantComparison_isIso a A
  let c := asIso (proEtaleCoefficientInverseImageMap a A)
  let M := (proEtaleModuleInverseImage a (proEtaleConstantRing T A)).obj F
  obtain ⟨theta, _⟩ := SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let V := SheafOfModules.toSheaf ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)) ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let ec := (extensionPresheafComparison c.hom M).some
  let es := (PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X A)).obj)).mapIso ec
  exact ⟨V.mapIso (es ≪≫ theta M) ≪≫ (ProEtaleTensorComparison.moduleSetsIdentification a F).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extensionUnderlyingTensorIso
    (T : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (proEtaleRingModules T (proEtaleConstantRing T A))]
    [HasDerivedCategory.{wB} (proEtaleRingModules T (proEtaleConstantRing T B))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, wA, wB}
      (restrictedScalarRingMap T f)) :
    letI := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
    let J := ProEt.topology T
    let VA := SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A))
    let VB := SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T B))
    let N := (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (restrictedScalarRingMap T f))).obj (SheafOfModules.unit _)
    Nonempty (D.E ⋙ VB ≅ MonoidalCategory.tensorRight N ⋙ VA) := by
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
  let := SheafOfModules.symmetricCategory (proEtaleConstantRing T A)
  let J := ProEt.topology T
  let VA := SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing T A))
  let VB := SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing T B))
  let N := (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (restrictedScalarRingMap T f))).obj (SheafOfModules.unit _)
  obtain ⟨e, he⟩ :=
    SheafOfModules.exists_changeOfRings_tensor_comparison_independent
      (restrictedScalarRingMap T f)
  let t : D.E ⋙ VB ≅ MonoidalCategory.tensorLeft N ⋙ VA :=
    NatIso.ofComponents (fun M ↦ VB.mapIso (eqToIso (D.obj_eq M)) ≪≫ e M) (by
      intro M M' g
      change VB.map (D.E.map g) ≫ (VB.map (eqToHom (D.obj_eq M')) ≫ (e M').hom) =
        (VB.map (eqToHom (D.obj_eq M)) ≫ (e M).hom) ≫ _
      have hg : D.E.map g ≫ eqToHom (D.obj_eq M') =
          eqToHom (D.obj_eq M) ≫ SheafOfModules.changeOfRingsHom
            (restrictedScalarRingMap T f) M g := by
        rw [D.map_eq]
        simp
      rw [← VB.map_comp_assoc, hg, VB.map_comp, Category.assoc, he,
        ← Category.assoc]
      rfl)
  exact ⟨t ≪≫ Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight N) VA⟩

/-- Forgetting the target coefficient action identifies K-flat scalar extension
cohomology, after arbitrary pullback, with the underlying cohomology of the tensor
with the restricted target coefficient in degree zero. -/
theorem restrictedScalarTensorCohomologyComparison
    {T X : Scheme.{u}} (a : X ⟶ T)
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wA} (proEtaleRingModules T (proEtaleConstantRing T A))]
    [HasDerivedCategory.{wB} (proEtaleRingModules T (proEtaleConstantRing T B))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, wA, wB}
      (restrictedScalarRingMap T f))
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (q : ℤ) :
    Nonempty
      (((sheafCompose (ProEt.topology X)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf _).obj
          (proEtaleConstantModulePullback a B
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules T (proEtaleConstantRing T B)) q).obj
                (D.T.obj (DerivedCategory.Q.obj P)))))) ≅
      ((sheafCompose (ProEt.topology X)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((SheafOfModules.toSheaf _).obj
          (proEtaleConstantModulePullback a A
            (restrictedScalarTensorCohomology T f P hP q)))))  := by
  let R := proEtaleConstantRing T A
  let J := ProEt.topology T
  let 𝒜 := proEtaleRingModules T R
  let ℬ := proEtaleRingModules T (proEtaleConstantRing T B)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let VA := SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let VB := SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing T B))
  let N := (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (restrictedScalarRingMap T f))).obj (SheafOfModules.unit _)
  let EP := (D.E.mapHomologicalComplex (.up ℤ)).obj P
  let Z := CochainComplex.mapBifunctor P
    ((HomologicalComplex.single 𝒜 (.up ℤ) 0).obj N) (curriedTensor 𝒜)
  obtain ⟨t⟩ := extensionUnderlyingTensorIso T f D
  let et : Z ≅ ((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P :=
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor 𝒜) N P
  let ec : (VB.mapHomologicalComplex (.up ℤ)).obj EP ≅
      (VA.mapHomologicalComplex (.up ℤ)).obj Z :=
    (NatIso.mapHomologicalComplex t (.up ℤ)).app P ≪≫
      (VA.mapHomologicalComplex (.up ℤ)).mapIso et.symm
  have hPi : P.IsKFlatIndependentCoefficients :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hP
  have := D.computes P hPi
  let eHA : Z.homology q ≅ restrictedScalarTensorCohomology T f P hP q := by
    letI := HasDerivedCategory.standard 𝒜
    exact ((DerivedCategory.homologyFunctorFactors 𝒜 q).app Z).symm
  let eH : VB.obj ((DerivedCategory.homologyFunctor ℬ q).obj
      (D.T.obj (DerivedCategory.Q.obj P))) ≅
      VA.obj (restrictedScalarTensorCohomology T f P hP q) :=
    VB.mapIso ((DerivedCategory.homologyFunctor ℬ q).mapIso (asIso (D.ε.app P)) ≪≫
      (DerivedCategory.homologyFunctorFactors ℬ q).app EP) ≪≫
    ((EP.sc q).mapHomologyIso VB).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso ec ≪≫
    (Z.sc q).mapHomologyIso VA ≪≫ VA.mapIso eHA
  exact ⟨(pullbackUnderlying a B _).some ≪≫
    (AlgebraicGeometry.ProEtale.setPullback a).mapIso
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso eH) ≪≫
    (pullbackUnderlying a A (restrictedScalarTensorCohomology T f P hP q)).some.symm⟩

end AlgebraicGeometry.Scheme
