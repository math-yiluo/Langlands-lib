/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.AlgebraicGeometry.PbcActualScalarPullback

/-! # Canonical coefficient change and ringed pullback

The recorded arbitrary ringed-topos tensor/pullback interface is reexported.
The helpers retain its ordinary adjunction and K-flat normalization for the
completed coefficient structure maps, which need not be isomorphisms.

## References

* Stacks Tags 03EL, 06YY, 0D6D and 099N
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_on_resolutions
    {C D : Type*} [Category C] [Category D] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (CochainComplex C ℤ))
    (hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : ObjectProperty.FullSubcategory
          (show ObjectProperty (HomotopyCategory C (.up ℤ)) from fun K ↦ P K.as))
        (s : L.obj ⟶ K), HomotopyCategory.quasiIso C (.up ℤ) s)
    (F G : DerivedCategory C ⥤ D) (U V : CochainComplex C ℤ ⥤ D)
    (l : DerivedCategory.Q ⋙ F ⟶ U) (r : DerivedCategory.Q ⋙ G ⟶ V)
    (b : U ≅ V) (hl : ∀ K : P.FullSubcategory, IsIso (l.app K.obj))
    (hr : ∀ K : P.FullSubcategory, IsIso (r.app K.obj)) :
    ∃! e : F ≅ G, ∀ K : CochainComplex C ℤ, P K →
      e.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = l.app K ≫ b.hom.app K := by
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have : (H.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage H.ι) :=
    CategoryTheory.restriction_localization _ _ H hres
  let f := H.lift (P.ι ⋙ HomotopyCategory.quotient C (.up ℤ)) (fun K ↦ K.property)
  have : f.Full := ⟨by
    intro K L a
    obtain ⟨b, hb⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective a.hom
    refine ⟨ObjectProperty.homMk b, ?_⟩
    apply ObjectProperty.hom_ext
    exact hb⟩
  have : f.EssSurj := ⟨by
    intro K
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, ⟨ObjectProperty.isoMk H (eqToIso hL)⟩⟩
    change H ((HomotopyCategory.quotient C (.up ℤ)).obj L)
    exact hL.symm ▸ K.property⟩
  let ff₀ := (Localization.fullyFaithfulWhiskeringLeft (H.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso C (.up ℤ)).inverseImage H.ι) D).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f D)
  let ff := ff₀.ofIso ((whiskeringLeft _ _ D).mapIso
    (isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso C)))
  let el : P.ι ⋙ DerivedCategory.Q ⋙ F ≅ P.ι ⋙ U :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (l.app K.obj) (hl K))
      (fun a ↦ l.naturality a.hom)
  let er : P.ι ⋙ DerivedCategory.Q ⋙ G ≅ P.ι ⋙ V :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ (r.app K.obj) (hr K))
      (fun a ↦ r.naturality a.hom)
  let e₀ := el ≪≫ isoWhiskerLeft P.ι b ≪≫ er.symm
  let e : F ≅ G := ff.preimageIso e₀
  have he (K : P.FullSubcategory) : e.hom.app (DerivedCategory.Q.obj K.obj) =
      e₀.hom.app K := congrArg (fun z ↦ z.app K)
      (ff.map_preimage (X := F) (Y := G) e₀.hom)
  have hn (K : CochainComplex C ℤ) (hp : P K) :
      e.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = l.app K ≫ b.hom.app K := by
    rw [he ⟨K, hp⟩]
    have := hr ⟨K, hp⟩
    change (l.app K ≫ b.hom.app K ≫ CategoryTheory.inv (r.app K)) ≫ r.app K = _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ff.map_injective
  ext K
  apply (cancel_mono (er.hom.app K)).1
  change e'.hom.app (DerivedCategory.Q.obj K.obj) ≫ r.app K.obj =
    e.hom.app (DerivedCategory.Q.obj K.obj) ≫ r.app K.obj
  exact (he' K.obj K.property).trans (hn K.obj K.property).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_good (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion Y dA) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := pbcAdicCompletion X dA)
      ((((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g (pbcAdicCompletion Y dA)
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 Y)).2.2.2.1
  have : (I.modules ⋙ reductionChange X (completedCoefficientMap g dA)).Additive := by
    rw [hI]
    exact completedModulePullback_additive g dA
  have ho := (reductionChangeExistence X (completedCoefficientMap g dA)).choose_spec.choose
  have hpres := SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1))) I (completedCoefficientMap g dA)
    (I.modules ⋙ reductionChange X (completedCoefficientMap g dA))
    (fun M ↦ ho (I.modules.obj M))
    (fun a ↦
      (reductionChangeExistence X (completedCoefficientMap g dA)).choose_spec.choose_spec.choose
        (I.modules.map a)) P hp hf
  simpa only [hI, pbcActualModulePull, completedModulePullback] using hpres

private theorem scalar_good (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hflat (n : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X n)) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R (P.X n)) (hf n)
  exact (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    φ P (pbcExtend φ) (pbcExtensionExistence φ).choose_spec.choose
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose hp hflat).1

private def complexCounit {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) eps ≫
    whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso D).hom

private theorem scalar_counit_iso (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) (hp : P.IsKFlatIndependentCoefficients) :
    IsIso (pbcComplexCounit φ P) := by
  have := pbcExtensionCounit_isIso φ P hp
  dsimp only [pbcComplexCounit]
  infer_instance

private theorem pull_counit_iso
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ)
    (hp : P.IsKFlatIndependentCoefficients) : IsIso (pbcActualPullComplexCounit g dA P) := by
  have : IsIso ((pbcActualPullCounit g dA).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    delta pbcActualPullCounit completedOrdinaryPullbackCounit completedOrdinaryPullback
    exact (completedOrdinaryPullback_exists g dA).choose_spec.choose_spec.2 P hp
  dsimp only [pbcActualPullComplexCounit]
  infer_instance

-- Keep completed coefficient objects out of the sectionwise construction.
set_option backward.isDefEq.respectTransparency false in
private theorem scalar_right
    {RA RB : Sheaf (ProEt.topology Y) RingCat.{u + 1}}
    {SA SB : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (ay : RA ⟶ RB) (ax : SA ⟶ SB)
    (aR : RA ⟶ (proEtaleSheafDirectImage g RingCat.{u + 1}).obj SA)
    (aS : RB ⟶ (proEtaleSheafDirectImage g RingCat.{u + 1}).obj SB)
    (h : ay ≫ aS = aR ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map ax) :
    ∃! δ : SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) aS ⋙
        SheafOfModules.restrictScalars ay ≅
      SheafOfModules.restrictScalars ax ⋙
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) aR,
      ∀ (N : SheafOfModules.{u + 1} SB) (U : Y.ProEtᵒᵖ)
        (x : ((SheafOfModules.pushforward (F := proEtaleBaseChange g) aS).obj N).val.obj U),
        (δ.hom.app N).val.app U x = x := by
  refine ⟨SheafOfModules.pushforwardCongr (F := proEtaleBaseChange g) h, ?_, ?_⟩
  · intro N U x
    rfl
  · intro e' he'
    apply Iso.ext
    ext N U x
    exact he' N U x

variable (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
    pbcActualStructureMap g dA ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))

set_option backward.isDefEq.respectTransparency false in
include hφ in
/-- The two right-adjoint composites agree by the coefficient square, with identity
underlying section maps. -/
theorem pbcActualScalarRightIso_exists :
    ∃! δ : pbcActualModulePush g dB ⋙
        SheafOfModules.restrictScalars.{u + 1} (pbcActualCoefficientRingMap Y φY) ≅
      SheafOfModules.restrictScalars.{u + 1} (pbcActualCoefficientRingMap X φX) ⋙
        pbcActualModulePush g dA,
      ∀ (N : pbcModules X (pbcAdicCompletion X dB)) (U : Y.ProEtᵒᵖ)
        (x : ((pbcActualModulePush g dB).obj N).val.obj U),
          (δ.hom.app N).val.app U x = x := by
  exact scalar_right g (pbcActualCoefficientRingMap Y φY)
    (pbcActualCoefficientRingMap X φX) (pbcActualStructureMap g dA)
    (pbcActualStructureMap g dB) hφ

/-- The identity-on-sections right-adjoint comparison, retaining its coefficient square. -/
def pbcActualScalarRightIso := (pbcActualScalarRightIso_exists g dA dB φY φX hφ).exists.choose

/-- The ordinary scalar/pullback comparison is the conjugate of the identity section
comparison under the actual tensor-unit-normalized adjunctions. -/
def pbcActualScalarOrdinaryPullIso :
    pbcExtend φY ⋙ pbcActualModulePull g dB ≅
      pbcActualModulePull g dA ⋙ pbcExtend φX :=
  ((conjugateIsoEquiv
    ((pbcScalarAdjunction φY).comp
      (pbcActualModuleAdjunction g dB))
    ((pbcActualModuleAdjunction g dA).comp
        (pbcScalarAdjunction φX))).symm
      (pbcActualScalarRightIso g dA dB φY φX hφ)).symm

/-- The same canonical comparison on actual cochain complexes, degree by degree. -/
def pbcActualScalarOrdinaryPullComplexIso :
    (pbcExtend φY).mapHomologicalComplex (.up ℤ) ⋙
      (pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ) ≅
    (pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend φX).mapHomologicalComplex (.up ℤ) :=
  letI : (pbcExtend φY).Additive := inferInstance
  letI : (pbcExtend φX).Additive := inferInstance
  letI : (pbcActualModulePull g dA).Additive := pbcActualModulePull_additive g dA
  letI : (pbcActualModulePull g dB).Additive := pbcActualModulePull_additive g dB
  Functor.mapHomologicalComplexCompIso
    (F := pbcExtend φY) (G := pbcActualModulePull g dB)
    (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (pbcActualScalarOrdinaryPullIso g dA dB φY φX hφ) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := pbcActualModulePull g dA) (G := pbcExtend φX)
        (Iso.refl _) (.up ℤ)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The derived scalar/pullback comparison retains the ordinary adjunction conjugate
on flat-term K-flat representatives. -/
theorem pbcActualScalarDerivedPullIso_exists :
    ∃! e : pbcDerivedExtend φY ⋙ pbcActualDerivedPull g dB ≅
        pbcActualDerivedPull g dA ⋙ pbcDerivedExtend φX,
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion Y dA) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion Y dA) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g dA P) ≫
          pbcComplexCounit φX
            (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) =
        (pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
          pbcActualPullComplexCounit g dB
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).hom.app
            P) := by
  -- Restriction to flat-term K-flat complexes is fully faithful on derived functors.
  let C := pbcModules Y (pbcAdicCompletion Y dA)
  let P : ObjectProperty (CochainComplex C ℤ) := fun K ↦
    K.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := pbcAdicCompletion Y dA) (K.X n)
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : H.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso C (.up ℤ) s := by
    intro K
    obtain ⟨L, s, hl, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K.as
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj L, hl, ?_⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion Y dA) (L.X n)).symm (hf n)
  let FY := (pbcExtend φY).mapHomologicalComplex (.up ℤ)
  let FX := (pbcExtend φX).mapHomologicalComplex (.up ℤ)
  let GA := (pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)
  let GB := (pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ)
  let LY := pbcDerivedExtend φY
  let LX := pbcDerivedExtend φX
  let LA := pbcActualDerivedPull g dA
  let LB := pbcActualDerivedPull g dB
  -- Both composite counits are invertible on the resolving class.
  let cy := complexCounit (pbcExtend φY) LY (pbcExtensionCounit φY)
  let cx := complexCounit (pbcExtend φX) LX (pbcExtensionCounit φX)
  let ca := complexCounit (pbcActualModulePull g dA) LA (pbcActualPullCounit g dA)
  let cb := complexCounit (pbcActualModulePull g dB) LB (pbcActualPullCounit g dB)
  let l : DerivedCategory.Q ⋙ (LY ⋙ LB) ⟶ (FY ⋙ GB) ⋙ DerivedCategory.Q :=
    whiskerRight cy LB ≫ whiskerLeft FY cb
  let r : DerivedCategory.Q ⋙ (LA ⋙ LX) ⟶ (GA ⋙ FX) ⋙ DerivedCategory.Q :=
    whiskerRight ca LX ≫ whiskerLeft GA cx
  have hl (K : P.FullSubcategory) : IsIso (l.app K.obj) := by
    have := scalar_counit_iso Y φY K.obj K.property.1
    have := pull_counit_iso g dB (FY.obj K.obj)
      (scalar_good Y φY K.obj K.property.1 K.property.2)
    change IsIso (LB.map (pbcComplexCounit φY K.obj) ≫
      pbcActualPullComplexCounit g dB (FY.obj K.obj))
    infer_instance
  have hr (K : P.FullSubcategory) : IsIso (r.app K.obj) := by
    have := pull_counit_iso g dA K.obj K.property.1
    have := scalar_counit_iso X φX (GA.obj K.obj)
      (pull_good g dA K.obj K.property.1 K.property.2).1
    change IsIso (LX.map (pbcActualPullComplexCounit g dA K.obj) ≫
      pbcComplexCounit φX (GA.obj K.obj))
    infer_instance
  let b := isoWhiskerRight
    (pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ) DerivedCategory.Q
  obtain ⟨e, he, hu⟩ := comparison_on_resolutions P hres (LY ⋙ LB) (LA ⋙ LX)
    ((FY ⋙ GB) ⋙ DerivedCategory.Q) ((GA ⋙ FX) ⋙ DerivedCategory.Q) l r b hl hr
  have normalize (e' : LY ⋙ LB ≅ LA ⋙ LX) (K : CochainComplex C ℤ) :
      (e'.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = l.app K ≫ b.hom.app K) ↔
        (e'.hom.app (DerivedCategory.Q.obj K) ≫
          (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g dA K) ≫
          pbcComplexCounit φX (GA.obj K) =
        (pbcActualDerivedPull g dB).map (pbcComplexCounit φY K) ≫
          pbcActualPullComplexCounit g dB (FY.obj K) ≫
          DerivedCategory.Q.map
            ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).hom.app K)) := by
    simp only [l, r, b, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      cy, cx, ca, cb, complexCounit, pbcComplexCounit, pbcActualPullComplexCounit,
      isoWhiskerRight_hom, Category.assoc]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro K hp hf
    exact (normalize e K).1 (he K ⟨hp, hf⟩)
  · intro e' he'
    apply hu e'
    intro K hp
    exact (normalize e' K).2 (he' K hp.1 hp.2)

/-- The canonical derived coefficient/pullback comparison, with its normalization retained. -/
def pbcActualScalarDerivedPullIso :=
  (pbcActualScalarDerivedPullIso_exists g dA dB φY φX hφ).exists.choose

/-- The direct-image scalar comparison is the actual adjunction mate of the normalized
ordinary-derived pullback comparison, before completeness or constructibility. -/
def pbcActualScalarDirectImageMap :
    pbcActualDerivedPush g dA ⋙ pbcDerivedExtend φY ⟶
      pbcDerivedExtend φX ⋙ pbcActualDerivedPush g dB :=
  (mateEquiv (pbcActualDerivedAdjunction g dA) (pbcActualDerivedAdjunction g dB)
    (TwoSquare.mk _ _ _ _ (pbcActualScalarDerivedPullIso g dA dB φY φX hφ).hom))

end AlgebraicGeometry.Scheme
