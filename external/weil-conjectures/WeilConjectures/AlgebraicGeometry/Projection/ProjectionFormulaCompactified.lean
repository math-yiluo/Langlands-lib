/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateSlicePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The compactified projection formula for locally perfect coefficients

## References

* Stacks, Tags 03DI and 015F
* Stacks, Tags 03DI and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

private theorem mixedTensor {R : Sheaf J CommRingCat.{u + 1}} (a : TensorModel R)
    (P Q : CochainComplex (Mod R) ℤ) (hq : resolving R Q) :
    Nonempty (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((total R).obj (P, Q))) := by
  let := SheafOfModules.monoidalCategory R
  let := a.preadditive
  obtain ⟨A, f, hk, hf, hqf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  let ha : resolving R A := ⟨hk, fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (A.X n)).symm (hf n)⟩
  have : QuasiIso f := hqf
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hqf
  let g := HomologicalComplex.mapBifunctorMap f (𝟙 Q) (tensor R) (.up ℤ)
  have hg : QuasiIso g := by
    have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hqf
    have ht := hq.1 (CochainComplex.mappingCone f) hc
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    intro i
    exact (ht i).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f Q (tensor R))
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  exact ⟨a.functor.mapIso (Iso.prod (asIso (DerivedCategory.Q.map f)).symm
      (Iso.refl _)) ≪≫
    (a.representative.app (⟨A, ha⟩, ⟨Q, hq⟩)).symm ≪≫ asIso (DerivedCategory.Q.map g)⟩

private theorem tensor_extension_supported (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (E : Der (R.over U)) (F : Der R) :
    (localizedModuleExtension R U).mapDerivedCategory.essImage
      (a.functor.obj ((localizedModuleExtension R U).mapDerivedCategory.obj E, F)) := by
  let L := localizedModuleExtension R U
  let P := DerivedCategory.Q.objPreimage E
  let N := DerivedCategory.Q.objPreimage F
  obtain ⟨Q, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients N
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  let hQ : resolving R Q := ⟨hk, fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)).symm (hf n)⟩
  let eF : DerivedCategory.Q.obj Q ≅ F :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso F
  let eE : L.mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
    L.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      L.mapDerivedCategoryFactors.app P
  obtain ⟨mixed⟩ := mixedTensor a ((L.mapHomologicalComplex (.up ℤ)).obj P) Q hQ
  obtain ⟨totalIso⟩ := extension_total_iso R U P Q
  let W := (total (R.over U)).obj
    (P, ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ)).obj Q)
  let e : a.functor.obj (L.mapDerivedCategory.obj E, F) ≅
      L.mapDerivedCategory.obj (DerivedCategory.Q.obj W) :=
    a.functor.mapIso (Iso.prod eE eF.symm) ≪≫ mixed ≪≫
      DerivedCategory.Q.mapIso totalIso.symm ≪≫ (L.mapDerivedCategoryFactors.app W).symm
  exact Functor.essImage.ofIso e.symm
    (L.mapDerivedCategory.obj_mem_essImage (DerivedCategory.Q.obj W))

end SheafOfModules

namespace AlgebraicGeometry.Scheme
section Open

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ S)

/-- The derived open adjunction is the localization of the termwise ordinary adjunction. -/
def proEtaleRingDerivedOpenAdjunction :
    proEtaleRingDerivedOpenExtension j R S c ⊣ proEtaleRingDerivedPullback j R S c :=
  letI : CatCommSq
      ((proEtaleRingOpenExtension j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedOpenExtension j R S c) :=
    ⟨(proEtaleRingOpenExtension j R S c).mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq
      ((proEtaleRingModulePullback j R S c).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (proEtaleRingDerivedPullback j R S c) :=
    ⟨(proEtaleRingModulePullback j R S c).mapDerivedCategoryFactors.symm⟩
  let am : proEtaleRingOpenExtension j R S c ⊣ proEtaleRingModulePullback j R S c :=
    Adjunction.ofIsRightAdjoint _
  (am.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (proEtaleRingDerivedOpenExtension j R S c) (proEtaleRingDerivedPullback j R S c)

/-- The adjunction projection is exactly the transpose of unit tensor identity. -/
def proEtaleOpenProjection
    (a : ProEtaleTensorModel Z R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (M : DerivedCategory (proEtaleRingModules Z R)) :
    (proEtaleRingDerivedOpenExtension j R S c).obj
        (b.tensor.obj (E, (proEtaleRingDerivedPullback j R S c).obj M)) ⟶
      a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M) :=
  ((proEtaleRingDerivedOpenAdjunction j R S c).homEquiv _ _).symm
    (b.tensor.map (Prod.mkHom ((proEtaleRingDerivedOpenAdjunction j R S c).unit.app E)
      (𝟙 _)) ≫ (proEtaleCanonicalTensorComparison j R S c a b).inv.app
        ((proEtaleRingDerivedOpenExtension j R S c).obj E, M))

private theorem openProjection_isIso
    (a : ProEtaleTensorModel Z R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (M : DerivedCategory (proEtaleRingModules Z R)) :
    IsIso (proEtaleOpenProjection j R S c a b E M) := by
  classical
  obtain ⟨e, ⟨he⟩⟩ := proEtaleOpen_slicePresentation j R S c
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let de := e.mapDerivedCategory
  let L := (SheafOfModules.localizedModuleExtension R (ProEt.mk j)).mapDerivedCategory
  let hder : proEtaleRingDerivedOpenExtension j R S c ≅ de.functor ⋙ L :=
    Functor.mapDerivedCategoryNatIso he ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  let adjL := SheafOfModules.localizedModuleDerivedAdjunction R (ProEt.mk j)
  have : IsIso adjL.unit := SheafOfModules.localizedDerivedUnit_isIso j R
  have : L.Full := adjL.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := adjL.fullyFaithfulLOfIsIsoUnit.faithful
  have : (proEtaleRingDerivedOpenExtension j R S c).Full :=
    Functor.Full.of_iso hder.symm
  have : (proEtaleRingDerivedOpenExtension j R S c).Faithful :=
    Functor.Faithful.of_iso hder.symm
  let adj := proEtaleRingDerivedOpenAdjunction j R S c
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  obtain ⟨g, _, _, _⟩ := ringedProjectionRestriction j R S c
  obtain ⟨t, _⟩ := tensorModelIso a g.tensorY
  let tensorIso : a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M) ≅
      g.tensorY.functor.obj (L.obj (de.functor.obj E), M) :=
    t.app _ ≪≫ g.tensorY.functor.mapIso (Iso.prod (hder.app E) (Iso.refl M))
  obtain ⟨W, ⟨hW⟩⟩ := SheafOfModules.tensor_extension_supported R (ProEt.mk j)
    g.tensorY (de.functor.obj E) M
  have hs : (proEtaleRingDerivedOpenExtension j R S c).essImage
      (a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M)) :=
    ⟨de.inverse.obj W, ⟨hder.app _ ≪≫ L.mapIso (de.counitIso.app W) ≪≫
      hW ≪≫ tensorIso.symm⟩⟩
  have : IsIso (adj.counit.app
      (a.tensor.obj ((proEtaleRingDerivedOpenExtension j R S c).obj E, M))) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr hs
  have : IsIso (Prod.mkHom (adj.unit.app E)
      (𝟙 ((proEtaleRingDerivedPullback j R S c).obj M))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  unfold proEtaleOpenProjection
  rw [Adjunction.homEquiv_counit]
  infer_instance

private theorem strictPerfect_isoLocus
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (F G : DerivedCategory C ⥤ DerivedCategory C)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (B : C) (hB : τ.isoLocus ((DerivedCategory.singleFunctor C 0).obj B))
    (T : CochainComplex C ℤ) (lo hi : ℤ)
    (hb : ∀ n : ℤ, n < lo ∨ hi < n → IsZero (T.X n))
    (rank : ℤ → ℕ) (i : ∀ n, T.X n ⟶ ∏ᶜ fun _ : Fin (rank n) ↦ B)
    (p : ∀ n, (∏ᶜ fun _ : Fin (rank n) ↦ B) ⟶ T.X n)
    (split : ∀ n, i n ≫ p n = 𝟙 _) :
    τ.isoLocus (DerivedCategory.Q.obj T) := by
  let H := DerivedCategory.singleFunctor C 0
  apply CategoryTheory.bounded_complex_mem_triangulated τ.isoLocus T lo hi hb
  intro n _ _
  have hfree : τ.isoLocus (H.obj (∏ᶜ fun _ : Fin (rank n) ↦ B)) :=
    τ.isoLocus.prop_of_isLimit
      (isLimitOfPreserves H (limit.isLimit
        (Discrete.functor (fun _ : Fin (rank n) ↦ B)))) (fun _ ↦ hB)
  exact τ.isoLocus.prop_of_retract ((show Retract (T.X n)
    (∏ᶜ fun _ : Fin (rank n) ↦ B) from ⟨i n, p n, split n⟩).map H) hfree

private theorem sitePerfect_projection_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (E : DerivedCategory (proEtaleRingModules X S))
    (Q : DerivedCategory (proEtaleRingModules Y R))
    (hQ : IsProEtaleSitePerfect Y R Q) :
    IsIso (proEtaleProjectionFormulaMate f R S c a b E Q) := by
  classical
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let (U : Y.ProEt) : HasDerivedCategory (SheafOfModules.{u + 1} (A.over U)) :=
    HasDerivedCategory.standard _
  obtain ⟨sF, sG, hF, hG, τ, hτ, hs, hu⟩ :=
    proEtaleProjectionMateExact f R S c a b E
  let := sF
  let := sG
  have := hF
  have := hG
  have := hs
  obtain ⟨T, hT, ⟨e⟩⟩ := hQ
  apply SheafOfModules.ringedRestrictionLocalIso A
  intro V
  obtain ⟨cover, hcover, hlocal⟩ := hT V
  refine ⟨cover, hcover, ?_⟩
  intro U q hq
  obtain ⟨B, ⟨lo, hi, hb⟩, ⟨pkg⟩, z, hz⟩ := hlocal U q hq
  have := hz
  let r := ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2} A U
  let L := SheafOfModules.overFunctor.{u + 1} A U
  have : L.Additive := (ringedOverFunctor_exactGeneral A U).1
  have : PreservesFiniteLimits L :=
    (ringedOverFunctor_exactGeneral A U).2.1
  have : PreservesFiniteColimits L :=
    (ringedOverFunctor_exactGeneral A U).2.2
  let model : r.obj Q ≅ DerivedCategory.Q.obj B :=
    r.mapIso e ≪≫ L.mapDerivedCategoryFactors.app T ≪≫
      (asIso (DerivedCategory.Q.map z)).symm
  obtain ⟨loc⟩ := proEtaleProjectionMateSlicePresentation f R S c a b E U
  let := loc.sourceShift
  let := loc.targetShift
  have := loc.sourceExact
  have := loc.targetExact
  have := loc.shiftCompatible
  let one := (DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
    (SheafOfModules.unit A)
  have hunit : IsIso (proEtaleProjectionFormulaMate f R S c a b E one) :=
    (congrArg IsIso (hτ one)).mp hu
  have hlocalunit : IsIso (loc.mate.app (r.obj one)) := by
    have : IsIso (loc.sourceComparison.hom.app one ≫ loc.mate.app (r.obj one)) := by
      rw [← loc.equation one]
      infer_instance
    exact IsIso.of_isIso_comp_left (loc.sourceComparison.hom.app one) _
  let unitIso : r.obj one ≅ (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (A.over U)) :=
    (L.mapDerivedCategorySingleFunctor 0).app (SheafOfModules.unit A)
  have hunit' : IsIso (loc.mate.app ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (A.over U)))) :=
    (NatTrans.isIso_app_iff_of_iso loc.mate unitIso).mp hlocalunit
  have hB := strictPerfect_isoLocus loc.source loc.target loc.mate _ hunit'
    B lo hi hb pkg.N pkg.i pkg.p pkg.splitting
  have : IsIso (loc.mate.app (r.obj Q)) :=
    (NatTrans.isIso_app_iff_of_iso loc.mate model).mpr hB
  have : IsIso (r.map (proEtaleProjectionFormulaMate f R S c a b E Q) ≫
      loc.targetComparison.hom.app Q) := by
    rw [loc.equation Q]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (loc.targetComparison.hom.app Q)

end Open
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {H : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf H CommRingCat.{u + 1}}
  {F : C ⥤ D} (o : Operation F R S) (t : o.OrdinaryTensor)

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f) [QuasiCompact d.i]
  (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RZ : Sheaf (ProEt.topology d.Z) CommRingCat.{u + 1})
  (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (cp : (proEtaleSheafInverseImage d.g CommRingCat.{u + 1}).obj RY ≅ RZ)
  (cj : (proEtaleSheafInverseImage d.i CommRingCat.{u + 1}).obj RZ ≅ RX)
  (a : ProEtaleTensorModel Y RY) (b : ProEtaleTensorModel d.Z RZ)
  (c : ProEtaleTensorModel X RX)
  (E : DerivedCategory (proEtaleRingModules X RX))
  (Q : DerivedCategory (proEtaleRingModules Y RY))

/-- The first arrow is the adjoint of counit tensor identity for p and j_!E. -/
def compactifiedProjectionPi :=
  derivedProjectionFormulaMate (proEtaleRingDerivedPullback d.g RY RZ cp)
    (proEtaleRingDerivedDirectImage d.g RY RZ cp)
    (proEtaleRingDerivedAdjunction d.g RY RZ cp) a.tensor b.tensor
    (proEtaleCanonicalTensorComparison d.g RY RZ cp a b)
    ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q

/-- Theta is alpha inverse followed by extension of identity tensor c inverse.
The factorization identifies f with d.i followed by d.g; its coefficient identification
is exactly the composite identification, with no independent third choice. -/
def compactifiedProjectionTheta
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :
    b.tensor.obj ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E,
        (proEtaleRingDerivedPullback d.g RY RZ cp).obj Q) ≅
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj
        (c.tensor.obj (E, (proEtaleRingDerivedPullback (d.i ≫ d.g) RY RX
          (proEtaleRingCompositeCoefficients d.i d.g RY RZ RX cp cj)).obj Q)) :=
  (@asIso _ _ _ _ (proEtaleOpenProjection d.i RZ RX cj b c E
    ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)) hα).symm ≪≫
      (proEtaleRingDerivedOpenExtension d.i RZ RX cj).mapIso
        (c.tensor.mapIso (Iso.prod (Iso.refl E)
          ((proEtaleCanonicalPullbackComposition d.i d.g RY RZ RX cp cj).app Q).symm))

/-- The ordered forward map pi followed by Rp_* theta. -/
def compactifiedProjectionForward
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q))) :=
  compactifiedProjectionPi d RY RZ RX cp cj a b E Q ≫
    (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).hom

/-- The reverse ordered map Rp_* theta inverse followed by rho = pi inverse. -/
def compactifiedProjectionReverse
    (hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
      ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)))
    (hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q)) :=
  (proEtaleRingDerivedDirectImage d.g RY RZ cp).map
      (compactifiedProjectionTheta d RY RZ RX cp cj b c E Q hα).inv ≫
    @inv _ _ _ _ (compactifiedProjectionPi d RY RZ RX cp cj a b E Q) hπ

set_option linter.unusedSectionVars false in
/-- The compactified perfect projection formula with its exact ordered inverse.
The local strict-perfect normalization of rho is recorded below on canonical slice
operations. No uniform bound, completion, constructibility or boundedness of E occurs. -/
theorem proEtaleProjectionFormula_compactified
    (hQ : IsProEtaleSitePerfect Y RY Q) :
    ∃ hα : IsIso (proEtaleOpenProjection d.i RZ RX cj b c E
        ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)),
    ∃ hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q),
      IsIso (compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα) ∧
      compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα ≫
        compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ = 𝟙 _ ∧
      compactifiedProjectionReverse d RY RZ RX cp cj a b c E Q hα hπ ≫
        compactifiedProjectionForward d RY RZ RX cp cj a b c E Q hα = 𝟙 _ := by
  have hα := openProjection_isIso d.i RZ RX cj b c E
    ((proEtaleRingDerivedPullback d.g RY RZ cp).obj Q)
  have hπ : IsIso (compactifiedProjectionPi d RY RZ RX cp cj a b E Q) :=
    sitePerfect_projection_isIso d.g RY RZ cp a b
      ((proEtaleRingDerivedOpenExtension d.i RZ RX cj).obj E) Q hQ
  let := hα
  let := hπ
  refine ⟨hα, hπ, ?_, ?_, ?_⟩
  · dsimp only [compactifiedProjectionForward]
    infer_instance
  · dsimp only [compactifiedProjectionForward, compactifiedProjectionReverse]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
    rw [(proEtaleRingDerivedDirectImage d.g RY RZ cp).map_id,
      Category.id_comp, IsIso.hom_inv_id]
  · dsimp only [compactifiedProjectionForward, compactifiedProjectionReverse]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc,
      ← Functor.map_comp, Iso.inv_hom_id]
    exact (proEtaleRingDerivedDirectImage d.g RY RZ cp).map_id _

end AlgebraicGeometry.Scheme
