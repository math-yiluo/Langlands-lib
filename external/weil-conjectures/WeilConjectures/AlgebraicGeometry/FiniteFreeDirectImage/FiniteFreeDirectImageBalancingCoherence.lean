/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
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
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Units and associators of scalar/pullback balancing

Source: Stacks Project, Tag 0D6D, lemma-derived-pullback-composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u uC vC rC wC
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

attribute [local irreducible] SheafOfModules.SuccessiveDerivedQuotient.sectionTensor
  SheafOfModules.SuccessiveDerivedQuotient.pure
  proEtaleRingModules_hasDerivedCategory proEtaleRingModuleDirectImage

-- Scalar adjunctions are determined by their normalization on resolving complexes.
open SheafOfModules.SuccessiveDerivedQuotient in
private theorem flat_ext {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {D : Type*} [Category D]
    {F G : DerivedCategory (proEtaleRingModules X R) ⥤ D} (α β : F ⟶ G)
    (h : ∀ (P : CochainComplex (proEtaleRingModules X R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) (P.X i)) →
      α.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) =
        β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ))
  intro H
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  obtain ⟨K, f, hK, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := ProEt.topology X) (R := R) P
  have hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := R) (K.X i) := fun i ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (K.X i)).symm (hf i)
  let q := HomotopyCategory.quotient (proEtaleRingModules X R) (.up ℤ)
  have : IsIso (DerivedCategory.Qh.map (q.map f)) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (proEtaleRingModules X R) (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hq)
  apply (cancel_epi (F.map (DerivedCategory.Qh.map (q.map f)))).mp
  rw [α.naturality, β.naturality, h K hK hflat]

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem scalar_hom {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ))
    (K : HomotopyCategory (proEtaleRingModules X S) (.up ℤ))
    (f : ((s.presentation a).ordinary.mapHomotopyCategory (.up ℤ)).obj H ⟶ K) :
    (s.adjunction a).homEquiv _ _
      ((s.presentation a).counit.app H ≫ DerivedCategory.Qh.map f) =
    DerivedCategory.Qh.map
      (((s.normalization.ordinaryAdjunction a).mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.inv.app K := by
  let p := s.presentation a
  obtain ⟨d, hd⟩ := SheafOfModules.sheafRingDerivedHomComparison a
    p.ordinary p.obj_eq p.map_eq (s.normalization.ordinaryAdjunction a)
    p.derived p.counit p.universal
  have he : s.adjunction a = d := by
    apply Adjunction.ext
    apply flat_ext
    intro P hP hf
    let H₀ := (HomotopyCategory.quotient _ _).obj P
    have : IsIso (p.counit.app H₀) := s.normalization.computed a P hP hf
    apply (cancel_mono ((proEtaleRingRestrictScalars a).mapDerivedCategory.map
      (p.counit.app H₀) ≫
      (proEtaleRingRestrictScalars a).mapDerivedCategoryFactorsh.hom.app
        ((p.ordinary.mapHomotopyCategory (.up ℤ)).obj H₀))).mp
    rw [s.adjunction_unit a P hP hf]
    have hn := hd H₀ ((p.ordinary.mapHomotopyCategory (.up ℤ)).obj H₀) (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at hn
    rw [Adjunction.homEquiv_unit] at hn
    rw [← Category.assoc, hn]
    simp
    rfl
  rw [he]
  exact hd H K f

open SheafOfModules.SuccessiveDerivedQuotient in
private def scalarData {X : Scheme.{u}} (s : ScalarModel X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    AdjData.{u + 1, u, u + 1, u + 2}
      (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) (s.presentation a) where
  ordinary := s.normalization.ordinaryAdjunction a
  ordinary_unit := s.normalization.ordinary_unit a
  derived := s.adjunction a
  computed := s.normalization.computed a
  unit_normalization := s.adjunction_unit a
  hom_comparison := scalar_hom s a

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem ordinary_comp {C : Type uC} [Category.{vC} C]
    [EssentiallySmall.{rC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{rC} RingCat.{rC})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{rC}] [HasSheafify J AddCommGrpCat.{rC}]
    [hD : ∀ R : Sheaf J CommRingCat.{rC}, HasDerivedCategory.{wC} (Modules R)]
    (p : ∀ {R S : Sheaf J CommRingCat.{rC}}, (a : R ⟶ S) →
      SheafOfModules.SuccessiveDerivedQuotient.Presentation a)
    (n : Normalization p)
    {R S T : Sheaf J CommRingCat.{rC}} (a : R ⟶ S) (b : S ⟶ T) :
    n.ordinary a b = ordinaryComp p (fun a ↦ n.ordinaryAdjunction a) a b := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let A := fun {R S : Sheaf J CommRingCat.{rC}} (a : R ⟶ S) ↦
    n.ordinaryAdjunction a
  let ac := ((A a).comp (A b)).ofNatIsoRight (resComp a b)
  apply (ac.homEquiv M _).injective
  change ac.homEquiv M _ ((n.ordinary a b).hom.app M) =
    ac.homEquiv M _ ((ac.leftAdjointUniq (A (a ≫ b))).hom.app M)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  simp only [ac, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change ((n.ordinary a b).hom.app M).val.app U
      (((A b).unit.app ((p a).ordinary.obj M)).val.app U
        (((A a).unit.app M).val.app U x)) =
    ((A (a ≫ b)).unit.app M).val.app U x
  dsimp only [A]
  rw [n.ordinary_unit, n.ordinary_unit,
    n.ordinary_unit]
  simpa using n.ordinary_hom a b M U x 1 1

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem scalar_comp {X : Scheme.{u}} (s : ScalarModel X)
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ T) :
    s.normalization.derived a b =
      Adjunction.leftAdjointCompIso (s.adjunction a) (s.adjunction b)
        (s.adjunction (a ≫ b)) (rightComp a b) := by
  have he := derivedComp_eq s.presentation (scalarData s) a b
  change derivedComp s.presentation (scalarData s) a b =
    Adjunction.leftAdjointCompIso (s.adjunction a) (s.adjunction b)
      (s.adjunction (a ≫ b)) (rightComp a b) at he
  rw [← he]
  apply Iso.ext
  apply flat_ext
  intro P hP hf
  have : IsIso ((s.presentation (a ≫ b)).counit.app
      ((HomotopyCategory.quotient _ _).obj P)) := s.normalization.computed (a ≫ b) P hP hf
  apply (cancel_mono ((s.presentation (a ≫ b)).counit.app
    ((HomotopyCategory.quotient _ _).obj P))).mp
  rw [s.normalization.representative a b P hP hf]
  erw [derivedComp_representative s.presentation (scalarData s) a b]
  rw [ordinary_comp s.presentation s.normalization a b]
  rfl

private def identityDerivedIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (U : C ⥤ C) [U.Additive]
    [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
    (hU : U = 𝟭 C) : U.mapDerivedCategory ≅ 𝟭 (DerivedCategory C) := by
  subst U
  exact Functor.mapDerivedCategoryIdIso C

private theorem normalized_unit {C : Type*} [Category C] [Abelian C]
    [hD : HasDerivedCategory C] (F : C ⥤ C) [F.Additive]
    (D : DerivedCategory C ⥤ DerivedCategory C)
    (c : DerivedCategory.Qh ⋙ D ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (U : C ⥤ C) [U.Additive]
    [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
    (hU : U = 𝟭 C) (A : F ⊣ U) (B : D ⊣ U.mapDerivedCategory)
    (hHom : ∀ (H K : HomotopyCategory C (.up ℤ))
      (f : (F.mapHomotopyCategory (.up ℤ)).obj H ⟶ K),
      B.homEquiv _ _ (c.app H ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((A.mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
          U.mapDerivedCategoryFactorsh.inv.app K)
    (eO : F ≅ 𝟭 C) (hOrd : ∀ M, A.unit.app M ≫ U.map (eO.hom.app M) = (eqToIso hU).inv.app M)
    (eD : D ≅ 𝟭 (DerivedCategory C))
    (heD : ∀ H : HomotopyCategory C (.up ℤ),
      eD.hom.app (DerivedCategory.Qh.obj H) = c.app H ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eO.hom (.up ℤ)).app H) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app H)) :
    eD = B.leftAdjointIdIso (identityDerivedIso U hU) := by
  subst U
  simp only [Functor.id_map, eqToIso_refl, Iso.refl_inv, NatTrans.id_app] at hOrd
  change eD = B.leftAdjointIdIso (Functor.mapDerivedCategoryIdIso C)
  have hO (H : HomotopyCategory (C) (.up ℤ)) :
      (A.mapHomotopyCategory (.up ℤ)).homEquiv
        H H ((NatTrans.mapHomotopyCategory eO.hom (.up ℤ)).app H ≫
          (Functor.mapHomotopyCategoryIdIso (C) (.up ℤ)).hom.app H) =
        𝟙 H := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    rw [Adjunction.homEquiv_unit,
      Adjunction.mapHomotopyCategory_unit_app_quotient,
      Functor.mapHomotopyCategoryIdIso_hom_app]
    simp only [NatTrans.mapHomotopyCategory_app, Functor.map_comp,
      Functor.mapHomotopyCategory_map]
    simp only [← (HomotopyCategory.quotient (C) (.up ℤ)).map_comp]
    erw [← (HomotopyCategory.quotient (C) (.up ℤ)).map_id P]
    apply congrArg (HomotopyCategory.quotient (C) (.up ℤ)).map
    ext i : 1
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.id_map]
    change A.unit.app (P.X i) ≫ eO.hom.app (P.X i) ≫ 𝟙 _ = 𝟙 _
    simpa only [Category.comp_id, Functor.id_obj] using hOrd (P.X i)
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id B).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (C) (.up ℤ))
  intro H
  have h := unit_conjugateEquiv Adjunction.id B eD.hom
    (DerivedCategory.Qh.obj H)
  simp only [Adjunction.id, NatTrans.id_app, Category.id_comp, Functor.id_obj] at h
  erw [h, ← Adjunction.homEquiv_unit, heD, ← DerivedCategory.Qh.map_comp,
    hHom, hO, DerivedCategory.Qh.map_id, Category.id_comp]
  refine Iso.inv_ext' (f := (Functor.mapDerivedCategoryIdIso
    (C)).app (DerivedCategory.Qh.obj H)) ?_
  change (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj H) ≫
    (𝟭 C).mapDerivedCategoryFactorsh.inv.app H = 𝟙 _
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  erw [Iso.hom_inv_id_app]
  rfl

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem scalar_unit {X : Scheme.{u}} (s : ScalarModel X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (eO : (s.presentation (𝟙 R)).ordinary ≅ 𝟭 (proEtaleRingModules X R))
    (heO : ∀ (M : proEtaleRingModules X R) (U : X.ProEtᵒᵖ) (r : R.obj.obj U) (x : M.val.obj U),
      (eO.hom.app M).val.app U (sectionTensor (s.presentation (𝟙 R)) M U r x) = r • x)
    (eD : (s.presentation (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (proEtaleRingModules X R)))
    (heD : ∀ H : HomotopyCategory (proEtaleRingModules X R) (.up ℤ),
      eD.hom.app (DerivedCategory.Qh.obj H) =
      (s.presentation (𝟙 R)).counit.app H ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eO.hom (.up ℤ)).app H) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryIdIso
            (proEtaleRingModules X R) (.up ℤ)).hom.app H)) :
    eD = (s.adjunction (𝟙 R)).leftAdjointIdIso
      (identityDerivedIso (proEtaleRingRestrictScalars (𝟙 R)) rfl) := by
  have hOrd (M : proEtaleRingModules X R) :
      (s.normalization.ordinaryAdjunction (𝟙 R)).unit.app M ≫
        (proEtaleRingRestrictScalars (𝟙 R)).map (eO.hom.app M) = 𝟙 M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (eO.hom.app M).val.app U
      (((s.normalization.ordinaryAdjunction (𝟙 R)).unit.app M).val.app U x) = x
    rw [s.normalization.ordinary_unit, heO]
    exact one_smul _ _
  exact normalized_unit (C := proEtaleRingModules X R)
    (hD := proEtaleRingModules_hasDerivedCategory X R)
    (s.presentation (𝟙 R)).ordinary (s.presentation (𝟙 R)).derived
    (s.presentation (𝟙 R)).counit (proEtaleRingRestrictScalars (𝟙 R)) rfl
    (s.normalization.ordinaryAdjunction (𝟙 R))
    (s.adjunction (𝟙 R)) (scalar_hom s (𝟙 R)) eO hOrd eD heD

-- Coherence of the exact restriction comparisons and the right derived units.
private def rightSquare {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S : Coefficients q} (a : CoefficientMap R S) :=
  proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm

private def ordinarySquare {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S : Coefficients q} (a : CoefficientMap R S) :=
  proEtaleRingRestrictionDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm

attribute [local semireducible] proEtaleRingModuleDirectImage in
private theorem ordinarySquare_section {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S : Coefficients q} (a : CoefficientMap R S)
    (N : proEtaleRingModules Z S.source) (U : W.ProEtᵒᵖ)
    (x : N.val.obj ((proEtaleBaseChange q).op.obj U)) :
    ((ordinarySquare a).hom.app N).val.app U x = x := by
  exact (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).1 N U x

private theorem rightSquare_fac {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S : Coefficients q} (a : CoefficientMap R S)
    (K : CochainComplex (proEtaleRingModules Z S.source) ℤ) :
    (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
        (chainDerivedUnit
          (proEtaleRingModuleDirectImage q S.target S.source S.identification) K) ≫
      (rightSquare a).hom.app (DerivedCategory.Q.obj K) ≫
      (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
        ((proEtaleRingRestrictScalars a.source).mapDerivedCategoryFactors.hom.app K) =
    (proEtaleRingRestrictScalars a.target).mapDerivedCategoryFactors.hom.app
        (((proEtaleRingModuleDirectImage
          q S.target S.source S.identification).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinarySquare a) (.up ℤ)).hom.app K) ≫
      chainDerivedUnit
        (proEtaleRingModuleDirectImage q R.target R.source R.identification)
        (((proEtaleRingRestrictScalars a.source).mapHomologicalComplex (.up ℤ)).obj K) := by
  simpa only [chainDerivedUnit, proEtaleRingDirectImageDerivedUnit, rightSquare,
    ordinarySquare, proEtaleRingRestrictionDerivedDirectImage, Category.assoc] using
    (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique q R.target S.target R.source
        S.source a.target a.source R.identification S.identification a.comm)).1 K

attribute [local semireducible] proEtaleRingModuleDirectImage in
private theorem direct_map_section {Z W : Scheme.{u}} (q : Z ⟶ W)
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R ≅ S)
    {M N : proEtaleRingModules Z S} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : ((proEtaleRingModuleDirectImage q R S c).obj M).val.obj U) :
    ((proEtaleRingModuleDirectImage q R S c).map f).val.app U x =
      f.val.app ((proEtaleBaseChange q).op.obj U) x := by
  with_unfolding_all rfl

private theorem restriction_map_section {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    {M N : proEtaleRingModules X S} (f : M ⟶ N) (U : X.ProEtᵒᵖ)
    (x : ((proEtaleRingRestrictScalars a).obj M).val.obj U) :
    ((proEtaleRingRestrictScalars a).map f).val.app U x = f.val.app U x := rfl

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem resComp_hom_section {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ T)
    (M : proEtaleRingModules X T) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((resComp a b).hom.app M).val.app U x = x := rfl

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem resComp_inv_section {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) (b : S ⟶ T)
    (M : proEtaleRingModules X T) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((resComp a b).inv.app M).val.app U x = x := rfl

open SheafOfModules.SuccessiveDerivedQuotient in
attribute [local semireducible] proEtaleRingModuleDirectImage in
private theorem ordinarySquare_comp {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S B : Coefficients q} (a : CoefficientMap R S) (b : CoefficientMap S B)
    (N : proEtaleRingModules Z B.source) :
    (resComp a.target b.target).inv.app
        ((proEtaleRingModuleDirectImage q B.target B.source B.identification).obj N) ≫
      (proEtaleRingRestrictScalars a.target).map ((ordinarySquare b).hom.app N) ≫
      (ordinarySquare a).hom.app ((proEtaleRingRestrictScalars b.source).obj N) ≫
      (proEtaleRingModuleDirectImage q R.target R.source R.identification).map
        ((resComp a.source b.source).hom.app N) =
    (ordinarySquare (a.comp b)).hom.app N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [direct_map_section q R.target R.source R.identification
    ((resComp a.source b.source).hom.app N) U]
  erw [restriction_map_section a.target ((ordinarySquare b).hom.app N) U]
  rw [resComp_hom_section, resComp_inv_section]
  erw [ordinarySquare_section a, ordinarySquare_section b,
    ordinarySquare_section (a.comp b)]

private theorem Qh_quotient_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality f
  simp only [Functor.comp_map, quotient_hom_id] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

private theorem chainUnit_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
      chainDerivedUnit F L =
    chainDerivedUnit F K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
  have h := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map f)
  dsimp only [chainDerivedUnit]
  rw [quotient_hom_id, quotient_inv_id, quotient_hom_id, quotient_inv_id]
  erw [F.rightDerivedFunctor.map_id, F.rightDerivedFunctor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
  simpa only [Functor.comp_map, Functor.mapHomotopyCategory_map, Qh_quotient_map] using h

private def exactComposition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F G ≪≫ Functor.mapDerivedCategoryNatIso e

private theorem exactComposition_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    (exactComposition e).hom.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  dsimp only [exactComposition, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F G]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private theorem exactComposition_inv_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (P : CochainComplex A ℤ) :
    (exactComposition e).inv.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).inv.app P) := by
  apply (cancel_epi ((exactComposition e).hom.app (DerivedCategory.Q.obj P))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [exactComposition_fac e P]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

private theorem rightTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₀]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₂]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    [F₀.Additive] [F₁.Additive] [F₂.Additive]
    (Ua : D₁ ⥤ D₀) (Ub : D₂ ⥤ D₁) (Uc : D₂ ⥤ D₀)
    (Va : C₁ ⥤ C₀) (Vb : C₂ ⥤ C₁) (Vc : C₂ ⥤ C₀)
    [Ua.Additive] [Ub.Additive] [Uc.Additive] [Va.Additive] [Vb.Additive] [Vc.Additive]
    [Limits.PreservesFiniteLimits Ua] [Limits.PreservesFiniteColimits Ua]
    [Limits.PreservesFiniteLimits Ub] [Limits.PreservesFiniteColimits Ub]
    [Limits.PreservesFiniteLimits Uc] [Limits.PreservesFiniteColimits Uc]
    [Limits.PreservesFiniteLimits Va] [Limits.PreservesFiniteColimits Va]
    [Limits.PreservesFiniteLimits Vb] [Limits.PreservesFiniteColimits Vb]
    [Limits.PreservesFiniteLimits Vc] [Limits.PreservesFiniteColimits Vc]
    (eu : Ub ⋙ Ua ≅ Uc) (ev : Vb ⋙ Va ≅ Vc)
    (da : F₁.rightDerivedFunctor ⋙ Ua.mapDerivedCategory ≅
      Va.mapDerivedCategory ⋙ F₀.rightDerivedFunctor)
    (db : F₂.rightDerivedFunctor ⋙ Ub.mapDerivedCategory ≅
      Vb.mapDerivedCategory ⋙ F₁.rightDerivedFunctor)
    (dc : F₂.rightDerivedFunctor ⋙ Uc.mapDerivedCategory ≅
      Vc.mapDerivedCategory ⋙ F₀.rightDerivedFunctor)
    (oa : F₁ ⋙ Ua ≅ Va ⋙ F₀) (ob : F₂ ⋙ Ub ≅ Vb ⋙ F₁)
    (oc : F₂ ⋙ Uc ≅ Vc ⋙ F₀)
    (ha : ∀ P : CochainComplex C₁ ℤ,
      Ua.mapDerivedCategory.map (chainDerivedUnit F₁ P) ≫
          da.hom.app (DerivedCategory.Q.obj P) ≫
          F₀.rightDerivedFunctor.map (Va.mapDerivedCategoryFactors.hom.app P) =
        Ua.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oa (.up ℤ)).hom.app P) ≫
          chainDerivedUnit F₀ ((Va.mapHomologicalComplex (.up ℤ)).obj P))
    (hb : ∀ P : CochainComplex C₂ ℤ,
      Ub.mapDerivedCategory.map (chainDerivedUnit F₂ P) ≫
          db.hom.app (DerivedCategory.Q.obj P) ≫
          F₁.rightDerivedFunctor.map (Vb.mapDerivedCategoryFactors.hom.app P) =
        Ub.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ob (.up ℤ)).hom.app P) ≫
          chainDerivedUnit F₁ ((Vb.mapHomologicalComplex (.up ℤ)).obj P))
    (hc : ∀ P : CochainComplex C₂ ℤ,
      Uc.mapDerivedCategory.map (chainDerivedUnit F₂ P) ≫
          dc.hom.app (DerivedCategory.Q.obj P) ≫
          F₀.rightDerivedFunctor.map (Vc.mapDerivedCategoryFactors.hom.app P) =
        Uc.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oc (.up ℤ)).hom.app P) ≫
          chainDerivedUnit F₀ ((Vc.mapHomologicalComplex (.up ℤ)).obj P))
    (ho : ∀ N : C₂, eu.inv.app (F₂.obj N) ≫ Ua.map (ob.hom.app N) ≫
      oa.hom.app (Vb.obj N) ≫ F₀.map (ev.hom.app N) = oc.hom.app N) :
    dc = isoWhiskerLeft F₂.rightDerivedFunctor (exactComposition eu).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight db Ua.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft Vb.mapDerivedCategory da ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (exactComposition ev) F₀.rightDerivedFunctor := by
  apply Iso.ext
  apply derived_comp_ext F₂ Uc (Vc.mapDerivedCategory ⋙ F₀.rightDerivedFunctor)
  intro P
  apply (cancel_mono (F₀.rightDerivedFunctor.map
    (Vc.mapDerivedCategoryFactors.hom.app P))).mp
  simp only [Category.assoc]
  erw [hc P]
  symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [(exactComposition eu).inv.naturality_assoc (chainDerivedUnit F₂ P)]
  rw [← F₀.rightDerivedFunctor.map_comp, exactComposition_fac ev P]
  simp only [F₀.rightDerivedFunctor.map_comp, Category.assoc]
  erw [← da.hom.naturality_assoc (Vb.mapDerivedCategoryFactors.hom.app P)]
  simp only [Functor.comp_map]
  rw [← Ua.mapDerivedCategory.map_comp_assoc, ← Ua.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hb P]
  simp only [Ua.mapDerivedCategory.map_comp, Category.assoc]
  erw [reassoc_of% (ha ((Vb.mapHomologicalComplex (.up ℤ)).obj P))]
  erw [Ua.mapDerivedCategoryFactors.hom.naturality_assoc
    ((NatIso.mapHomologicalComplex ob (.up ℤ)).hom.app P)]
  erw [reassoc_of% (exactComposition_inv_fac eu
    ((F₂.mapHomologicalComplex (.up ℤ)).obj P))]
  erw [← chainUnit_naturality F₀
    ((NatIso.mapHomologicalComplex ev (.up ℤ)).hom.app P)]
  have hco :
      (NatIso.mapHomologicalComplex eu (.up ℤ)).inv.app
          ((F₂.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Ua.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex ob (.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex oa (.up ℤ)).hom.app
          ((Vb.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (F₀.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex ev (.up ℤ)).hom.app P) =
      (NatIso.mapHomologicalComplex oc (.up ℤ)).hom.app P := by
    ext i : 1
    exact ho (P.X i)
  simp only [Functor.comp_map, Category.assoc, ← DerivedCategory.Q.map_comp_assoc]
  erw [hco]

open SheafOfModules.SuccessiveDerivedQuotient in
private theorem rightSquare_comp {Z W : Scheme.{u}} {q : Z ⟶ W}
    {R S B : Coefficients q} (a : CoefficientMap R S) (b : CoefficientMap S B)
    (K : DerivedCategory (proEtaleRingModules Z B.source)) :
    (rightSquare (a.comp b)).hom.app K =
    (rightComp a.target b.target).inv.app
        ((proEtaleRingDerivedDirectImage q B.target B.source B.identification).obj K) ≫
      (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
        ((rightSquare b).hom.app K) ≫
      (rightSquare a).hom.app ((proEtaleRingRestrictScalars b.source).mapDerivedCategory.obj K) ≫
      (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
        ((rightComp a.source b.source).hom.app K) := by
  have h := rightTower
    (proEtaleRingModuleDirectImage q R.target R.source R.identification)
    (proEtaleRingModuleDirectImage q S.target S.source S.identification)
    (proEtaleRingModuleDirectImage q B.target B.source B.identification)
    (proEtaleRingRestrictScalars a.target) (proEtaleRingRestrictScalars b.target)
    (proEtaleRingRestrictScalars (a.target ≫ b.target))
    (proEtaleRingRestrictScalars a.source) (proEtaleRingRestrictScalars b.source)
    (proEtaleRingRestrictScalars (a.source ≫ b.source))
    (resComp a.target b.target) (resComp a.source b.source)
    (rightSquare a) (rightSquare b) (rightSquare (a.comp b))
    (ordinarySquare a) (ordinarySquare b) (ordinarySquare (a.comp b))
    (rightSquare_fac a) (rightSquare_fac b) (rightSquare_fac (a.comp b))
    (ordinarySquare_comp a b)
  have hh := NatTrans.congr_app (congrArg Iso.hom h) K
  simpa only [exactComposition, rightComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using hh

private theorem identity_fac {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  simp only [quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id] at h
  erw [(𝟭 C).mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at h
  exact h

attribute [local semireducible] proEtaleRingModuleDirectImage in
private theorem ordinarySquare_id {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R : Coefficients q) (N : proEtaleRingModules Z R.source) :
    (ordinarySquare (CoefficientMap.id R)).hom.app N = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact ordinarySquare_section (CoefficientMap.id R) N U x

private def ordinaryIdentityIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : D ⥤ D) (V : C ⥤ C) (hU : U = 𝟭 D) (hV : V = 𝟭 C) :
    F ⋙ U ≅ V ⋙ F := by
  subst U
  subst V
  exact Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm

private theorem ordinaryIdentityIso_hom_app
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (U : D ⥤ D) (V : C ⥤ C) (hU : U = 𝟭 D) (hV : V = 𝟭 C) (N : C) :
    (ordinaryIdentityIso F U V hU hV).hom.app N =
      (eqToIso hU).hom.app (F.obj N) ≫ F.map ((eqToIso hV).inv.app N) := by
  subst U
  subst V
  simp only [ordinaryIdentityIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.id_obj,
    CategoryTheory.Functor.map_id]

private theorem rightIdentity
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (U : D ⥤ D) (V : C ⥤ C)
    [U.Additive] [V.Additive]
    [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
    [Limits.PreservesFiniteLimits V] [Limits.PreservesFiniteColimits V]
    (hU : U = 𝟭 D) (hV : V = 𝟭 C)
    (d : F.rightDerivedFunctor ⋙ U.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ F.rightDerivedFunctor)
    (o : F ⋙ U ≅ V ⋙ F)
    (ho : o = ordinaryIdentityIso F U V hU hV)
    (hd : ∀ P : CochainComplex C ℤ,
      U.mapDerivedCategory.map (chainDerivedUnit F P) ≫
        d.hom.app (DerivedCategory.Q.obj P) ≫
        F.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.hom.app P) =
      U.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) ≫
        chainDerivedUnit F ((V.mapHomologicalComplex (.up ℤ)).obj P)) :
    d = isoWhiskerLeft F.rightDerivedFunctor (identityDerivedIso U hU) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      isoWhiskerRight (identityDerivedIso V hV).symm F.rightDerivedFunctor := by
  subst U
  subst V
  change d = isoWhiskerLeft F.rightDerivedFunctor (Functor.mapDerivedCategoryIdIso D) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (Functor.mapDerivedCategoryIdIso C).symm F.rightDerivedFunctor
  apply Iso.ext
  apply derived_comp_ext F (𝟭 D) ((𝟭 C).mapDerivedCategory ⋙ F.rightDerivedFunctor)
  intro P
  apply (cancel_mono (F.rightDerivedFunctor.map
    ((𝟭 C).mapDerivedCategoryFactors.hom.app P))).mp
  simp only [Category.assoc]
  erw [hd P]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  erw [(Functor.mapDerivedCategoryIdIso D).hom.naturality_assoc (chainDerivedUnit F P)]
  rw [← F.rightDerivedFunctor.map_comp]
  erw [← identity_fac P, Iso.inv_hom_id_app, F.rightDerivedFunctor.map_id,
    Category.comp_id, identity_fac]
  have hco : (NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P = 𝟙 _ := by
    ext i : 1
    rw [ho]
    change 𝟙 (F.obj (P.X i)) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  erw [hco, DerivedCategory.Q.map_id, Category.id_comp]
  simp only [Functor.id_map, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Category.comp_id]
  erw [Category.comp_id]
  all_goals rfl

private theorem rightSquare_id {Z W : Scheme.{u}} {q : Z ⟶ W} (R : Coefficients q) :
    rightSquare (CoefficientMap.id R) =
    isoWhiskerLeft (proEtaleRingDerivedDirectImage q R.target R.source R.identification)
      (identityDerivedIso (proEtaleRingRestrictScalars (𝟙 R.target)) rfl) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (identityDerivedIso
      (proEtaleRingRestrictScalars (𝟙 R.source)) rfl).symm
      (proEtaleRingDerivedDirectImage q R.target R.source R.identification) := by
  have ho : ordinarySquare (CoefficientMap.id R) =
      ordinaryIdentityIso
        (proEtaleRingModuleDirectImage q R.target R.source R.identification)
        (proEtaleRingRestrictScalars (𝟙 R.target))
        (proEtaleRingRestrictScalars (𝟙 R.source)) rfl rfl := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    rw [ordinaryIdentityIso_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact ordinarySquare_id R N
  exact rightIdentity
    (proEtaleRingModuleDirectImage q R.target R.source R.identification)
    (proEtaleRingRestrictScalars (𝟙 R.target))
    (proEtaleRingRestrictScalars (𝟙 R.source)) rfl rfl
    (rightSquare (CoefficientMap.id R)) (ordinarySquare (CoefficientMap.id R))
    ho (rightSquare_fac (CoefficientMap.id R))

-- The required two equations are transported through conjugation of adjunctions.
namespace Conjugation

private def square {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A} {I : C ⥤ D} {X : D ⥤ C}
    (af : F ⊣ U) (ag : G ⊣ V) (ah : H ⊣ W) (ai : I ⊣ X)
    (d : V ⋙ U ≅ X ⋙ W) : F ⋙ G ≅ H ⋙ I :=
  ((conjugateIsoEquiv (af.comp ag) (ah.comp ai)).symm d).symm

private theorem square_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ D} {V : D ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A} {I : C ⥤ D} {X : D ⥤ C}
    (af : F ⊣ U) (ag : G ⊣ V) (ah : H ⊣ W) (ai : I ⊣ X)
    (d : V ⋙ U ≅ X ⋙ W) :
    conjugateIsoEquiv (ah.comp ai) (af.comp ag) (square af ag ah ai d) = d.symm := by
  rw [square, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]

private theorem unit
    {A B : Type*} [Category A] [Category B]
    {E : A ⥤ A} {U : A ⥤ A} {F : B ⥤ B} {V : B ⥤ B}
    {L : A ⥤ B} {G : B ⥤ A}
    (a : E ⊣ U) (b : F ⊣ V) (g : L ⊣ G)
    (ew : U ≅ 𝟭 A) (ez : V ≅ 𝟭 B) (d : G ⋙ U ≅ V ⋙ G)
    (hd : d = isoWhiskerLeft G ew ≪≫ rightUnitor G ≪≫
      (leftUnitor G).symm ≪≫ isoWhiskerRight ez.symm G) :
    isoWhiskerRight (a.leftAdjointIdIso ew).symm L ≪≫
      square a g g b d ≪≫ isoWhiskerLeft L (b.leftAdjointIdIso ez) =
      leftUnitor L ≪≫ (rightUnitor L).symm := by
  apply (conjugateIsoEquiv (g.comp Adjunction.id) (Adjunction.id.comp g)).injective
  rw [conjugateIsoEquiv_trans (g.comp Adjunction.id) (a.comp g) (Adjunction.id.comp g),
    conjugateIsoEquiv_trans (g.comp Adjunction.id) (g.comp b) (a.comp g),
    conjugateIsoEquiv_trans (g.comp Adjunction.id) g (Adjunction.id.comp g)]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_iso_symm, square_conjugate, Adjunction.leftAdjointIdIso,
    Equiv.apply_symm_apply, conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_rightUnitor]
  rw [hd]
  apply Iso.ext
  ext K
  simp

private theorem tower_private
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category B₀] [Category B₁] [Category B₂]
    {F₀₁ : A₀ ⥤ A₁} {F₁₂ : A₁ ⥤ A₂} {F₀₂ : A₀ ⥤ A₂}
    {U₁₀ : A₁ ⥤ A₀} {U₂₁ : A₂ ⥤ A₁} {U₂₀ : A₂ ⥤ A₀}
    {H₀₁ : B₀ ⥤ B₁} {H₁₂ : B₁ ⥤ B₂} {H₀₂ : B₀ ⥤ B₂}
    {V₁₀ : B₁ ⥤ B₀} {V₂₁ : B₂ ⥤ B₁} {V₂₀ : B₂ ⥤ B₀}
    {L₀ : A₀ ⥤ B₀} {L₁ : A₁ ⥤ B₁} {L₂ : A₂ ⥤ B₂}
    {G₀ : B₀ ⥤ A₀} {G₁ : B₁ ⥤ A₁} {G₂ : B₂ ⥤ A₂}
    (a₀₁ : F₀₁ ⊣ U₁₀) (a₁₂ : F₁₂ ⊣ U₂₁) (a₀₂ : F₀₂ ⊣ U₂₀)
    (b₀₁ : H₀₁ ⊣ V₁₀) (b₁₂ : H₁₂ ⊣ V₂₁) (b₀₂ : H₀₂ ⊣ V₂₀)
    (g₀ : L₀ ⊣ G₀) (g₁ : L₁ ⊣ G₁) (g₂ : L₂ ⊣ G₂)
    (ew : U₂₁ ⋙ U₁₀ ≅ U₂₀) (ez : V₂₁ ⋙ V₁₀ ≅ V₂₀)
    (da : G₁ ⋙ U₁₀ ≅ V₁₀ ⋙ G₀) (db : G₂ ⋙ U₂₁ ≅ V₂₁ ⋙ G₁)
    (dc : G₂ ⋙ U₂₀ ≅ V₂₀ ⋙ G₀)
    (hc : dc = isoWhiskerLeft G₂ ew.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight db U₁₀ ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft V₂₁ da ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ez G₀) :
    square a₀₂ g₂ g₀ b₀₂ dc =
    isoWhiskerRight (a₀₁.leftAdjointCompIso a₁₂ a₀₂ ew).symm L₂ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F₀₁ (square a₁₂ g₂ g₁ b₁₂ db) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (square a₀₁ g₁ g₀ b₀₁ da) H₁₂ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft L₀ (b₀₁.leftAdjointCompIso b₁₂ b₀₂ ez) := by
  apply (conjugateIsoEquiv (g₀.comp b₀₂) (a₀₂.comp g₂)).injective
  rw [square_conjugate,
    conjugateIsoEquiv_trans (g₀.comp b₀₂) ((a₀₁.comp a₁₂).comp g₂) (a₀₂.comp g₂),
    conjugateIsoEquiv_trans (g₀.comp b₀₂) (a₀₁.comp (a₁₂.comp g₂))
      ((a₀₁.comp a₁₂).comp g₂),
    conjugateIsoEquiv_trans (g₀.comp b₀₂) (a₀₁.comp (g₁.comp b₁₂))
      (a₀₁.comp (a₁₂.comp g₂)),
    conjugateIsoEquiv_trans (g₀.comp b₀₂) ((a₀₁.comp g₁).comp b₁₂)
      (a₀₁.comp (g₁.comp b₁₂)),
    conjugateIsoEquiv_trans (g₀.comp b₀₂) ((g₀.comp b₀₁).comp b₁₂)
      ((a₀₁.comp g₁).comp b₁₂),
    conjugateIsoEquiv_trans (g₀.comp b₀₂) (g₀.comp (b₀₁.comp b₁₂))
      ((g₀.comp b₀₁).comp b₁₂)]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator, square_conjugate,
    Adjunction.leftAdjointCompIso, Equiv.apply_symm_apply]
  rw [hc]
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

/-- Public export of the private `tower_private`
(used by `import all` importers; linter.privateModule). -/
alias tower := tower_private

end Conjugation

/-- Balancing respects scalar multiplication units and balanced tensor associators.
Source: Stacks Project, Tag 0D6D, lemma-derived-pullback-composition;
finite-free direct-image proof, Step 3.
(blueprint: lem-sp-finite-free-balancing-coherence).

Proof: flat-term K-flat resolutions and the derived Hom comparison identify the
specified scalar adjunctions with the universal scalar-extension adjunctions. The
ordinary pure-tensor formulas identify multiplication and composition with the
canonical left-adjoint unit and composition isomorphisms; the representative
normalizations give the same identifications after localization. On the right,
restriction/direct-image comparisons are identity maps on sections. Their unit and
tower equations lift uniquely using the specified derived-unit normalization.
Finally conjugation preserves composition, whiskering, unitors and associators.
Applying these identities to the normalized right comparisons proves the two
assertions. No finite-basis choice or finite-free assumption is required. -/
theorem finiteFreeDirectImageBalancingCoherence {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z) :
    (∀ (R : Coefficients q) (K : DerivedCategory (proEtaleRingModules W R.target)),
      (proEtaleRingDerivedPullback q R.target R.source R.identification).map
          ((sW.unit R.target).inv.app K) ≫
        (balancing sW sZ (CoefficientMap.id R)).hom.app K ≫
        (sZ.unit R.source).hom.app
          ((proEtaleRingDerivedPullback q R.target R.source R.identification).obj K) = 𝟙 _) ∧
    (∀ (R S B : Coefficients q) (a : CoefficientMap R S) (b : CoefficientMap S B)
      (K : DerivedCategory (proEtaleRingModules W R.target)),
      (balancing sW sZ (a.comp b)).hom.app K =
        (proEtaleRingDerivedPullback q B.target B.source B.identification).map
          ((sW.normalization.derived a.target b.target).inv.app K) ≫
        (balancing sW sZ b).hom.app ((sW.presentation a.target).derived.obj K) ≫
        (sZ.presentation b.source).derived.map ((balancing sW sZ a).hom.app K) ≫
        (sZ.normalization.derived a.source b.source).hom.app
          ((proEtaleRingDerivedPullback q R.target R.source R.identification).obj K)) := by
  constructor
  · intro R K
    have hw := scalar_unit sW R.target (sW.ordinaryUnit R.target)
      (sW.ordinaryUnit_pure R.target) (sW.unit R.target) (sW.unit_normalization R.target)
    have hz := scalar_unit sZ R.source (sZ.ordinaryUnit R.source)
      (sZ.ordinaryUnit_pure R.source) (sZ.unit R.source) (sZ.unit_normalization R.source)
    have h := Conjugation.unit (sW.adjunction (𝟙 R.target))
      (sZ.adjunction (𝟙 R.source))
      (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
      (identityDerivedIso (proEtaleRingRestrictScalars (𝟙 R.target)) rfl)
      (identityDerivedIso (proEtaleRingRestrictScalars (𝟙 R.source)) rfl)
      (rightSquare (CoefficientMap.id R)) (rightSquare_id R)
    rw [← hw, ← hz] at h
    have hc := NatTrans.congr_app (congrArg Iso.hom h) K
    simpa only [CoefficientMap.id, Functor.id_obj, Conjugation.square, balancing,
      rightSquare, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Category.id_comp, Category.comp_id] using hc
  · intro R S B a b K
    let ew := SheafOfModules.SuccessiveDerivedQuotient.rightComp a.target b.target
    let ez := SheafOfModules.SuccessiveDerivedQuotient.rightComp a.source b.source
    have hc : rightSquare (a.comp b) =
        isoWhiskerLeft
          (proEtaleRingDerivedDirectImage q B.target B.source B.identification) ew.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (rightSquare b)
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft (proEtaleRingRestrictScalars b.source).mapDerivedCategory
          (rightSquare a) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight ez
          (proEtaleRingDerivedDirectImage q R.target R.source R.identification) := by
      apply Iso.ext
      ext M
      simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
        isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id] using rightSquare_comp a b M
    have h := Conjugation.tower_private
      (sW.adjunction a.target) (sW.adjunction b.target) (sW.adjunction (a.comp b).target)
      (sZ.adjunction a.source) (sZ.adjunction b.source) (sZ.adjunction (a.comp b).source)
      (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
      (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
      (proEtaleRingDerivedAdjunction q B.target B.source B.identification)
      ew ez (rightSquare a) (rightSquare b) (rightSquare (a.comp b)) hc
    dsimp only [ew, ez, CoefficientMap.comp] at h
    erw [← scalar_comp sW a.target b.target, ← scalar_comp sZ a.source b.source] at h
    have hh := NatTrans.congr_app (congrArg Iso.hom h) K
    simpa only [CoefficientMap.comp, Functor.id_obj, Conjugation.square, balancing,
      rightSquare, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id] using hh

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
