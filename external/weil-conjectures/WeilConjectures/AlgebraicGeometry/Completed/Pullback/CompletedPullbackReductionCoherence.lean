/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import all WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientTransitionCompatibility
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
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
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement

/-! # Coherence of the projection-induced finite reduction arrows

Source: Stacks Tag 099N (5), and the completed-pullback blueprint proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.mapHomotopyCategoryFactors

private theorem adjunct_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    {Lb : C ⥤ D} {Rb : D ⥤ C} {Lq : D ⥤ E} {Rq : E ⥤ D}
    {La : C ⥤ E} {Ra : E ⥤ C}
    (ab : Lb ⊣ Rb) (aq : Lq ⊣ Rq) (aa : La ⊣ Ra)
    (e : Rq ⋙ Rb ≅ Ra) (M : C) (B : D) (A : E)
    (pb : M ⟶ Rb.obj B) (pa : M ⟶ Ra.obj A) (t : B ⟶ Rq.obj A)
    (h : pb ≫ Rb.map t ≫ e.hom.app A = pa) :
    Lq.map ((ab.homEquiv M B).symm pb) ≫ (aq.homEquiv B A).symm t =
      (Adjunction.leftAdjointCompIso ab aq aa e).hom.app M ≫
        (aa.homEquiv M A).symm pa := by
  have he : Adjunction.leftAdjointCompIso ab aq aa e =
      ((ab.comp aq).ofNatIsoRight e).leftAdjointUniq aa := by
    apply Iso.ext
    ext Z
    simp [Adjunction.leftAdjointCompIso, Adjunction.leftAdjointUniq]
  rw [he]
  apply (cancel_epi ((((ab.comp aq).ofNatIsoRight e).leftAdjointUniq aa).inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply (aa.homEquiv M A).injective
  rw [CategoryTheory.adjunctionComposition_transpose ab aq aa e M B A pb t]
  exact h.trans ((aa.homEquiv M A).apply_symm_apply pa).symm

namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

private theorem norm_eq {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : DerivedCategory (pbcModules T R)) :
    (pbcReductionNormalization φ ψ χ h M).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
        (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
        (pbcDerivedRestrictComp φ ψ χ h)).hom.app M := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem norm_natural {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {M N : DerivedCategory (pbcModules T R)} (f : M ⟶ N) :
    (pbcDerivedExtend ψ).map ((pbcDerivedExtend φ).map f) ≫
        (pbcReductionNormalization φ ψ χ h N).hom =
      (pbcReductionNormalization φ ψ χ h M).hom ≫ (pbcDerivedExtend χ).map f := by
  rw [norm_eq, norm_eq]
  exact (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
    (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
    (pbcDerivedRestrictComp φ ψ χ h)).hom.naturality f

private theorem norm_assoc {T : Scheme.{u}}
    {R S B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ D)
    (ab : R ⟶ B) (bc : S ⟶ D) (abc : R ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : a ≫ bc = abc) (hab_c : ab ≫ c = abc)
    (M : DerivedCategory (pbcModules T R)) :
    (pbcDerivedExtend c).map ((pbcReductionNormalization a b ab hab M).hom) ≫
        (pbcReductionNormalization ab c abc hab_c M).hom =
      (pbcReductionNormalization b c bc hbc ((pbcDerivedExtend a).obj M)).hom ≫
        (pbcReductionNormalization a bc abc habc M).hom := by
  let eab := pbcRestrictComp a b ab hab
  let ebc := pbcRestrictComp b c bc hbc
  let eabc := pbcRestrictComp a bc abc habc
  let eab_c := pbcRestrictComp ab c abc hab_c
  have he : Functor.isoWhiskerLeft (pbcRestrict c) eab ≪≫ eab_c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ebc (pbcRestrict a) ≪≫ eabc := by
    apply Iso.ext
    ext M U x
    change (eab_c.hom.app M).val.app U ((eab.hom.app ((pbcRestrict c).obj M)).val.app U x) =
      (eabc.hom.app M).val.app U ((ebc.hom.app M).val.app U x)
    erw [(pbcRestrictComp_exists a b ab hab).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hab_c).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists a bc abc habc).exists.choose_spec]
  have hd := SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    (pbcRestrict a) (pbcRestrict b) (pbcRestrict c)
    (pbcRestrict ab) (pbcRestrict bc) (pbcRestrict abc) eab ebc eabc eab_c he
  have hh := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc habc) (pbcDerivedRestrictComp ab c abc hab_c) hd
  have hx := congrArg (fun e ↦ e.hom.app M) hh
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hx
  simpa only [norm_eq] using hx.symm

private theorem source_assoc (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (M : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
        ((completedPullbackSourceNormalization d X b c hbc M).hom) ≫
      (completedPullbackSourceNormalization d X a b hab M).hom =
    (completedReductionQuotientAssoc d X a b c hab hbc
        ((reductionDerivedChange X (completedReductionProjection X d c)).obj M)).hom ≫
      (completedPullbackSourceNormalization d X a c (hab.trans hbc) M).hom := by
  exact norm_assoc _ _ _ _ _ _
    (completedReductionProjection_comp X d c b hbc)
    (reductionCoefficientMap_comp X d c b a hab hbc)
    (completedReductionProjection_comp X d c a (hab.trans hbc))
    (completedReductionProjection_comp X d b a hab) M

private theorem source_unit (a : ℕ)
    (M : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (completedPullbackSourceNormalization d X a a (le_refl a) M).hom =
      completedReductionUnit d X a
        ((reductionDerivedChange X (completedReductionProjection X d a)).obj M) := by
  let φ := completedReductionProjection X d a
  let ψ := reductionCoefficientMap X d a a (le_refl a)
  let h := completedReductionProjection_comp X d a a (le_refl a)
  let ρ := (completedReductionOrdinaryRestrictionUnit_exists d X a).exists.choose
  have he : pbcRestrictComp φ ψ φ h = Functor.isoWhiskerRight ρ (pbcRestrict φ) := by
    apply Iso.ext
    ext M U x
    change ((pbcRestrictComp φ ψ φ h).hom.app M).val.app U x =
      ((pbcRestrict φ).map (ρ.hom.app M)).val.app U x
    erw [(pbcRestrictComp_exists φ ψ φ h).exists.choose_spec]
    exact ((completedReductionOrdinaryRestrictionUnit_exists d X a).exists.choose_spec
      M U x).symm
  have hd : pbcDerivedRestrictComp φ ψ φ h =
      Functor.isoWhiskerRight (completedReductionRestrictionUnit d X a)
        (pbcDerivedRestrict φ) ≪≫ Functor.leftUnitor (pbcDerivedRestrict φ) := by
    unfold pbcDerivedRestrictComp
    dsimp only [pbcDerivedRestrict]
    rw [he]
    apply Iso.ext
    ext K
    have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight ρ
      (pbcRestrict φ)) K
    have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp (pbcRestrict φ)) K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hn hu
    simp only [completedReductionRestrictionUnit, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.map_comp]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (pbcRestrict ψ)
      (pbcRestrict φ)).inv.app K)).mp
    erw [Iso.inv_hom_id_app_assoc]
    simp only [← Category.assoc]
    rw [← hn]
    simp only [Category.assoc]
    simp only [NatTrans.id_app] at hu
    erw [reassoc_of% hu]
    erw [Category.id_comp, Category.comp_id]
  have hx := congrArg (fun e ↦ e.hom.app M)
    (Adjunction.leftAdjointCompIso_comp_id (pbcDerivedScalarAdjunction φ)
      (pbcDerivedScalarAdjunction ψ) _ _ hd)
  rw [show (completedPullbackSourceNormalization d X a a (le_refl a) M).hom =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
      (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction φ)
      (pbcDerivedRestrictComp φ ψ φ h)).hom.app M from norm_eq _ _ _ _ _]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hx
  rw [hx]
  simp only [Adjunction.leftAdjointIdIso_hom_app]
  erw [Category.comp_id]
  rfl

private theorem unit_natural (a : ℕ)
    {M N : DerivedCategory (pbcModules X (reductionCoefficient X d a))}
    (v : M ⟶ N) :
    (reductionDerivedChange X (reductionCoefficientMap X d a a (le_refl a))).map v ≫
        completedReductionUnit d X a N =
      completedReductionUnit d X a M ≫ v := by
  let F := reductionDerivedChange X (reductionCoefficientMap X d a a (le_refl a))
  let R := pbcDerivedRestrict (reductionCoefficientMap X d a a (le_refl a))
  let adj := pbcDerivedScalarAdjunction (reductionCoefficientMap X d a a (le_refl a))
  let ρ := completedReductionRestrictionUnit d X a
  have hn := ρ.inv.naturality v
  change v ≫ ρ.inv.app N = ρ.inv.app M ≫ R.map v at hn
  change F.map v ≫ (F.map (ρ.inv.app N) ≫ adj.counit.app N) =
    (F.map (ρ.inv.app M) ≫ adj.counit.app M) ≫ v
  rw [← Category.assoc, ← F.map_comp, hn, F.map_comp, Category.assoc]
  exact (congrArg (fun t ↦ F.map (ρ.inv.app M) ≫ t)
    (adj.counit.naturality v)).trans (Category.assoc _ _ _).symm

private theorem source_normalization_eq (a b : ℕ) (h : a ≤ b)
    (M : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (completedPullbackSourceNormalization d X a b h M).hom =
      (Adjunction.leftAdjointCompIso
        (pbcDerivedScalarAdjunction (completedReductionProjection X d b))
        (pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h))
        (pbcDerivedScalarAdjunction (completedReductionProjection X d a))
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h))).hom.app M := by
  dsimp [completedPullbackSourceNormalization, pbcReductionNormalization,
    pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

private theorem normalization_square_of_projection
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (a b : ℕ) (h : a ≤ b)
    (hp :
      (completedReductionLimitProjection d (X := X) b).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
        (completedReductionFiniteEvaluation g d b).hom.app K ≫
        (pbcDerivedRestrict (completedReductionProjection X d b)).map
          ((completedReductionTargetTransition g d a b h).app K) ≫
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteTarget g d a).obj K) =
      (completedReductionLimitProjection d (X := X) a).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
        (completedReductionFiniteEvaluation g d a).hom.app K) :
    (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
        (completedPullbackReductionArrow g d K b) ≫
          completedReductionTargetNormalization g d K a b h =
      (completedPullbackSourceNormalization d X a b h (completedPullbackObject g d K)).hom ≫
        completedPullbackReductionArrow g d K a := by
  rw [source_normalization_eq]
  exact adjunct_square
    (pbcDerivedScalarAdjunction (completedReductionProjection X d b))
    (pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h))
    (pbcDerivedScalarAdjunction (completedReductionProjection X d a))
    (pbcDerivedRestrictComp (completedReductionProjection X d b)
      (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
      (completedReductionProjection_comp X d b a h)) _ _ _ _ _ _
    (by simpa only [Category.assoc] using hp)
private theorem projection_transition (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : DerivedCategory (pbcTowers T R)) (a b : ℕ) (h : a ≤ b) :
    (completedRlimProjection T R b).app M ≫ (pbcTowerTransition T R b a h).app M =
      (completedRlimProjection T R a).app M := by
  classical
  let E := HomotopyCategory.KInjectives.equivalence (pbcTowers T R)
  obtain ⟨J, hJ, hj⟩ := HomotopyCategory.KInjectives.mk_surjective (E.inverse.obj M)
  let eM : DerivedCategory.Q.obj J ≅ M :=
    (E.functor.mapIso (eqToIso hj)).symm ≪≫ E.counitIso.app M
  have : J.IsKInjective := hJ
  have : IsIso ((completedRlimUnit T R).app
      ((HomotopyCategory.quotient _ _).obj J)) := completedRlim_computation T R J
  apply (cancel_epi ((completedRlim T R).map eM.hom)).mp
  rw [← Category.assoc, (completedRlimProjection T R b).naturality]
  rw [Category.assoc, (pbcTowerTransition T R b a h).naturality]
  rw [(completedRlimProjection T R a).naturality, ← Category.assoc]
  apply congrArg (· ≫ (pbcTowerEvaluation T R a).map eM.hom)
  apply (cancel_epi ((completedRlimUnit T R).app
    ((HomotopyCategory.quotient _ _).obj J))).mp
  rw [← Category.assoc, completedRlimProjection_unit, completedRlimProjection_unit]
  apply (cancel_mono (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
    (op a)).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [towerTransition_factors]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  with_unfolding_all
    change
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op b))
          (.up ℤ)).app J) ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).map (homOfLE h).op)
          (.up ℤ)).app J) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op a))
          (.up ℤ)).app J)
  rw [← DerivedCategory.Q.map_comp]
  apply congrArg DerivedCategory.Q.map
  ext i : 1
  exact limit.w (J.X i) (homOfLE h).op
/-- Invertible finite reduction arrows satisfy all quotient coherence equations.

Source: Stacks Tag 099N (5); completed-pullback reduction, normalization clause
(blueprint: lem-weil-pbc-completed-pullback-reduction-coherence).

Proof: strict limit projections commute with tower transitions. Combine this with
finite evaluation compatibility, then transpose the resulting square through the
scalar adjunctions. The source normalizations are the canonical composites of
left adjoints; their associativity and identity laws follow from the corresponding
laws for scalar restriction. Cancel the invertible finite arrows to obtain the
same laws for the target normalizations. -/
theorem completedPullbackReduction_coherence
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (hiso : ∀ n : ℕ, IsIso (completedPullbackReductionArrow g d K n)) :
    (∀ (a b : ℕ) (h : a ≤ b),
      IsIso (completedReductionTargetNormalization g d K a b h) ∧
      ((pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)).homEquiv _ _
          ((completedPullbackSourceNormalization d X a b h
            (completedPullbackObject g d K)).hom)) ≫
            (pbcDerivedRestrict (reductionCoefficientMap X d b a h)).map
              (completedPullbackReductionArrow g d K a) =
        completedPullbackReductionArrow g d K b ≫
          (completedReductionTargetTransition g d a b h).app K) ∧
    (∀ (a b : ℕ) (h : a ≤ b),
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h =
        (completedPullbackSourceNormalization d X a b h
          (completedPullbackObject g d K)).hom ≫
          completedPullbackReductionArrow g d K a) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (reductionDerivedChange X (reductionCoefficientMap X d b a hab)).map
          (completedReductionTargetNormalization g d K b c hbc) ≫
            completedReductionTargetNormalization g d K a b hab =
        (completedReductionQuotientAssoc d X a b c hab hbc
            ((completedReductionFiniteTarget g d c).obj K)).hom ≫
          completedReductionTargetNormalization g d K a c
            (hab.trans hbc)) ∧
    (∀ a : ℕ, completedReductionTargetNormalization g d K a a (le_refl a) =
      completedReductionUnit d X a ((completedReductionFiniteTarget g d a).obj K)) := by
  have hsquare : ∀ (a b : ℕ) (h : a ≤ b),
      (reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h =
        (completedPullbackSourceNormalization d X a b h
          (completedPullbackObject g d K)).hom ≫
            completedPullbackReductionArrow g d K a := by
    intro a b h
    apply normalization_square_of_projection g d K a b h
    have ht := finite_quotient_transition_compatibility g d K a b h
    have hp := projection_transition X (pbcAdicCompletion X d)
      ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) a b h
    have hc := congrArg (fun t ↦
      (completedReductionLimitProjection d (X := X) b).app
        ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫ t) ht
    have hp' :
        (completedReductionLimitProjection d (X := X) b).app
            ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) ≫
          (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
            ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) =
        (completedReductionLimitProjection d (X := X) a).app
          ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K)) := by
      exact hp
    exact hc.trans (by
      simpa only [Category.assoc] using
        congrArg (fun t ↦ t ≫ (completedReductionFiniteEvaluation g d a).hom.app K) hp')
  refine ⟨?_, hsquare, ?_, ?_⟩
  · intro a b h
    let adj := pbcDerivedScalarAdjunction (reductionCoefficientMap X d b a h)
    constructor
    · have := hiso a
      have := hiso b
      have : IsIso ((reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b) ≫
            completedReductionTargetNormalization g d K a b h) := by
        rw [hsquare a b h]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((reductionDerivedChange X (reductionCoefficientMap X d b a h)).map
          (completedPullbackReductionArrow g d K b)) _
    · have hs := congrArg (adj.homEquiv _ _) (hsquare a b h)
      rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right] at hs
      change _ = _ at hs
      simpa only [completedReductionTargetNormalization, adj,
        Equiv.apply_symm_apply] using hs.symm
  · intro a b c hab hbc
    have := hiso c
    let F := reductionDerivedChange X (reductionCoefficientMap X d b a hab)
    let G := reductionDerivedChange X (reductionCoefficientMap X d c b hbc)
    let H := reductionDerivedChange X (reductionCoefficientMap X d c a (hab.trans hbc))
    let v := completedPullbackReductionArrow g d K c
    apply (cancel_epi (F.map (G.map v))).mp
    rw [← Category.assoc, ← F.map_comp, hsquare b c hbc, F.map_comp,
      Category.assoc, hsquare a b hab, ← Category.assoc, source_assoc]
    rw [Category.assoc, ← hsquare a c (hab.trans hbc), ← Category.assoc]
    simpa only [Category.assoc, F, G, H, v, completedReductionQuotientAssoc] using
      congrArg (fun t ↦ t ≫ completedReductionTargetNormalization g d K a c
      (hab.trans hbc)) (norm_natural
      (reductionCoefficientMap X d c b hbc) (reductionCoefficientMap X d b a hab)
      (reductionCoefficientMap X d c a (hab.trans hbc))
      (reductionCoefficientMap_comp X d c b a hab hbc) v).symm
  · intro a
    have := hiso a
    let F := reductionDerivedChange X (reductionCoefficientMap X d a a (le_refl a))
    let v := completedPullbackReductionArrow g d K a
    apply (cancel_epi (F.map v)).mp
    rw [hsquare a a (le_refl a), source_unit]
    exact (unit_natural d a v).symm

end AlgebraicGeometry.Scheme
