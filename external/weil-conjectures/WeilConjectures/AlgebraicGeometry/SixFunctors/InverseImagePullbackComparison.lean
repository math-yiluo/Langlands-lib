/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import all WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-!
# Inverse image to finite and completed derived pullback

Inverse image is expressed in its canonical sectionwise model for an isomorphism.
All coefficient sheaves, finite reductions, pullbacks, transitions, and the Roos
complex are the recorded constructions. A map chosen below has a unique prescribed
value on every section; no arbitrary comparison or cone is supplied as data.
The index n denotes positive exponent n+1. The integral definition takes precisely
the good representative and resolution used to evaluate the recorded completed pullback.

## Main definitions

- `inverseImageCompletedCoefficientMap`: limit lift of the actual finite structure maps.
- `inverseImageFiniteDerived`, `inverseImageIntegralDerived`: exact module inverse images.
- `inverseImagePullbackComparisonFinite`: the sheafified finite tensor-unit map.
- `inverseImagePullbackComparisonFiniteIntrinsic`: its recorded intrinsic presentation.
- `inverseImageRoosComparisonComplex`: the compatible reductions with zero homotopy.
- `inverseImagePullbackComparison`: the integral map for the chosen resolution.

## References

* Bhatt--Scholze, Section 6.5
* Stacks Tags 03D2 and 00YV
* Stacks Tags 03CO and 0H7J
* Stacks Tags 09A5, 00WX and 03CO
* Stacks Tag 05RU
* Stacks Tag 04JC
* Stacks Tags 03D6 and 08TC
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The coefficient-sized pullback is the recorded intrinsic finite pullback,
with the canonical unit-preserving identification of left adjoints. This comparison
uses the same constant-section direct image on both sides. -/
def inverseImageFiniteIntrinsicPullbackComparison {S T : Scheme.{t}} (f : S ⟶ T)
    (A : Type t) [CommRing A] [Finite A] :
    coefficientProEtaleModulePullback.{t, t} f (CommRingCat.of (ULift.{t + 1, t} A)) ≅
      sfIntrinsicPullback A f :=
  (coefficientProEtaleModuleAdjunction.{t, t} f
    (CommRingCat.of (ULift.{t + 1, t} A))).leftAdjointUniq
      (sfIntrinsicConstantModuleAdjunction f A)

/-- The finite constant coefficient structure map, in the sectionwise inverse-image model. -/
abbrev inverseImageFiniteCoefficientMap (n : ℕ) :=
  isoSectionwiseConstantMap g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The prescribed components of the completed structure map are inverse images of
limit projections followed by the constant-section comparison. -/
def inverseImageCompletedCoefficientComponent (n : ℕ) :=
  (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
      (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
    inverseImageFiniteCoefficientMap l E g n

attribute [local irreducible] HasDerivedCategory.standard

private theorem constantMap_eq (A : CommRingCat.{max u (t + 1)}) :
    isoSectionwiseConstantMap g A =
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (sectionwiseConstantCommIso g A).hom := by
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
  · intro U a
    have hn := sectionwiseConstantCommIso_normalization g A
    exact congrArg (fun f ↦ (f.app (op U)) a) hn

private theorem constantMap_naturality {A B : CommRingCat.{max u (t + 1)}}
    (f : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f)) ≫
      isoSectionwiseConstantMap g B =
    isoSectionwiseConstantMap g A ≫
      (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map f) := by
  have := sectionwisePostcompose_cocontinuous g
  rw [constantMap_eq, constantMap_eq]
  let e := ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Y)).symm
  have h := e.hom.naturality ((Functor.const Y.ProEtᵒᵖ).map f)
  exact congrArg ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map) h

private def coefficientDiagramMap :
    integralCoefficientSheafSystem l E Y ⋙ isoSectionwiseInverseImage g RingCat ⟶
      integralCoefficientSheafSystem l E X :=
  NatTrans.ofOpSequence (fun n ↦ inverseImageFiniteCoefficientMap l E g n) (fun n ↦ by
    simpa only [Functor.comp_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ, integralCoefficientSheafTransition,
      inverseImageFiniteCoefficientMap] using
      constantMap_naturality g (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))

/-- The prescribed components commute with every coefficient reduction. -/
theorem inverseImageCompletedCoefficientComponent_naturality {a b : ℕᵒᵖ} (f : a ⟶ b) :
    inverseImageCompletedCoefficientComponent l E g a.unop ≫
        (integralCoefficientSheafSystem l E X).map f =
      inverseImageCompletedCoefficientComponent l E g b.unop := by
  unfold inverseImageCompletedCoefficientComponent
  change (isoSectionwiseInverseImage g RingCat).map
      (limit.π (integralCoefficientSheafSystem l E Y) a) ≫
        (coefficientDiagramMap l E g).app a ≫ (integralCoefficientSheafSystem l E X).map f =
    (isoSectionwiseInverseImage g RingCat).map
      (limit.π (integralCoefficientSheafSystem l E Y) b) ≫
        (coefficientDiagramMap l E g).app b
  rw [← (coefficientDiagramMap l E g).naturality f, ← Category.assoc,
    Functor.comp_map, ← Functor.map_comp, limit.w]

/-- The completed structure map is the actual limit lift of its finite components. -/
def inverseImageCompletedCoefficientMap :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
        completedIntegralCoefficientSheafUnrestricted l E X :=
  limit.lift (integralCoefficientSheafSystem l E X)
    { pt := (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y)
      π := { app n := inverseImageCompletedCoefficientComponent l E g n.unop
             naturality _ _ f := (Category.id_comp _).trans
               (inverseImageCompletedCoefficientComponent_naturality l E g f).symm } }

/-- The completed coefficient map is an isomorphism, without a completeness
hypothesis on any module. -/
@[instance] theorem inverseImageCompletedCoefficientMap_isIso :
    IsIso (inverseImageCompletedCoefficientMap l E g) := by
  let F := isoSectionwiseInverseImage g RingCat.{max u (t + 1)}
  have : PreservesLimitsOfSize.{0, 0} F :=
    (isoSectionwiseInverseImage_equivalence g RingCat.{max u (t + 1)}).2.1
  let α := coefficientDiagramMap l E g
  have : ∀ n, IsIso (α.app n) := fun n ↦
    isoSectionwiseConstantMap_isIso g _
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e := preservesLimitIso F (integralCoefficientSheafSystem l E Y) ≪≫
    HasLimit.isoOfNatIso (asIso α)
  have he : inverseImageCompletedCoefficientMap l E g = e.hom := by
    apply limit.hom_ext
    intro n
    simp only [inverseImageCompletedCoefficientMap, limit.lift_π, e, Iso.trans_hom,
      Category.assoc, HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc]
    rfl
  rw [he]
  infer_instance

/-- Finite inverse image, with action a acting through c_A inverse(a). -/
abbrev inverseImageFiniteModules (n : ℕ) :
    integralOperationsFiniteModules l E Y n ⥤ integralOperationsFiniteModules l E X n :=
  isoSectionwiseModuleInverseImage g (inverseImageFiniteCoefficientMap l E g n)

/-- Completed-coefficient inverse image, with the action transported through the
inverse of the constructed limit coefficient map. -/
abbrev inverseImageIntegralModules : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  isoSectionwiseModuleInverseImage g (inverseImageCompletedCoefficientMap l E g)

/-- Exact inverse image descends termwise to the unbounded finite derived category. -/
abbrev inverseImageFiniteDerived (n : ℕ) :=
  (inverseImageFiniteModules l E g n).mapDerivedCategory

/-- Exact inverse image descends termwise to the entire completed-coefficient derived
category; no derived-completeness or constructibility condition is imposed. -/
abbrev inverseImageIntegralDerived := (inverseImageIntegralModules l E g).mapDerivedCategory

/-- The finite pullback is exact in the canonical coefficient-sized presentation. -/
theorem inverseImageFinitePullback_exact (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E g n) ∧
      PreservesFiniteColimits (integralOperationsLevelPullback l E g n) := by
  exact coefficientProEtaleModulePullback_exact (asIso g).hom
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- Left exactness of the recorded finite tensor pullback. -/
instance inverseImageFinitePullback_limits (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
  (inverseImageFinitePullback_exact l E g n).1

/-- Right exactness of the recorded finite tensor pullback. -/
instance inverseImageFinitePullback_colimits (n : ℕ) :
    PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
  (inverseImageFinitePullback_exact l E g n).2

private abbrev constantRing (W : Scheme.{t}) (A : CommRingCat.{max u (t + 1)}) :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj A)

private def isoSiteAdjunction :=
  MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial

private def constantRingViaUnit (A : CommRingCat.{max u (t + 1)}) :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj (constantRing Y A) ⟶
      constantRing X A :=
  ⟨(proEtaleIsoPostcompose g).op.whiskerLeft
      (Functor.whiskerRight (coefficientProEtaleDirectRingMap g A).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})) ≫
    Functor.whiskerRight (NatTrans.op (isoSiteAdjunction g).unit) (constantRing X A).obj⟩

private theorem constantRingViaUnit_eq (A : CommRingCat.{max u (t + 1)}) :
    constantRingViaUnit g A = isoSectionwiseConstantMap g A := by
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · intro U a
    have h := Equiv.apply_symm_apply ((sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)))
      (Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
    rw [Adjunction.homEquiv_unit] at h
    have hx := congrArg (fun k ↦ k.app (op ((proEtaleIsoPostcompose g).obj U)) a) h
    change ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A).obj.map
        (proEtaleIsoCommaArrow g U).op
        ((coefficientProEtaleDirectRingMap g A).hom.app _
          ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app _ a)) = _
    rw [show (coefficientProEtaleDirectRingMap g A).hom.app _
        ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app _ a) =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app _ a from hx]
    exact (congrArg (fun k ↦ k a)
      ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
        (proEtaleIsoCommaArrow g U).op)).symm
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec

private def finiteEvaluation (n : ℕ) :
    coefficientProEtaleModuleDirectImage g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ⋙
      inverseImageFiniteModules l E g n ⟶ 𝟭 _ := by
  let A := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let φ := inv (inverseImageFiniteCoefficientMap l E g n)
  let ψ : constantRing Y A ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).obj (constantRing X A) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap g A).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  letI := Functor.isContinuous_comp (proEtaleIsoPostcompose g) (proEtaleBaseChange g)
    (ProEt.topology X) (ProEt.topology Y) (ProEt.topology X)
  letI : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g) ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).IsContinuous
      (ProEt.topology X) (ProEt.topology X) :=
    inferInstanceAs ((proEtaleIsoPostcompose g ⋙ proEtaleBaseChange g).IsContinuous
      (ProEt.topology X) (ProEt.topology X))
  letI : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ X)).IsContinuous
      (ProEt.topology X) (ProEt.topology X) := Functor.isContinuous_id (ProEt.topology X)
  have h : (φ ≫ (isoSectionwiseInverseImage g RingCat).map ψ) ≫
      (Functor.sheafPushforwardContinuousNatTrans (isoSiteAdjunction g).unit
        RingCat (ProEt.topology X) (ProEt.topology X)).app (constantRing X A) =
      𝟙 (constantRing X A) := by
    rw [Category.assoc]
    change φ ≫ constantRingViaUnit g A = 𝟙 _
    rw [constantRingViaUnit_eq]
    exact IsIso.inv_hom_id _
  exact (SheafOfModules.pushforwardComp φ ψ).hom ≫
    SheafOfModules.pushforwardNatTrans _ (isoSiteAdjunction g).unit ≫
      (SheafOfModules.pushforwardCongr h).hom ≫ (SheafOfModules.pushforwardId _).hom

private def finiteModuleComparison (n : ℕ) :
    inverseImageFiniteModules l E g n ⟶ integralOperationsLevelPullback l E g n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (coefficientProEtaleModuleAdjunction g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit
      (inverseImageFiniteModules l E g n) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (integralOperationsLevelPullback l E g n) (finiteEvaluation l E g n) ≫
      (Functor.rightUnitor _).hom

/-- The finite comparison is uniquely specified on every inverse-image section.
The adjunction unit is the sheafified generator x tensor 1; restriction along the
canonical comma arrow evaluates that generator at U. -/
theorem inverseImageFiniteComparison_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    ∃! f : ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)).obj K ⟶
        ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).obj K,
      ∀ (i : ℤ) (U : X.ProEt)
        (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (f.f i).val.app (op U) x =
          (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.map
            (proEtaleIsoCommaArrow g U).op)
            (integralOperationsPullbackGenerator l E g n (K.X i)
              ((proEtaleIsoPostcompose g).obj U) x) := by
  let := integralOperationsLevelPullback_additive l E g n
  let f := ((finiteModuleComparison l E g n).mapHomologicalComplex (.up ℤ)).app K
  refine ⟨f, ?_, ?_⟩
  · intro i U x
    rfl
  · intro h hh
    ext i U x
    exact (hh i U.unop x).trans (by rfl)

/-- The actual finite comparison chain map, uniquely fixed on every section. -/
def inverseImageFiniteComparisonComplex (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :=
  (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose

/-- The finite-level derived category, on the unfolded constant-coefficient presentation
used as the source and target of `integralOperationsLevelPullback`. -/
@[instance_reducible]
noncomputable def levelPullbackHasDerivedCategory
    (W : Scheme.{t}) (R : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

attribute [local instance] levelPullbackHasDerivedCategory

/-- Finite comparison in the derived category: the class of the sheafified tensor-unit
chain map, with the canonical exact-functor localization comparisons on both sides. -/
def inverseImagePullbackComparisonFinite
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    (inverseImageFiniteDerived l E g n).obj (DerivedCategory.Q.obj K) ⟶
      (integralOperationsLevelPullback l E g n).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) :=
  (inverseImageFiniteModules l E g n).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (inverseImageFiniteComparisonComplex l E g n K) ≫
      (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors.inv.app K

/-- In the recorded finite intrinsic presentation, the same comparison has exactly
finiteDerivedPullback as its target. The adjunction comparison preserves x tensor 1. -/
def inverseImagePullbackComparisonFiniteIntrinsic
    (F : Type t) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l F Y n) ℤ) :
    (inverseImageFiniteDerived l F g n).obj (DerivedCategory.Q.obj K) ⟶
      (finiteDerivedPullback l F n g).obj (DerivedCategory.Q.obj K) :=
  letI : Finite (Padic.coefficientExtensionRing l F (n + 1)) :=
    Padic.finite_coefficientExtensionRing l F (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e : integralOperationsLevelPullback l F g n ≅
      sfIntrinsicPullback (Padic.coefficientExtensionRing l F (n + 1)) g :=
    inverseImageFiniteIntrinsicPullbackComparison g (Padic.coefficientExtensionRing l F (n + 1))
  inverseImagePullbackComparisonFinite l F g hX hY n K ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K)

private abbrev coefficientProjection (W : Scheme.{t}) (n : ℕ) :=
  (sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)

private def reductionUnitRaw (n : ℕ) (M : integralTowerModules l E Y) :
    M.val ⟶ (PresheafOfModules.restrictScalars (coefficientProjection l E Y n).hom).obj
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M) where
  app U := (ModuleCat.extendRestrictScalarsAdj
    ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom).unit.app _
  naturality {U V} f := by
    ext x
    have h := SheafOfModules.UnrestrictedTowerProof.restriction_tmul
      (completedIntegralCommRingProjectionUnrestricted l E Y n) M f
      (1 : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) x
    simp only [map_one] at h
    with_unfolding_all exact h.symm

private def reductionUnitObj (n : ℕ) (M : integralTowerModules l E Y) :
    M ⟶ (SheafOfModules.restrictScalars (coefficientProjection l E Y n)).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj M) :=
  ⟨reductionUnitRaw l E (Y := Y) n M ≫
    (PresheafOfModules.restrictScalars (coefficientProjection l E Y n).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
        (𝟙 (integralCoefficientSheaf l E Y n).obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
            (completedIntegralCommRingProjectionUnrestricted l E Y n) M)) ≫
    (PresheafOfModules.restrictScalars (coefficientProjection l E Y n).hom).map
      (eqToHom (unrestrictedReduction_obj l E Y n M).symm).val⟩

private theorem reduction_generator_map (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N)
    (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
    ((unrestrictedIntegralReductionFunctor l E Y n).map a).val.app V
        (unrestrictedIntegralTensorSection l E Y n M V 1 x) =
      unrestrictedIntegralTensorSection l E Y n N V 1 (a.val.app V x) := by
  have h : eqToHom (unrestrictedReduction_obj l E Y n M).symm ≫
      (unrestrictedIntegralReductionFunctor l E Y n).map a =
      SheafOfModules.changeOfRingsHom (completedIntegralCommRingProjectionUnrestricted l E Y n)
        M a ≫ eqToHom (unrestrictedReduction_obj l E Y n N).symm := by
    rw [unrestrictedReduction_map]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  calc
    _ = (eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V
        ((SheafOfModules.changeOfRingsHom
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M a).val.app V
          (SheafOfModules.UnrestrictedTowerProof.tensorSection
            (completedIntegralCommRingProjectionUnrestricted l E Y n) M V 1 x)) :=
      congrArg (fun k ↦ k.val.app V
        (SheafOfModules.UnrestrictedTowerProof.tensorSection
          (completedIntegralCommRingProjectionUnrestricted l E Y n) M V 1 x)) h
    _ = _ := congrArg ((eqToHom (unrestrictedReduction_obj l E Y n N).symm).val.app V)
      (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M a V 1 x)

private def reductionUnit (n : ℕ) :
    𝟭 (integralTowerModules l E Y) ⟶ unrestrictedIntegralReductionFunctor l E Y n ⋙
      SheafOfModules.restrictScalars (coefficientProjection l E Y n) where
  app := reductionUnitObj l E (Y := Y) n
  naturality {M N} a := by
    ext U x
    exact (reduction_generator_map l E (Y := Y) n a U x).symm

private theorem inverseCoefficient_square (n : ℕ) :
    inv (inverseImageCompletedCoefficientMap l E g) ≫
        (isoSectionwiseInverseImage g RingCat).map (coefficientProjection l E Y n) =
      coefficientProjection l E X n ≫ inv (inverseImageFiniteCoefficientMap l E g n) := by
  have h : inverseImageCompletedCoefficientMap l E g ≫ coefficientProjection l E X n =
      (isoSectionwiseInverseImage g RingCat).map (coefficientProjection l E Y n) ≫
        inverseImageFiniteCoefficientMap l E g n := by
    exact limit.lift_π _ (op n)
  apply (cancel_mono (inverseImageFiniteCoefficientMap l E g n)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

private def inverseReductionTransport (n : ℕ) :
    SheafOfModules.restrictScalars (coefficientProjection l E Y n) ⋙
        inverseImageIntegralModules l E g ⟶
      inverseImageFiniteModules l E g n ⋙
        SheafOfModules.restrictScalars (coefficientProjection l E X n) where
  app N :=
    { val.app U := ModuleCat.ofHom
        (X := ((inverseImageIntegralModules l E g).obj
          ((SheafOfModules.restrictScalars (coefficientProjection l E Y n)).obj N)).val.obj U)
        (Y := ((SheafOfModules.restrictScalars (coefficientProjection l E X n)).obj
          ((inverseImageFiniteModules l E g n).obj N)).val.obj U)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a x ↦ by
            change ((coefficientProjection l E Y n).hom.app
                (op ((proEtaleIsoPostcompose g).obj U.unop))
                ((inv (inverseImageCompletedCoefficientMap l E g)).hom.app U a)) •
                (show N.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) from x) =
              ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U
                ((coefficientProjection l E X n).hom.app U a)) •
                (show N.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) from x)
            exact congrArg (fun z ↦ z •
                (show N.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) from x))
              (congrArg (fun k ↦ k.hom.app U a) (inverseCoefficient_square l E g n)) }
      val.naturality := by intros; ext x; rfl }
  naturality := by intros; ext U x; rfl

private def integralModuleComparison (n : ℕ) :
    inverseImageIntegralModules l E g ⟶
      unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E g n ⋙
        SheafOfModules.restrictScalars (coefficientProjection l E X n) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (reductionUnit l E (Y := Y) n) (inverseImageIntegralModules l E g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (unrestrictedIntegralReductionFunctor l E Y n)
      (inverseReductionTransport l E g n) ≫
    Functor.whiskerLeft (unrestrictedIntegralReductionFunctor l E Y n)
      (Functor.whiskerRight (finiteModuleComparison l E g n)
        (SheafOfModules.restrictScalars (coefficientProjection l E X n)))

/-- The compatible integral-to-finite maps are uniquely specified on every section:
reduce x to 1 tensor x, apply the finite pullback unit, and restrict along the
canonical comma arrow. The target is exactly the recorded restricted finite pullback. -/
theorem inverseImageReductionTheta_existsUnique (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ∃! f : ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (integralOperationsPullbackLevel l E g n).obj P,
      ∀ (i : ℤ) (U : X.ProEt)
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (f.f i).val.app (op U) x =
          (((integralOperationsPullbackLevel l E g n).obj P).X i).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)
              ((proEtaleIsoPostcompose g).obj U)
              (unrestrictedIntegralTensorSection l E Y n (P.X i)
                (op ((proEtaleIsoPostcompose g).obj U)) 1 x)) := by
  let := integralOperationsLevelPullback_additive l E g n
  let f := ((integralModuleComparison l E g n).mapHomologicalComplex (.up ℤ)).app P
  refine ⟨f, ?_, ?_⟩
  · intro i U x
    rfl
  · intro h hh
    ext i U x
    exact (hh i U.unop x).trans (by rfl)

/-- The canonical theta_n, fixed by reduction and the finite pullback unit. -/
def inverseImageReductionTheta (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (inverseImageReductionTheta_existsUnique l E g n P).exists.choose

/-- The theta maps commute strictly with every consecutive reduction. -/
theorem inverseImageReductionTheta_compatible (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    inverseImageReductionTheta l E g (n + 1) P ≫
        (integralOperationsPullbackTransition l E g n).app P =
      inverseImageReductionTheta l E g n P := by
  ext i U x
  have hθ (m : ℕ) := (inverseImageReductionTheta_existsUnique l E g m P).exists.choose_spec
  dsimp only [inverseImageReductionTheta]
  change (((integralOperationsPullbackTransition l E g n).app P).f i).val.app U
      ((((inverseImageReductionTheta_existsUnique l E g (n + 1) P).exists.choose).f i).val.app U
        x) = _
  erw [hθ (n + 1) i U.unop x, hθ n i U.unop x]
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let y := unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) (op V) 1 x
  have ht := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    P i V y
  have hr := congrArg (fun k ↦ k
      (integralOperationsPullbackGenerator l E g (n + 1)
        (((unrestrictedIntegralFiniteComplex l E Y (n + 1)).obj P).X i) V y))
    ((((integralOperationsPullbackTransition l E g n).app P).f i).val.naturality
      (proEtaleIsoCommaArrow g U.unop).op)
  have hy := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
    P i (op V) 1 x
  have hy' : (((unrestrictedIntegralTransition l E Y n).app P).f i).val.app (op V) y =
      unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x := by
    simpa only [y, unrestrictedIntegralTransition, map_one] using hy
  exact hr.trans (congrArg
    ((((integralOperationsPullbackLevel l E g n).obj P).X i).val.map
      (proEtaleIsoCommaArrow g U.unop).op) (ht.trans (congrArg
        (integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V) hy')))

/-- The product of the actual theta maps. -/
def inverseImageReductionProduct (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  Pi.lift (fun n ↦ inverseImageReductionTheta l E g n P)

/-- Strict compatibility gives the zero-homotopy equation for the Roos lift. -/
theorem inverseImageReductionProduct_lift_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P)
          (∏ᶜ fun n ↦ (integralOperationsPullbackLevel l E g n).obj P) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (inverseImageReductionProduct l E g P ≫
          towerTransitionEndomorphism
            (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E g).obj P))) =
      0 := by
  have h : inverseImageReductionProduct l E g P ≫
      towerTransitionEndomorphism
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E g).obj P)) =
      0 := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.comp_id, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
      zero_comp, inverseImageReductionProduct]
    have hs : integralOperationsTowerStep
        ((integralOperationsPullbackTowerFunctor l E g).obj P) n =
        (integralOperationsPullbackTransition l E g n).app P := by
      change ((Functor.ofOpSequence (integralOperationsPullbackTransition l E g)).map
        (homOfLE (Nat.le_succ n)).op).app P = _
      rw [Functor.ofOpSequence_map_homOfLE_succ]
    rw [hs, inverseImageReductionTheta_compatible, sub_self]
  rw [h]
  simp

/-- The concrete shifted-cone map z to (0, (theta_n(z))_n), using zero homotopy.
Its target is the existing strict Roos complex, with its actual differential. -/
def inverseImageRoosComparisonComplex
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E g).obj P :=
  CochainComplex.mappingCocone.lift _ (inverseImageReductionProduct l E g P) 0
    (inverseImageReductionProduct_lift_condition l E g P)

attribute [local irreducible] constantSheaf completedIntegralCoefficientSheafUnrestricted
  DerivedCategory.Q

/-- The inverse-image resolution is invertible after localization. -/
@[instance] theorem inverseImageResolution_isIso
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    IsIso (DerivedCategory.Q.map
      (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map q)) := by
  infer_instance

/-- The completed comparison for the chosen K-flat flat-term resolution q:P to K.
Compose the inverse of inverse-image(q), the explicit zero-homotopy Roos lift,
and the recorded representative identification with completed derived pullback.
This defines the map on the entire ambient category. Naturality, independence of
resolution and invertibility on constructible complete objects are separate assertions. -/
def inverseImagePullbackComparison
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (inverseImageIntegralDerived l E g).obj (DerivedCategory.Q.obj K) ⟶
      (integralDerivedPullback l E g).obj (DerivedCategory.Q.obj K) :=
  (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app K ≫
    inv (DerivedCategory.Q.map
      (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map q)) ≫
    DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
    (integralDerivedPullbackComparison l E g).inv.app P ≫
    (integralDerivedPullback l E g).map (DerivedCategory.Q.map q)

end AlgebraicGeometry.ProEtale
