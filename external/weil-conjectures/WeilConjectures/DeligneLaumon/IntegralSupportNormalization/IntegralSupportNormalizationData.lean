/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralOrdinaryRecollementRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # Data for normalized integral support operations

The existing definitions are shared by the separate open and closed support proofs.
Their public names, signatures and bodies agree with the original theorem module.
Source: smooth-purity localization integral and rational support paragraphs;
Stacks 09AA, 09BM, 09BN, 0GL1, 0A07, 04C4 and 095R
(blueprint: def-sf-integral-support-normalization-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary open extension with the recorded completed coefficient identifications.
Source: Stacks 03DI--03DJ
(blueprint: lem-sf-integral-support-functor-normalization). -/
abbrev ordinaryOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).mapDerivedCategory

/-- The identity base change preserves constant sections, by naturality of sheafification.
Source: Stacks 03D8; (blueprint: lem-sf-integral-support-functor-normalization). -/
private theorem constantDirectImageId (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    proEtaleConstantDirectImageMap (𝟙 X) CommRingCat.{u + 1} A =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.app
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj A) _).injective
  rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext V
  change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange (𝟙 X)).op.obj V) =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app V ≫
      (sheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op
  have h := (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op
  change 𝟙 A ≫ _ = _ at h
  exact (Category.id_comp _).symm.trans h

/-- Finite quotient projections identify the completed identity coefficient map uniquely.
Source: Stacks 03CO; (blueprint: lem-sf-integral-support-functor-normalization). -/
private theorem completedDirectImageId (X : Scheme.{u}) :
    sfCompletedCoefficientMap l E (𝟙 X) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.app
        (completedIntegralCommRingSheafUnrestricted l E X) := by
  apply (sfCompletedCoefficientMap_existsUnique l E (𝟙 X)).unique
  · exact (sfCompletedCoefficientMap_existsUnique l E (𝟙 X)).exists.choose_spec
  · intro n
    rw [show proEtaleCoefficientDirectImageMap (𝟙 X)
        (Padic.coefficientExtensionRing l E (n + 1)) = _ from constantDirectImageId X _]
    exact ((AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.naturality
      (completedIntegralCommRingProjectionUnrestricted l E X n)).symm

/-- Taking the adjoint of the prescribed completed pullback recovers that identity map.
Source: Stacks 03D8; (blueprint: lem-sf-integral-support-functor-normalization). -/
private theorem ringDirectImageId (X : Scheme.{u}) :
    proEtaleRingDirectImageMap (𝟙 X) ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull
          (𝟙 X)) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.app
        (completedIntegralCommRingSheafUnrestricted l E X) := by
  change (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).homEquiv _ _
    (PurCompactSupport.completedPullMap l E (𝟙 X)) = _
  rw [PurCompactSupport.completedPullMap, Equiv.apply_symm_apply, completedDirectImageId]

/-- Identity-site module transport, with the coefficient sheaf kept abstract.
Source: Stacks 03D8; (blueprint: lem-sf-integral-support-functor-normalization). -/
@[irreducible] private def moduleSiteIdentity (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ψ : R ⟶ ((proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).obj R)
    (h : (𝟙 R) ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).app R = ψ) :
    SheafOfModules.pushforward.{u + 1} ψ ≅ 𝟭 (SheafOfModules.{u + 1} R) :=
  (SheafOfModules.pushforwardCongr₂
    (F := proEtaleBaseChange (𝟙 X)) (G := 𝟭 X.ProEt)
    (J := ProEt.topology X) (K := ProEt.topology X) (T := R) (S := R)
    (ψ := ψ) (𝟙 R) (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) h).symm ≪≫
      SheafOfModules.pushforwardId R

/-- The inverse comparison acts by restriction along the identity base change. -/
private theorem moduleSiteIdentity_sections (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (ψ : R ⟶ ((proEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).obj R)
    (h : (𝟙 R) ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).app R = ψ)
    (M : SheafOfModules.{u + 1} R) (V : X.ProEt) (x : M.val.obj (op V)) :
    ((moduleSiteIdentity X R ψ h).inv.app M).val.app (op V) x =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x := by
  unfold moduleSiteIdentity
  rfl

/-- Explicit identity comparison obtained by the site identity and coefficient equality.
Source: Stacks 03D8; (blueprint: lem-sf-integral-support-functor-normalization). -/
@[irreducible] private def identityModuleCandidate (X : Scheme.{u}) :
    proEtaleRingModuleDirectImage (𝟙 X)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull (𝟙 X)) ≅
        𝟭 (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X)) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (completedIntegralCommRingSheafUnrestricted l E X)
  let a := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
  have h : (𝟙 R) ≫ (Functor.sheafPushforwardContinuousNatTrans a.hom
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology X)).app R =
      ⟨Functor.whiskerRight
        (proEtaleRingDirectImageMap (𝟙 X) ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull (𝟙 X))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ := by
    rw [Category.id_comp]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change _ = (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((proEtaleRingDirectImageMap (𝟙 X) ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull (𝟙 X))).hom.app V)
    rw [ringDirectImageId]
    rfl
  exact moduleSiteIdentity X R _ h

/-- The completed-coefficient comparison has the prescribed section formula. -/
private theorem identityModuleCandidate_sections (X : Scheme.{u})
    (M : proEtaleRingModules X ((PurCompactSupport.completed l E).ring X))
    (V : X.ProEt) (x : M.val.obj (op V)) :
    ((identityModuleCandidate l E X).inv.app M).val.app (op V) x =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x := by
  unfold identityModuleCandidate
  exact moduleSiteIdentity_sections X _ _ _ M V x

/-- Sectionwise uniqueness with the coefficient ring and direct-image functor abstract. -/
private theorem identityIso_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (F : SheafOfModules.{u + 1} R ⥤ SheafOfModules.{u + 1} R)
    (e e' : F ≅ 𝟭 (SheafOfModules.{u + 1} R))
    (h : ∀ (M : SheafOfModules.{u + 1} R) (V : X.ProEt)
      (x : M.val.obj (op V)),
      (e.inv.app M).val.app (op V) x = (e'.inv.app M).val.app (op V) x) : e = e' := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h M V.unop

/-- Identity direct image, uniquely fixed on every section by the identity base change.
Source: Stacks 03D8; localization proof, compactification (j,id)
(blueprint: lem-sf-integral-support-functor-normalization).
Proof: pull sections across V times_X X = V. The coefficient structure map has the
same finite projections as this pullback. Thus the section map is linear, natural,
and invertible. Sections determine module maps, so they determine this iso uniquely. -/
theorem identityModuleImage_existsUnique (X : Scheme.{u}) :
    ∃! e : proEtaleRingModuleDirectImage (𝟙 X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull (𝟙 X)) ≅
          𝟭 (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X)),
      ∀ (M : proEtaleRingModules X ((PurCompactSupport.completed l E).ring X))
        (V : X.ProEt) (x : M.val.obj (op V)),
        (e.inv.app M).val.app (op V) x =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op x := by
  refine ⟨identityModuleCandidate l E X, identityModuleCandidate_sections l E X, ?_⟩
  intro e' he'
  apply identityIso_ext X _ _ e' (identityModuleCandidate l E X)
  intro M V x
  exact (he' M V x).trans (identityModuleCandidate_sections l E X M V x).symm

/-- The section-normalized identity direct image.
Source: Stacks 03D8
(blueprint: lem-sf-integral-support-functor-normalization). -/
def identityModuleImage (X : Scheme.{u}) := (identityModuleImage_existsUnique l E X).exists.choose

/-- Derive the section-normalized identity and identify the derived identity termwise.
Source: Stacks 015F, 03D8
(blueprint: lem-sf-integral-support-functor-normalization). -/
def identityImage (X : Scheme.{u}) :
    proEtaleRingDerivedDirectImage (𝟙 X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull (𝟙 X)) ≅
      𝟭 (DerivedCategory (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X))) :=
  Functor.rightDerivedFunctorNatIso (identityModuleImage l E X) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory
      (𝟭 (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X))) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Remove the proper identity factor in the actual compactification (j,id).
Source: localization integral paragraph; Stacks 03DI
(blueprint: lem-sf-integral-support-functor-normalization). -/
def openIdentity {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PurCompactSupport.image (PurCompactSupport.completed l E)
        (Compactification.ofIsOpenImmersion j) ≅ ordinaryOpen l E j :=
  isoWhiskerLeft (ordinaryOpen l E j) (identityImage l E X) ≪≫ Functor.rightUnitor _

/-- The whole-system pullback/reduction arrow, including the actual reduction counit.
Source: Stacks 0941, 099N; localization proof Step 3
(blueprint: lem-sf-integral-support-functor-normalization). -/
def closedReduction {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) :
    sfOrdinaryDerivedPull l E i ⋙ FrobeniusExchange.reduction l E Z ⟶
      FrobeniusExchange.reduction l E X ⋙ integralComparisonDerivedSequencePullback l E i :=
  whiskerRight C.pull (FrobeniusExchange.reduction l E Z) ≫
    integralComparisonPullbackCounit l E i
      ((FrobeniusExchange.models l E).system X)
      ((FrobeniusExchange.models l E).system Z)
      ((FrobeniusExchange.models l E).roos Z)
      ((FrobeniusExchange.models l E).pullback i)

/-- The direct-image/strict-limit comparison is the canonical right-adjunction conjugate.
The input iso is the specified quotient comparison, not an arbitrary comparison of values.
Source: Stacks 0A07, 07A6
(blueprint: lem-sf-integral-support-functor-normalization). -/
def closedLimit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) [IsIso (closedReduction l E i C)] :
    coefficientSequenceLimit l E Z ⋙ sfCompletedDerivedDirectImage l E i ≅
      FrobeniusExchange.systemDirect l E i ⋙ coefficientSequenceLimit l E X :=
  conjugateIsoEquiv
    ((sfOrdinaryDerivedAdjunction l E i).comp
      ((FrobeniusExchange.models l E).system Z).adjunction)
    (((FrobeniusExchange.models l E).system X).adjunction.comp
      (FrobeniusExchange.systemAdjunction l E i))
    (asIso (closedReduction l E i C)).symm

/-- The canonical alpha is ordinary image of the actual completion unit, then closedLimit.
Source: Stacks 0A07; localization proof Step 3
(blueprint: lem-sf-integral-support-functor-normalization). -/
def closedAlpha {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (C : SfOrdinaryIntegralComparison l E i) [IsIso (closedReduction l E i C)] :
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i ⟶
      (sfIntegralConstructible l E Z).ι ⋙ FrobeniusExchange.integralDirectImage l E i :=
  whiskerLeft (sfIntegralConstructible l E Z).ι
    (whiskerRight (((FrobeniusExchange.models l E).system Z).adjunction.unit)
      (sfCompletedDerivedDirectImage l E i) ≫
        whiskerLeft (FrobeniusExchange.reduction l E Z) (closedLimit l E i C).hom)

/-- The ordinary open pullback in the same completed coefficient presentation.
Source: Stacks 03DI, 03D2
(blueprint: lem-sf-integral-support-functor-normalization). -/
abbrev ordinaryOpenPull {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  proEtaleRingDerivedPullback j ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).ring U) ((PurCompactSupport.completed l E).pull j)

/-- The ordinary derived open adjunction, with its termwise units and counits.
Source: Stacks 015F, 03DI
(blueprint: lem-sf-integral-support-functor-normalization). -/
def ordinaryOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ordinaryOpen l E j ⊣ ordinaryOpenPull l E j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j)

/-- Identity on systems is fixed by the actual pullback identity and its right adjunction.
Source: Stacks 03D8, 0941
(blueprint: lem-sf-integral-support-functor-normalization). -/
def systemDirectId (X : Scheme.{u}) :
    FrobeniusExchange.systemDirect l E (𝟙 X) ≅ 𝟭 (coefficientSequenceDerived l E X) :=
  Adjunction.rightAdjointUniq
    ((FrobeniusExchange.systemAdjunction l E (𝟙 X)).ofNatIsoLeft
      (integralComparisonSystemUnit l E X)) Adjunction.id

/-- Total inverse limit has the shift induced by exact scalar restriction and derived limit.
Source: Stacks 0941
(blueprint: lem-sf-integral-support-functor-normalization). -/
instance limitShift (T : Scheme.{u}) : (coefficientSequenceLimit l E T).CommShift ℤ := by
  unfold coefficientSequenceLimit coefficientConstantTowerLimit
  infer_instance

/-- Reduction has the left-adjoint shift of the specified total inverse limit.
Source: Stacks 0941, 099N
(blueprint: lem-sf-integral-support-functor-normalization). -/
instance reductionShift (T : Scheme.{u}) : (FrobeniusExchange.reduction l E T).CommShift ℤ :=
  ((FrobeniusExchange.models l E).system T).adjunction.leftAdjointCommShift ℤ

/-- Direct image uses the whole-system shift followed by the signed total-limit shift.
Source: Stacks 0941, 0A07
(blueprint: lem-sf-integral-support-functor-normalization). -/
instance directShift {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (FrobeniusExchange.integralDirectImage l E i).CommShift ℤ := by
  unfold FrobeniusExchange.integralDirectImage FrobeniusExchange.realize
  infer_instance

/-- Inverse of the normalized finite evaluation mate for direct image.
Source: Zheng 4.10; Stacks 0941
(blueprint: lem-sf-integral-support-functor-normalization). -/
def directEvaluationIso {Z X : Scheme.{u}} (i : Z ⟶ X) (n : ℕ) :=
  letI := FrobeniusExchange.systemDirectEvaluation_isIso l E i n
  asIso (FrobeniusExchange.systemDirectEvaluation l E i n)

/-- The support normalization, retaining the specified functors, maps and shifts.
All inherited geometric properties are outputs, not additional hypotheses. The closed
comparison uses the actual unit and the strict-limit conjugate defined above. The open
comparison is the fixed compact-support realization followed by identity direct image.
Source: localization integral and rational paragraphs; Stacks 09AA, 09BM, 0GL1, 0A07
(blueprint: lem-sf-integral-support-functor-normalization). -/
structure Normalization (D : FiniteFieldDatum.{u})
    {Z U X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  primeUnit : IsUnit (l : D.k)
  [openOver : U.Over (Spec (.of D.k))]
  [closedOver : Z.Over (Spec (.of D.k))]
  [openIsOver : j.IsOver (Spec (.of D.k))]
  [closedIsOver : i.IsOver (Spec (.of D.k))]
  [openFiniteType : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [openQuasiCompact : QuasiCompact (U ↘ Spec (.of D.k))]
  [closedFiniteType : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [closedQuasiCompact : QuasiCompact (Z ↘ Spec (.of D.k))]
  [openQuasiCompactMap : QuasiCompact j]
  [invertibleX : ∀ x : X, Invertible (l : X.residueField x)]
  [invertibleU : ∀ x : U, Invertible (l : U.residueField x)]
  [invertibleZ : ∀ x : Z, Invertible (l : Z.residueField x)]
  closed : SfOrdinaryIntegralComparison l E i
  [closedReductionIso : IsIso (closedReduction l E i closed)]
  [closedModuleColimits : PreservesFiniteColimits (sfCompletedModuleDirectImage l E i)]
  [closedModuleLimits : PreservesFiniteLimits (sfCompletedModuleDirectImage l E i)]
  dj : sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j
  dj_formula : dj = (sfQcqsCompactSupportRealization l E D.k primeUnit
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)
  di : (sfIntegralConstructible l E Z).ι ⋙ FrobeniusExchange.integralDirectImage l E i ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  di_formula : di.inv = closedAlpha l E i closed
  openPull : constructibleIntegralPullback l E j ⋙ (sfIntegralConstructible l E U).ι ≅
    (sfIntegralConstructible l E X).ι ⋙ ordinaryOpenPull l E j
  closedPull : constructibleIntegralPullback l E i ⋙ (sfIntegralConstructible l E Z).ι ≅
    (sfIntegralConstructible l E X).ι ⋙ sfOrdinaryDerivedPull l E i
  closedPull_formula : ∀ K : sfIntegralConstructibleCategory l E X,
    closedPull.hom.app K ≫ closed.pull.app K.obj = 𝟙 _
  openComplete : ∀ K : DerivedCategory (scalarReductionSource l E U),
    IsSfDerivedComplete l E U K → IsSfDerivedComplete l E X ((ordinaryOpen l E j).obj K)
  closedComplete : ∀ K : DerivedCategory (scalarReductionSource l E Z),
    IsSfDerivedComplete l E Z K →
      IsSfDerivedComplete l E X ((sfCompletedDerivedDirectImage l E i).obj K)
  openConstructible : ∀ K : sfIntegralConstructibleCategory l E U,
    sfIntegralConstructible l E X ((ordinaryOpen l E j).obj K.obj)
  closedConstructible : ∀ K : sfIntegralConstructibleCategory l E Z,
    sfIntegralConstructible l E X ((sfCompletedDerivedDirectImage l E i).obj K.obj)
  openInterval : ∀ (K : sfIntegralConstructibleCategory l E U) (a b : ℤ),
    IntegralImmersionNormalization.HasReductionInterval l E U K.obj a b →
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((ordinaryOpen l E j).obj K.obj) a b
  closedInterval : ∀ (K : sfIntegralConstructibleCategory l E Z) (a b : ℤ),
    IntegralImmersionNormalization.HasReductionInterval l E Z K.obj a b →
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((sfCompletedDerivedDirectImage l E i).obj K.obj) a b
  openReduction : ∀ n : ℕ,
    (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j ⋙
        scalarReductionDerivedExtension l E X n ≅
      (sfIntegralConstructible l E U).ι ⋙ scalarReductionDerivedExtension l E U n ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n+1))
          (Compactification.ofIsOpenImmersion j)
  openProjection : ∀ (K : sfIntegralConstructibleCategory l E U) (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map (dj.hom.app K) ≫
      (openReduction n).hom.app K =
    (sfCompactSupportFiniteReductionIso l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E K n).hom
  closedProjection : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    di.inv.app K ≫
      (coefficientSequenceProjection l E X n).app
        ((FrobeniusExchange.systemDirect l E i).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) =
    (sfCompletedDerivedDirectImage l E i).map
      (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj ≫
        (coefficientSequenceProjection l E Z n).app
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (sfDerivedRestrictionComparison l E i n).hom.app
        ((coefficientSequenceDerivedEvaluation l E Z n).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((directEvaluationIso l E i n).inv.app
          ((FrobeniusExchange.reduction l E Z).obj K.obj))
  closedReductionComparison : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    IsIso (sfOrdinaryPushReduction l E i K.obj n)
  openAdjunction : sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E ⊣ constructibleIntegralPullback l E j
  closedAdjunction : constructibleIntegralPullback l E i ⊣
    FrobeniusExchange.directImageFunctor l E D.k primeUnit i
  openUnit : ∀ N : sfIntegralConstructibleCategory l E U,
    (openAdjunction.unit.app N).hom ≫ openPull.hom.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj N) =
      (ordinaryOpenAdjunction l E j).unit.app N.obj ≫
        (ordinaryOpenPull l E j).map (dj.inv.app N)
  openCounit : ∀ K : sfIntegralConstructibleCategory l E X,
    (openAdjunction.counit.app K).hom =
      dj.hom.app ((constructibleIntegralPullback l E j).obj K) ≫
        (ordinaryOpen l E j).map (openPull.hom.app K) ≫
          (ordinaryOpenAdjunction l E j).counit.app K.obj
  closedUnit : ∀ K : sfIntegralConstructibleCategory l E X,
    (closedAdjunction.unit.app K).hom ≫
        di.hom.app ((constructibleIntegralPullback l E i).obj K) =
      (sfOrdinaryDerivedAdjunction l E i).unit.app K.obj ≫
        (sfCompletedDerivedDirectImage l E i).map (closedPull.inv.app K)
  closedCounit : ∀ M : sfIntegralConstructibleCategory l E Z,
    (closedAdjunction.counit.app M).hom =
      closedPull.hom.app ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M) ≫
        (sfOrdinaryDerivedPull l E i).map (di.hom.app M) ≫
          (sfOrdinaryDerivedAdjunction l E i).counit.app M.obj
  openSystemUnit : ∀ N : sfIntegralConstructibleCategory l E U,
    (FrobeniusExchange.reduction l E U).map (openAdjunction.unit.app N).hom ≫
      (integralComparisonPullbackCounit l E j
        ((FrobeniusExchange.models l E).system X)
        ((FrobeniusExchange.models l E).system U)
        ((FrobeniusExchange.models l E).roos U)
        ((FrobeniusExchange.models l E).pullback j)).app
          (((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
            (Compactification.ofIsOpenImmersion j) E).obj N).obj) ≫
      (integralComparisonDerivedSequencePullback l E j).map
        ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
          (Compactification.ofIsOpenImmersion j)).app N ≫
          (systemDirectId l E X).hom.app
            ((FrobeniusExchange.systemDerivedOpen l E j).obj
              ((FrobeniusExchange.reduction l E U).obj N.obj))) =
    (FrobeniusExchange.systemDerivedOpenAdjunction l E j).unit.app
      ((FrobeniusExchange.reduction l E U).obj N.obj)
  openSystemCounit : ∀ K : sfIntegralConstructibleCategory l E X,
    (FrobeniusExchange.reduction l E X).map (openAdjunction.counit.app K).hom =
      ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
        (Compactification.ofIsOpenImmersion j)).app
          ((constructibleIntegralPullback l E j).obj K)) ≫
      (systemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj
            ((constructibleIntegralPullback l E j).obj K).obj)) ≫
      (FrobeniusExchange.systemDerivedOpen l E j).map
        ((integralComparisonPullbackCounit l E j
          ((FrobeniusExchange.models l E).system X)
          ((FrobeniusExchange.models l E).system U)
          ((FrobeniusExchange.models l E).roos U)
          ((FrobeniusExchange.models l E).pullback j)).app K.obj) ≫
      (FrobeniusExchange.systemDerivedOpenAdjunction l E j).counit.app
        ((FrobeniusExchange.reduction l E X).obj K.obj)
  [openShift : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E).CommShift ℤ]
  [closedShift : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).CommShift ℤ]
  openShiftNormalization : NatTrans.CommShift dj.hom ℤ
  closedShiftNormalization : NatTrans.CommShift di.hom ℤ
  closedShiftInclusion : ∀ (n : ℤ) (M : sfIntegralConstructibleCategory l E Z),
    (((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).commShiftIso n).hom.app
      M).hom ≫ ((sfIntegralConstructible l E X).ι.commShiftIso n).hom.app
        ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M) =
      (FrobeniusExchange.integralDirectImage l E i).map
        (((sfIntegralConstructible l E Z).ι.commShiftIso n).hom.app M) ≫
      ((FrobeniusExchange.integralDirectImage l E i).commShiftIso n).hom.app M.obj
  closedTermwiseShift : NatTrans.CommShift
    (isoWhiskerLeft (sfIntegralConstructible l E Z).ι
      (sfCompletedModuleDirectImage l E i).rightDerivedFunctorIsoMapDerivedCategory).hom ℤ
  openExact : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E).IsTriangulated
  closedExact : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).IsTriangulated
  openLinear : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E).Linear (Padic.coefficientExtensionIntegers l E)
  closedLinear : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).Linear
    (Padic.coefficientExtensionIntegers l E)
  disjoint : ∀ M : sfIntegralConstructibleCategory l E Z,
    IsZero ((constructibleIntegralPullback l E j).obj
      ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M))

end WeilConjectures.IntegralSupportNormalization
