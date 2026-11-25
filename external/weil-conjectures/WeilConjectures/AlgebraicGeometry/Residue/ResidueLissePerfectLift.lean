/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicRealization
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-!
# Perfect local lifting of a lisse residue reduction

Constant complexes use the existing constant-module sheafification. The coefficient
maps below are fixed uniquely on constant sections. Restriction means the actual
localized site, without identifying it with a separately chosen small skeleton.

## Main definitions

- `residueLisseDerivedConstant`: the exact constant module functor on derived categories.
- `residueLisseConstantComparison`: the normalized quotient coefficient comparison.

## Main statements

- `residue_lisse_perfect_lift`: the local perfect realization over completed coefficients.

## References

* Bhatt--Scholze, Lemma 6.6.8 and Proposition 6.6.11
* Stacks Tags 03CY and 09C6
* Stacks Tag 05RU
* Stacks Tags 0H7J and 09C6
* Stacks Tag 03DA
* Stacks Tag 099M
* Stacks Tags 03DJ and 08JB
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- Constant module sheafification is additive. -/
@[instance]
theorem residueLisseConstant_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (koszulConstantFunctor X A).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map
        (f + g))) = _
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    (((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map f)) +
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)).map g))) = _
  exact Functor.map_add _

/-- Constant module sheafification preserves finite limits. -/
@[instance]
theorem residueLisseConstant_preservesFiniteLimits
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    PreservesFiniteLimits (koszulConstantFunctor X A) := by
  have : PreservesFiniteLimits (koszulConstantFunctor X A ⋙
      SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A)) := by
    change PreservesFiniteLimits
      (forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} A)) AddCommGrpCat.{t + 1} ⋙
        constantSheaf (ProEt.topology X) AddCommGrpCat.{t + 1})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X A))

/-- Constant module sheafification preserves finite colimits. -/
@[instance]
theorem residueLisseConstant_preservesFiniteColimits
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    PreservesFiniteColimits (koszulConstantFunctor X A) := by
  have := (koszulConstantUnit_local X A).1
  have := (koszulConstantUnit_local X A).2
  have : PreservesFiniteColimits
      (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} A)) := by
    constructor
    intro J _ _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun U ↦ ?_)⟩
    exact hc
  exact comp_preservesFiniteColimits _ _

/-- The standard algebraic localization, with no equality imposed on site universes. -/
instance residueLisseAlgebraHasDerivedCategory (A : Type u) [CommRing A] :
    HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The standard localization for arbitrary coefficient sheaves on the small site. -/
instance residueLisseRingHasDerivedCategory (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    HasDerivedCategory (SheafOfModules.{t + 1} R) :=
  HasDerivedCategory.standard _

/-- The constant complex functor uses the canonical module-universe lift and scalar
restriction along ULift.ringEquiv before the recorded exact constant module functor. -/
def residueLisseDerivedConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  let e := (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom
  letI : (ModuleCat.restrictScalars.{t + 1} e).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{t + 1, t + 1, t} e).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{t + 1} e).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t} e).isRightAdjoint
  (ModuleCat.uliftFunctor.{t + 1, t} A ⋙
    ModuleCat.restrictScalars.{t + 1} e ⋙
      koszulConstantFunctor X A).mapDerivedCategory

/-- The constant-to-component comparison is fixed on all constant quotient sections. -/
theorem residueLisseConstantComparison_exists (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! φ : adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n,
      IsIso φ ∧ ∀ (U : X.ProEtᵒᵖ) (a : completedAdicQuotient d n),
        φ.hom.app U ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
          (finiteCoefficientScalarMap X (completedAdicQuotient d n)).app U a := by
  let Q := completedAdicQuotient d n
  let J := ProEt.topology X
  let F := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Q)
  let R := completedAdicFiniteCommRing X d n
  let α : F ⟶ R.obj :=
    { app := fun U ↦
        letI := completedAdicFiniteCommRingStructure X d n U
        CommRingCat.ofHom ((finiteCoefficientScalarMap X Q).app U).hom
      naturality := fun U V f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((finiteCoefficientScalarMap X Q).naturality f) }
  let φ : adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ R :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F R).symm α
  have hφ : toSheafify J F ≫ φ.hom = α :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F R).apply_symm_apply α
  have hαi : Presheaf.IsLocallyInjective J α := by
    rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (finiteCoefficientScalarMap X Q) (CategoryTheory.forget RingCat))
    infer_instance
  have hαs : Presheaf.IsLocallySurjective J α := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (finiteCoefficientScalarMap X Q) (CategoryTheory.forget RingCat))
    infer_instance
  have : Presheaf.IsLocallyInjective J (toSheafify J F ≫ φ.hom) := hφ.symm ▸ hαi
  have : Presheaf.IsLocallySurjective J (toSheafify J F ≫ φ.hom) := hφ.symm ▸ hαs
  have : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      J (toSheafify J F) φ.hom
  have : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J F) φ.hom
  have : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨inferInstance, inferInstance⟩
  refine ⟨φ, ⟨inferInstance, ?_⟩, ?_⟩
  · intro U a
    exact congrArg (fun k : F ⟶ R.obj ↦ (k.app U).hom a) hφ
  · intro ψ hψ
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ R.property
    refine Eq.trans ?_ hφ.symm
    ext U a
    exact hψ.2 U a

/-- The normalized constant-to-component quotient coefficient comparison. -/
def residueLisseConstantComparison (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶ completedAdicFiniteCommRing X d n :=
  (residueLisseConstantComparison_exists X d n).exists.choose

/-- The normalized comparison is invertible, including for the zero quotient ring. -/
private instance residueLisseConstantComparison_isIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    IsIso (residueLisseConstantComparison X d n) :=
  (residueLisseConstantComparison_exists X d n).exists.choose_spec.1

/-- The chosen comparison has the prescribed value on every constant section. -/
private theorem residueLisseConstantComparison_apply (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : completedAdicQuotient d n) :
    (residueLisseConstantComparison X d n).hom.app U
        ((koszulConstantUnit X (A ⧸ d.ideal ^ (n + 1))).app U a) =
      (finiteCoefficientScalarMap X (completedAdicQuotient d n)).app U a :=
  (residueLisseConstantComparison_exists X d n).exists.choose_spec.2 U a

/-- Fix the coefficient universe when applying the derived reconstruction API. -/
private theorem residueLisseAbLocallyBijective (X : Scheme.{t}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  finitePerfectModelsAbLocallyBijective X

attribute [local instance] residueLisseAbLocallyBijective

/-- The actual quotient-completion unit is invertible on an intrinsically complete object. -/
private theorem residueLisse_reconstruction (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hM : IsCompletedAdicDerivedComplete X d r a ha M) :
    IsIso ((reconstructionCompletionUnit X d).app M) := by
  obtain ⟨j, hj⟩ := reconstructionKoszulIntrinsicComparison X d r a M
  have : IsIso (completedAdicIntrinsicUnit X d r a M) := hM
  have hκ : IsIso ((reconstructionKoszulDerivedUnit X d r a).app M) :=
    IsIso.of_isIso_fac_right hj
  exact (koszulReconstruction X d r a ha).choose_spec.2 M hκ

/-- The standard localization on each slice, with its inherited coefficient ring. -/
instance residueLisseSliceHasDerivedCategory (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt) :
    HasDerivedCategory (SheafOfModules.{t + 1} (R.over U)) :=
  HasDerivedCategory.standard _

/-- Compare exact derived restriction with the localization representative in the statement. -/
private def residueLisseRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

/-- Transport an isomorphism through the statement's representative-based restriction. -/
private def residueLisseRestrictIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    {M N : DerivedCategory (SheafOfModules.{t + 1} R)} (e : M ≅ N) :
    ringedSiteDerivedRestrictionOfUniverses R U M ≅
      ringedSiteDerivedRestrictionOfUniverses R U N :=
  (residueLisseRestrictionComparison X R U M).symm ≪≫
    (ringedDerivedRestrictionGeneral R U).mapIso e ≪≫
      residueLisseRestrictionComparison X R U N

/-- The exact constant functor computes constant complexes termwise. -/
private def residueLisseConstantComplexComparison (X : Scheme.{t})
    (B : Type t) [CommRing B] (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    (residueLisseDerivedConstant X B).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (finiteModelConstantComplex X B P) := by
  let e := (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  have : (ModuleCat.restrictScalars.{t + 1} e).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{t + 1, t + 1, t} e).isLeftAdjoint
  have : (ModuleCat.restrictScalars.{t + 1} e).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t} e).isRightAdjoint
  let F := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1} e ⋙ koszulConstantFunctor X B
  exact F.mapDerivedCategoryFactors.app P

/-- A derived-complete complex whose residue reduction is etale locally a constant
perfect complex is pro-etale locally the completed realization of a perfect A-complex.
The sieve on the final object expresses the covering, including an empty covering
when X is empty. Perfectness is exactly the recorded bounded finite-projective model.
-/
theorem residue_lisse_perfect_lift (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [IsAdicComplete d.ideal A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (M : DerivedCategory (CompletedAdicModules X d))
    (_hcomplete : IsCompletedAdicDerivedComplete X d r a ha M)
    (_hresidue : ∃ S : Sieve (⊤_ X.Etale), S ∈ X.smallEtaleTopology (⊤_ X.Etale) ∧
      ∀ (V : X.Etale) (f : V ⟶ ⊤_ X.Etale), S f →
        ∃ P : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V)
                ((completedAdicQuotientReduction X d 0).obj M) ≅
              ringedSiteDerivedRestrictionOfUniverses
                (completedAdicFiniteRing X d 0)
                ((toProEt X).obj V)
                ((completedAdicDerivedChange X
                    (residueLisseConstantComparison X d 0)).obj
                  ((residueLisseDerivedConstant X (A ⧸ d.ideal ^ (0 + 1))).obj P)))) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        ∃ P : DerivedCategory (ModuleCat.{t} A),
          DerivedCategory.IsPerfectRingComplex P ∧
          Nonempty
            (ringedSiteDerivedRestrictionOfUniverses
                (completedAdicRing X d) U M ≅
              ringedSiteDerivedRestrictionOfUniverses
                (completedAdicRing X d) U
                ((completedAdicDerivedChange X (completedAdicScalar X d)).obj
                  ((residueLisseDerivedConstant X A).obj P))) := by
  have hφ (n : ℕ) : IsIso (residueLisseConstantComparison X d n) := inferInstance
  have hnorm : FinitePerfectModelsNormalized X d (residueLisseConstantComparison X d) :=
    residueLisseConstantComparison_apply X d
  have hcompat := finitePerfectModels_normalized_compatible X d
    (residueLisseConstantComparison X d) hnorm
  have hmodels : HasUniformFinitePerfectModels X d
      (residueLisseConstantComparison X d) M := by
    apply residuePerfect_finite_quotient_models X d
      (residueLisseConstantComparison X d) hφ hcompat M
    obtain ⟨S, hS, hlocal⟩ := _hresidue
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨P, hP, ⟨e⟩⟩ := hlocal V f hf
    obtain ⟨K, a, b, haK, hbK, hK, ⟨eK⟩⟩ := hP
    refine ⟨K, a, b, haK, hbK, hK, ⟨e ≪≫ ?_⟩⟩
    apply residueLisseRestrictIso X (completedAdicFiniteRing X d 0) ((toProEt X).obj V)
    apply (completedAdicDerivedChange X (residueLisseConstantComparison X d 0)).mapIso
    exact (residueLisseDerivedConstant X _).mapIso eK ≪≫
      residueLisseConstantComplexComparison X _ K
  obtain ⟨S, hS, hlocal⟩ := finitePerfectModels_adic_realization X d
    (residueLisseConstantComparison X d) hφ hcompat M hmodels
  have := residueLisse_reconstruction X d r a ha M _hcomplete
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨P, c, b, hc, hb, hP, ⟨e⟩⟩ := hlocal U f hf
  refine ⟨DerivedCategory.Q.obj P, ⟨P, c, b, hc, hb, hP, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  refine residueLisseRestrictIso X (completedAdicRing X d) U
    (asIso ((reconstructionCompletionUnit X d).app M)) ≪≫ e ≪≫ ?_
  apply residueLisseRestrictIso X (completedAdicRing X d) U
  exact (completedAdicDerivedChange X (completedAdicScalar X d)).mapIso
    (residueLisseConstantComplexComparison X A P).symm

end AlgebraicGeometry.Scheme
