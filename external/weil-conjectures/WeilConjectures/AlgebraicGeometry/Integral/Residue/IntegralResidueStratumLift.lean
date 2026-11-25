/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumConstant
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels

/-! # Lifting a perfect residue model on a single stratum

## References

* Bhatt--Scholze, Proposition 6.6.11, forward implication
* Bhatt--Scholze, Lemma 6.6.8
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

-- Fix the module size before generic ring-sheaf instance search.
private theorem sliceBaseAbLocallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  finitePerfectModelsAbLocallyBijective S

private theorem sliceOverAbLocallyBijective (S : Scheme.{u}) (U : S.ProEt) :
    ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  strictPerfectSliceLocallyBijective S U

attribute [local instance 100000] sliceBaseAbLocallyBijective sliceOverAbLocallyBijective

private noncomputable def sliceRestrictionComparison
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (U : S.ProEt) (K : DerivedCategory.{u + 2} (SheafOfModules.{u + 1} R)) :
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U).obj K ≅
      ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U K := by
  let F := SheafOfModules.overFunctor.{u + 1} R U
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R U).2.2
  exact F.mapDerivedCategory.{u + 2, u + 2}.mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    F.mapDerivedCategoryFactors.{u + 2, u + 2}.app (DerivedCategory.Q.objPreimage K)

private noncomputable def sliceRestrictionIso
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1}) (U : S.ProEt)
    {K L : DerivedCategory.{u + 2} (SheafOfModules.{u + 1} R)} (e : K ≅ L) :
    ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U K ≅
      ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U L :=
  (sliceRestrictionComparison S R U K).symm ≪≫
    (ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, u + 2, u + 2} R U).mapIso e ≪≫
      sliceRestrictionComparison S R U L

private theorem sliceCoefficient_reflects
    (S : Scheme.{u}) {R B : Sheaf (ProEt.topology S) CommRingCat.{u + 1}}
    (e : R ≅ B) (U : S.ProEt) {K L : DerivedCategory.{u + 2} (pbcModules S R)}
    (h : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1}
          ((adicLisseForget S).obj B) U
          ((pbcDerivedRestrict e.inv).obj K) ≅
        ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1}
          ((adicLisseForget S).obj B) U
          ((pbcDerivedRestrict e.inv).obj L))) :
    Nonempty
      (ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1}
          ((adicLisseForget S).obj R) U K ≅
        ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1}
          ((adicLisseForget S).obj R) U L) := by
  let R' := (adicLisseForget S).obj R
  let B' := (adicLisseForget S).obj B
  let e' : R' ≅ B' := (adicLisseForget S).mapIso e
  let eU := ((ProEt.topology S).overPullback RingCat.{u + 1} U).mapIso e'
  let G := SheafOfModules.restrictScalars.{u + 1} e'.inv
  let H := SheafOfModules.restrictScalars.{u + 1} eU.inv
  have : G.IsEquivalence := WeilConjectures.restriction_isEquivalence e'.symm
  have : H.IsEquivalence := WeilConjectures.restriction_isEquivalence eU.symm
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R' U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R' U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} R' U).2.2
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B' U).1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B' U).2.1
  have := (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1} B' U).2.2
  let F := SheafOfModules.overFunctor.{u + 1} R' U
  let F' := SheafOfModules.overFunctor.{u + 1} B' U
  let q : F ⋙ H ≅ G ⋙ F' := Iso.refl _
  let qD := Functor.mapDerivedCategorySquareIso q
  have : H.mapDerivedCategory.{u + 2, u + 2}.IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory H
  obtain ⟨j⟩ := h
  let j' : H.mapDerivedCategory.{u + 2, u + 2}.obj (F.mapDerivedCategory.{u + 2, u + 2}.obj K) ≅
      H.mapDerivedCategory.{u + 2, u + 2}.obj (F.mapDerivedCategory.{u + 2, u + 2}.obj L) :=
    qD.app K ≪≫
      sliceRestrictionComparison S B' U (G.mapDerivedCategory.{u + 2, u + 2}.obj K) ≪≫ j ≪≫
      (sliceRestrictionComparison S B' U (G.mapDerivedCategory.{u + 2, u + 2}.obj L)).symm ≪≫
        (qD.app L).symm
  exact ⟨(sliceRestrictionComparison S R' U K).symm ≪≫
    H.mapDerivedCategory.{u + 2, u + 2}.preimageIso j' ≪≫ sliceRestrictionComparison S R' U L⟩

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Complete integral coefficients lift perfect constant residue models on one stratum. -/
theorem integralResidueStratum_lift
    (T : Scheme.{u}) [IsNoetherian T] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hcomplete : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K)
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (g : S ⟶ T) [IsImmersion g]
    (𝒰 : Scheme.Cover.{u} etalePrecoverage S)
    (C : CochainComplex
      (FiniteCoefficientModules T (PbcQuotient (pbcIntegralDatum l E) 0)) ℤ)
    (eC : Nonempty
      (DerivedCategory.Q.obj (((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison T
          (PbcQuotient (pbcIntegralDatum l E) 0)).hom).mapHomologicalComplex (.up ℤ)).obj C) ≅
        (pbcCompletedReduction T (pbcIntegralDatum l E) 0).obj K))
    (hmodels : ∀ j : 𝒰.I₀,
      ∃ P : CochainComplex (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) 0)) ℤ,
        @DerivedCategory.IsPerfectRingComplex (PbcQuotient (pbcIntegralDatum l E) 0) _
          (HasDerivedCategory.standard _) (DerivedCategory.Q.obj P) ∧
        Nonempty
          ((finiteCoefficientDerivedPullback T (PbcQuotient (pbcIntegralDatum l E) 0)
            (𝒰.f j ≫ g)).obj (DerivedCategory.Q.obj C) ≅
            (finiteCoefficientRealization (𝒰.X j)
              (PbcQuotient (pbcIntegralDatum l E) 0)).mapDerivedCategory.obj
                (DerivedCategory.Q.obj
                  (((constantSheaf (ProEt.topology (𝒰.X j))
                  (ModuleCat.{u + 1} (PbcQuotient (pbcIntegralDatum l E) 0))).mapHomologicalComplex
                      (.up ℤ)).obj P)))) :
    ∃ V : Sieve (⊤_ S.ProEt), V ∈ ProEt.topology S (⊤_ S.ProEt) ∧
      ∀ (U : S.ProEt) (f : U ⟶ ⊤_ S.ProEt), V f →
        ∃ P : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)),
          @DerivedCategory.IsPerfectRingComplex (PbcIntegralRing l E) _
            (HasDerivedCategory.standard _) P ∧
          Nonempty (integralLocalDerived g (pbcAdicCompletion T (pbcIntegralDatum l E)) U K ≅
            integralLocalDerived g (pbcAdicCompletion T (pbcIntegralDatum l E)) U
              ((integralConstantDerived T (pbcIntegralDatum l E)).obj P)) := by
  obtain ⟨d, hd, _⟩ := WeilConjectures.PrincipalKoszulStrictReplacement.coefficient_datum l E
  obtain ⟨c⟩ := integralResidueCoefficientModel_exists l E d hd S
  have hJ : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have : IsAdicComplete d.ideal (Padic.coefficientExtensionIntegers l E) := by
    rw [hd, hJ]
    exact Padic.coefficientIntegers_complete l E
  obtain ⟨⟨ha, hM⟩, hresidue⟩ :=
    integralResidueStratum_input T l E S g d hd c K hcomplete 𝒰 C eC hmodels
  obtain ⟨V, hV, hlocal⟩ := residue_lisse_perfect_lift S d 1
    (fun _ ↦ Padic.coefficientExtensionUniformizer l E) ha
    ((integralResidueStratumPull T l E S g d c).obj K) hM hresidue
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨P, hP, ⟨j⟩⟩ := hlocal U f hf
  obtain ⟨Q, hQ, ⟨i⟩⟩ := integralResidueStratum_constant T l E S g d hd c P hP
  refine ⟨Q, hQ, ?_⟩
  apply sliceCoefficient_reflects S (integralResidueStratumCoefficient T l E S g d c) U
  exact ⟨j ≪≫ (sliceRestrictionIso S (completedAdicRing S d) U i).symm⟩

end AlgebraicGeometry.Scheme
