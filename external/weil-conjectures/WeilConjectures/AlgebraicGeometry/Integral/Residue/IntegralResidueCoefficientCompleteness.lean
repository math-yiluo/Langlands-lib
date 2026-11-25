/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicCriterion
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels

/-! # Completeness under normalized integral coefficient restriction

## References

* Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.5.1
* Bhatt--Scholze, Lemma 6.5.8(1) and Definition 6.5.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale WeilConjectures
namespace AlgebraicGeometry.Scheme

private theorem completedComplete_of_iso
    (S : Scheme.{u}) {A : Type u} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    {K L : DerivedCategory (CompletedAdicModules S d)} (e : K ≅ L)
    (hK : IsCompletedAdicDerivedComplete S d r a ha K) :
    IsCompletedAdicDerivedComplete S d r a ha L := by
  obtain ⟨i, hi⟩ := reconstructionKoszulIntrinsicComparison S d r a K
  obtain ⟨j, hj⟩ := reconstructionKoszulIntrinsicComparison S d r a L
  have : IsIso (completedAdicIntrinsicUnit S d r a K) := hK
  have : IsIso ((reconstructionKoszulDerivedUnit S d r a).app K) := by
    have : IsIso ((reconstructionKoszulDerivedUnit S d r a).app K ≫ i.hom) := by
      rw [hi]
      infer_instance
    exact IsIso.of_isIso_comp_right _ i.hom
  have hn := (reconstructionKoszulDerivedUnit S d r a).naturality e.hom
  dsimp only [Functor.id_map] at hn
  have : IsIso ((reconstructionKoszulDerivedUnit S d r a).app L) := by
    have : IsIso (e.hom ≫ (reconstructionKoszulDerivedUnit S d r a).app L) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  change IsIso (completedAdicIntrinsicUnit S d r a L)
  rw [← hj]
  infer_instance

/-- Normalized scalar restriction preserves intrinsic completeness on a fixed scheme. -/
theorem integralResidueCoefficient_complete
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (ha : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal)
    (c : IntegralResidueCoefficientModel l E d S)
    (K : PbcCompletedDerived S (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E) K) :
    IsCompletedAdicDerivedComplete S d 1
      (fun _ ↦ Padic.coefficientExtensionUniformizer l E) ha
      ((pbcDerivedRestrict (purCoefficientIso l E S ≪≫ c.completed.symm).inv).obj K) := by
  let e := (adicLisseForget S).mapIso c.completed
  let C : OpenDvrCoefficientModel l E d S :=
    { finite := c.finite
      finite_constants := c.finite_constants
      finite_transition := c.finite_transition
      completed := c.completed
      completed_projection := c.completed_projection
      modules := WeilConjectures.restrictionEquivalence e
      modules_functor := rfl
      additive := inferInstanceAs (SheafOfModules.restrictScalars e.hom).Additive
      inverse_additive := inferInstanceAs (SheafOfModules.restrictScalars e.inv).Additive }
  let P := (purCoefficientModel l E S).functor.obj K
  have hP : IsDerivedCompleteUnrestricted.{u, u} l E S P :=
    (purCoefficientModel_predicates l E S K).1.mp hK
  have hc := (openDvrIntrinsicCriterion l E d ha S C P).mp hP
  let t := (pbcDerivedRestrictComp c.completed.hom (purCoefficientIso l E S).inv
    (c.completed.hom ≫ (purCoefficientIso l E S).inv) rfl).app K
  apply completedComplete_of_iso S d 1
    (fun _ ↦ Padic.coefficientExtensionUniformizer l E) ha t
  exact hc

end AlgebraicGeometry.Scheme
