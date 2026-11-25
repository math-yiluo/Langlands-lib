/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.Integral.IntegralChartPullbackComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CechPerfectModelCompleteness

/-! # Completeness of a single perfect integral chart

## References

* Bhatt--Scholze, Proposition 6.6.11, reverse implication
* Bhatt--Scholze, Lemma 6.5.8(1), (2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- A perfect integral model on one pro-etale chart is intrinsically complete there. -/
theorem integralPerfectChart_complete
    (T : Scheme.{u}) [IsNoetherian T] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S : Scheme.{u}} (g : S ⟶ T) [IsImmersion g] (U : S.ProEt)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (P : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (hP : @DerivedCategory.IsPerfectRingComplex (PbcIntegralRing l E) _
      (HasDerivedCategory.standard _) P)
    (e : Nonempty (integralLocalDerived g (pbcAdicCompletion T (pbcIntegralDatum l E)) U K ≅
      integralLocalDerived g (pbcAdicCompletion T (pbcIntegralDatum l E)) U
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj P)))
    (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (C : CochainComplex (pbcModules U.left
      (pbcAdicCompletion U.left (pbcIntegralDatum l E))) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ ((pbcIntegralDatum l E).pull (U.hom ≫ g)).obj K) :
    IsDerivedCompleteIntrinsic U.left (pbcIntegralDatum l E) r a ha
      (((pbcIntegralDatum l E).pull (U.hom ≫ g)).obj K) C eC := by
  let d := pbcIntegralDatum l E
  let : IsNoetherianRing (PbcIntegralRing l E) := d.noetherian
  let L := (integralConstantDerived T d).obj P
  let D := DerivedCategory.Q.objPreimage L
  let eD := DerivedCategory.Q.objObjPreimageIso L
  have hL := cechPerfectModel_intrinsicComplete T d P hP r a ha D eD
  obtain ⟨e⟩ := e
  obtain ⟨χ⟩ := integralLocalDerived_pullbackIso d g U K L e
  have hf : IsAdicStratumRestriction (U.hom ≫ g) :=
    Or.inr (Or.inr (Or.inl ⟨S, g, U.hom, inferInstance, inferInstance, rfl⟩))
  have h := stratumIntrinsicComplete_preserved d (U.hom ≫ g) hf r a ha L D eD C
    (eC ≪≫ χ) hL
  change IsIso (intrinsicCompletionUnit U.left d r a ha _ C eC)
  change IsIso ((χ.inv ≫ eC.inv) ≫
    DerivedCategory.Q.map (intrinsicCompletionComplexUnit U.left d r a C)) at h
  rw [Category.assoc] at h
  exact (isIso_comp_left_iff χ.inv _).mp h

end AlgebraicGeometry.Scheme
