import Langlands.Automorphic.AssociatedGammaAutomorphicFamily
import Langlands.Automorphic.AssociatedGammaArithmeticFamily
import Langlands.Automorphic.AssociatedGammaUnramifiedMatch
import Langlands.Automorphic.AssociatedPresentationSpectrum

/-!
# Matching of the two Hecke families at unramified places

At a finite place where the twisted automorphic factor choice is unramified, the Hecke
character is unramified and both relative Weil representations are unramified and match the
Satake parameters of the presentations, the automorphic and arithmetic local L-factors of the
two Hecke Euler families coincide.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- Evaluation of the reciprocal of a polynomial, totalized at its zeros. -/
theorem eval_inv_algebraMap_total (P : ℂ[X]) (x : ℂ) :
    RatFunc.eval (RingHom.id ℂ) x ((algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) = (P.eval x)⁻¹ := by
  have h0 : RatFunc.eval (RingHom.id ℂ) x (algebraMap ℂ[X] (RatFunc ℂ) P) = P.eval x := by
    rw [RatFunc.eval_algebraMap]
    simp
  by_cases hx : P.eval x = 0
  · rw [hx, inv_zero]
    by_contra h
    by_cases hP : P = 0
    · subst hP
      simp at h
    · have hreg := RankinSelberg.RationalEvaluation.RegularAt.of_eval_ne_zero h
      have hm := RankinSelberg.RationalEvaluation.eval_mul hreg
        (RankinSelberg.RationalEvaluation.RegularAt.polynomial (z := x) P)
      have hne : algebraMap ℂ[X] (RatFunc ℂ) P ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).mpr hP
      rw [inv_mul_cancel₀ hne, h0, hx, mul_zero] at hm
      simp at hm
  · rw [RankinSelberg.RationalEvaluation.eval_inv (by rw [h0]; exact hx), h0]

/-- Images of a product multiset. -/
theorem map_product_map {α β γ δ : Type*} (s : Multiset α) (t : Multiset β) (f : α → γ)
    (g : β → δ) : s.map f ×ˢ t.map g = (s ×ˢ t).map (Prod.map f g) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.cons_product, Multiset.cons_product, Multiset.map_add, ih,
      Multiset.map_map, Multiset.map_map]
    rfl

/-- The pair Euler polynomial with a scaled first spectrum, as a product over complex
numbers. -/
theorem pairEulerPolynomial_scale {n m : ℕ} (a : ℂˣ) (x : Unramified.Eigenvalues n)
    (y : Unramified.Eigenvalues m) :
    pairEulerPolynomial (Unramified.Eigenvalues.scale a x) y =
      (((((x : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ))).map ((a : ℂ) * ·)) ×ˢ
        ((y : Multiset ℂˣ).map fun z : ℂˣ => (z : ℂ))).map
          fun p : ℂ × ℂ => 1 - C (p.1 * p.2) * X).prod := by
  unfold pairEulerPolynomial Unramified.Eigenvalues.scale
  rw [Sym.coe_map]
  have h1 : ((x : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ))).map ((a : ℂ) * ·) =
      ((x : Multiset ℂˣ).map (fun z => a * z)).map (fun z : ℂˣ => (z : ℂ)) := by
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun z _ => by simp
  rw [h1, map_product_map, Multiset.map_map]
  rfl

/-- An Euler polynomial of eigenvalues as a product over complex numbers. -/
theorem eigenvalues_eulerPolynomial_eq {n : ℕ} (x : Unramified.Eigenvalues n) :
    x.eulerPolynomial = ((((x : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ)))).map
      fun r => 1 - C r * X).prod := by
  rw [Unramified.Eigenvalues.eulerPolynomial, Multiset.map_map]
  rfl

/-- The arithmetic pair L-factor of a twisted unramified pair is the reciprocal of the pair
Euler polynomial of the twisted Satake parameters of matching presentations. -/
theorem arithmeticPairLFactor_eq_pairEulerPolynomial [CompactSpace (AdeleQuotient F)]
    {r t : ℕ} {T₀ : Automorphic.CuspidalOperatorRealization F r}
    {T₀' : Automorphic.CuspidalOperatorRealization F t}
    (Q : Automorphic.CuspidalSpectralPresentation.{u, uQ} T₀)
    (Q' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T₀')
    {S₀ S₀' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)} {z : FinitePlace F}
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) (hχz : χ.IsUnramifiedAt z)
    (hz : z ∉ Q.exceptional) (hzχ : z ∉ (Q.heckeDeterminantTwist χ).exceptional)
    (hz' : z ∉ Q'.exceptional)
    (hS : IsUnramifiedMatchAt S₀ z (Q.spectralSystem.eulerPolynomial z hz))
    (hS' : IsUnramifiedMatchAt S₀' z (Q'.spectralSystem.eulerPolynomial z hz')) :
    Correspondence.arithmeticPairLFactor (padicField z)
        (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S₀) ι)
        (localPairClass S₀' ι) =
      (algebraMap ℂ[X] (RatFunc ℂ) (pairEulerPolynomial
        ((Q.heckeDeterminantTwist χ).spectralSystem.eigenvalues z hzχ)
        (Q'.spectralSystem.eigenvalues z hz')))⁻¹ := by
  obtain ⟨hSu, hSe⟩ := (hS w).2 e ι hι
  obtain ⟨hSu', hSe'⟩ := (hS' w).2 e ι hι
  have hSe2 := hSe.trans (eigenvalues_eulerPolynomial_eq (Q.spectralSystem.eigenvalues z hz))
  have hSe2' := hSe'.trans (eigenvalues_eulerPolynomial_eq (Q'.spectralSystem.eigenvalues z hz'))
  rw [arithmeticPairLFactor_twist_of_unramified hι eC heC χ hχz hSu hSu' _ _ hSe2 hSe2']
  congr 2
  exact (pairEulerPolynomial_scale _ _ _).symm

/-- **Unramified matching of L-factors** of the automorphic and arithmetic families. -/
theorem lFactor_eq_of_unramified {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (arch : NumberField.InfinitePlace F → LocalFactors) (χ : HeckeCharacter F)
    (Sχ : Finset (FinitePlace F)) (hU : (D.twistedChoice χ).IsUnramifiedOutside Sχ)
    (z : FinitePlace F) (hz : z ∉ Sχ) (hzP : z ∉ D.P.exceptional)
    (hzχ : z ∉ (D.P.heckeDeterminantTwist χ).exceptional) (hzP' : z ∉ D.P'.exceptional)
    (hχz : χ.IsUnramifiedAt z)
    (hS : IsUnramifiedMatchAt S z (D.P.spectralSystem.eulerPolynomial z hzP))
    (hS' : IsUnramifiedMatchAt S' z (D.P'.spectralSystem.eulerPolynomial z hzP'))
    (s : ℂ) :
    (D.localFactors χ (.inr z)).lFactor s = (A.localFactors arch χ (.inr z)).lFactor s := by
  change ((D.finiteData χ z).1.eval (RankinSelberg.spectralPoint (residueCardinality z) s))⁻¹ =
    (A.finiteFactors χ z).lFactor s
  have hpoly : (D.finiteData χ z).1 = pairEulerPolynomial
      ((D.P.heckeDeterminantTwist χ).spectralSystem.eigenvalues z hzχ)
      (D.P'.spectralSystem.eigenvalues z hzP') := (hU z hz).1 hzχ hzP'
  rw [(A.finiteFactors_spec hEps χ z).1 s, arithmeticPairLFactor_eq_pairEulerPolynomial D.P D.P'
    (A.localMap_spec z) (A.family z) (A.system_spec z).1 χ hχz hzP hzχ hzP' hS hS',
    eval_inv_algebraMap_total, hpoly]

/-- The dual of a twist is the twist of the dual by the inverse character, on local classes. -/
theorem localPairClass_twist_dual_eq
    (S₀ : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {z : FinitePlace F}
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (η : RelativeWeilGroup c F E →* ℂˣ) :
    localPairClass (FiniteRepresentation.twist η S₀).dual ι =
      localPairClass (FiniteRepresentation.twist η⁻¹ S₀.dual) ι := by
  let e : FiniteRepresentation.Equiv (localComponent (FiniteRepresentation.twist η S₀).dual ι)
      (localComponent (FiniteRepresentation.twist η⁻¹ S₀.dual) ι) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      change (Langlands.twist η S₀.representation ((ι g)⁻¹)).dualMap =
        Langlands.twist η⁻¹ S₀.representation.dual (ι g)
      ext l x
      change l (((η (ι g)⁻¹ : ℂˣ) : ℂ) • S₀.representation (ι g)⁻¹ x) =
        ((η⁻¹ (ι g) : ℂˣ) : ℂ) • l (S₀.representation (ι g)⁻¹ x)
      rw [map_smul, map_inv, MonoidHom.inv_apply])
  apply Quotient.sound
  exact ⟨WeilDeligneRepresentation.Equiv.ofIso
    ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
      (FiniteRepresentation.isoOfEquiv e))⟩

/-- The inverse of a Hecke character is unramified where the character is. -/
theorem _root_.Langlands.Global.HeckeCharacter.isUnramifiedAt_inv {χ : HeckeCharacter F}
    {z : FinitePlace F} (h : χ.IsUnramifiedAt z) : χ⁻¹.IsUnramifiedAt z := fun a ha => by
  change (χ.finiteComponent z a)⁻¹ = 1
  rw [h a ha, inv_one]

/-- **Unramified matching of dual L-factors** of the automorphic and arithmetic families. -/
theorem dualLFactor_eq_of_unramified
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (arch : NumberField.InfinitePlace F → LocalFactors) (χ : HeckeCharacter F)
    (Sχ : Finset (FinitePlace F)) (hU : (D.twistedChoice χ).IsUnramifiedOutside Sχ)
    (z : FinitePlace F) (hz : z ∉ Sχ) (hzP : z ∉ D.Pd.exceptional)
    (hzχ : z ∉ (D.Pd.heckeDeterminantTwist χ⁻¹).exceptional) (hzP' : z ∉ D.Pd'.exceptional)
    (hχz : χ.IsUnramifiedAt z)
    (hS : IsUnramifiedMatchAt S.dual z (D.Pd.spectralSystem.eulerPolynomial z hzP))
    (hS' : IsUnramifiedMatchAt S'.dual z (D.Pd'.spectralSystem.eulerPolynomial z hzP'))
    (s : ℂ) :
    (D.localFactors χ (.inr z)).dualLFactor s =
      (A.localFactors arch χ (.inr z)).dualLFactor s := by
  change ((D.finiteData χ z).2.1.eval
    (RankinSelberg.spectralPoint (residueCardinality z) s))⁻¹ =
    (A.finiteFactors χ z).dualLFactor s
  have hpoly : (D.finiteData χ z).2.1 = pairEulerPolynomial
      ((D.Pd.heckeDeterminantTwist χ⁻¹).spectralSystem.eigenvalues z hzχ)
      (D.Pd'.spectralSystem.eigenvalues z hzP') := (hU z hz).2.1 hzχ hzP'
  have hcls : localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual
      (A.localMap z) = localPairClass
        (FiniteRepresentation.twist (reciprocityCharacter c F E χ⁻¹) S.dual) (A.localMap z) := by
    rw [localPairClass_twist_dual_eq]
    exact localPairClass_twist_congr _ _ fun g => by
      rw [MonoidHom.inv_apply, reciprocityCharacter_apply, reciprocityCharacter_apply]
      rfl
  rw [(A.finiteFactors_spec hEps χ z).2.1 s, hcls, arithmeticPairLFactor_eq_pairEulerPolynomial
    D.Pd D.Pd' (A.localMap_spec z) (A.family z) (A.system_spec z).1 χ⁻¹
    (HeckeCharacter.isUnramifiedAt_inv hχz) hzP hzχ hzP' hS hS',
    eval_inv_algebraMap_total, hpoly]

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
