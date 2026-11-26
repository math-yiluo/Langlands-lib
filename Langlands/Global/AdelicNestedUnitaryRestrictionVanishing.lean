import Langlands.Global.AdelicParabolicConstantTermTransitivity
import Langlands.Global.AdelicWeakConstantTermTransitivity

/-! # Vanishing of an inner exponent component with unitary outer restriction -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Functions" => (AdelicGroupPoints F G → ℂ)
local notation "Param(" J ")" => ComplexCharacterParameter F (fam.P J)

private theorem realPart_eq_zero_of_norm_one (J : Idx) (lam : Param(J))
    (h : ∀ a : fam.positiveSplitComponent J, ‖parameterPower F (fam.P J) lam a‖ = 1) :
    parameterRealPart F (fam.P J) lam = 0 := by
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have := (r.rationalCharacters_free_finite fam.connectedReductive).1
  apply realParameterPairing_left_eq_zero
  intro H
  obtain ⟨a, ha⟩ := (eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J)
    (fam.p J) (fam.l J) (fam.a J) r).1 H
  change characterLog F (fam.P J) a.val = H at ha
  have hn := h a
  rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, ha, Real.exp_eq_one_iff] at hn
  exact hn

/-- When the weak term along `P` vanishes, a normalized exponent of `C_Q f` whose restriction
has unit modulus on the positive split component of `P` has zero component. The input function
may itself belong to any larger parabolic quotient. -/
theorem exponentComponent_eq_zero_of_unitary_restriction {Q P R : Idx} (hQP : Q ≤ P) (hPR : P ≤ R)
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    {f : Functions} (hf : fam.IsAutomorphicOn hsmooth Kinf rho R f)
    {s : Finset (Param(P))} {c : Param(P) → Functions}
    (hP : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho P (fam.constantTerm P f) s c)
    (hw : fam.unitaryExponentSum P s c = 0)
    {v : Finset (Param(Q))} {g : Param(Q) → Functions}
    (hQ : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q f) v g)
    (hDec : ∀ nu ∈ s, ∃ t e,
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q (c nu)) t e)
    {lam : Param(Q)} (hlam : lam ∈ v)
    (hunit : ∀ (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q),
      map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a →
        ‖parameterPower F (fam.P Q) lam b‖ = 1) : g lam = 0 := by
  classical
  have hChoice (nu : Param(P)) : ∃ t e, nu ∈ s →
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q (c nu)) t e := by
    by_cases h : nu ∈ s
    · obtain ⟨t, e, ht⟩ := hDec nu h
      exact ⟨t, e, fun _ => ht⟩
    · exact ⟨∅, 0, fun hn => (h hn).elim⟩
  choose t e hte using hChoice
  have hvan (nu : Param(P)) (hnu : nu ∈ s) (hnt : lam ∈ t nu) : e nu lam = 0 := by
    by_contra hne
    have hrad : fam.IsRadicalInvariant P (c nu) := by
      intro u x
      obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp u.property
      exact (hP.automorphic nu hnu).1 _ (Subgroup.mem_sup_left ⟨w, hw⟩) x
    have hint : fam.HasIntegrableConstantTerm Q (c nu) := fun x =>
      fam.integrable_constantTermIntegrand_of_le P Q hQP (hP.automorphic nu hnu).2.1.1
        (hP.automorphic nu hnu).1 x
    have hReal : parameterRealPart F (fam.P P) nu = 0 := by
      apply fam.realPart_eq_zero_of_norm_one P nu
      intro a
      obtain ⟨b, hab, -⟩ := fam.exists_positiveSplitComponent_lift_with_values hQP a
      have hval := fam.exponent_value_eq_of_constantTerm hQP (hP.exponent nu hnu) hrad hint
        (hte nu hnu).sum_eq (hte nu hnu).exponent hnt hne a b hab
      rw [parameterPower_add, parameterPower_add] at hval
      change parameterPower F (fam.P Q) lam b * fam.halfModulus Q b =
        parameterPower F (fam.P P) nu a * fam.halfModulus P a at hval
      rw [hδ F G fam Q P hQP a b hab] at hval
      have heq := mul_right_cancel₀ (show fam.halfModulus P a ≠ 0 from Complex.exp_ne_zero _) hval
      rw [← heq, hunit a b hab]
    have hc : c nu = 0 := fam.eq_zero_of_sum_eq_zero_of_hasExponent P _ c
      (fun x hx => hP.exponent x (Finset.mem_filter.mp hx).1) hw nu (Finset.mem_filter.mpr ⟨hnu, hReal⟩)
    have hzero : ∑ x ∈ t nu, e nu x = 0 := by
      rw [← (hte nu hnu).sum_eq, hc]
      ext x
      simp [constantTerm, subgroupConstantTerm]
    exact hne (fam.eq_zero_of_sum_eq_zero_of_hasExponent Q (t nu) (e nu)
      (hte nu hnu).exponent hzero lam hnt)
  let u := s.biUnion t
  let E (lam : Param(Q)) : Functions := ∑ nu ∈ s, if lam ∈ t nu then e nu lam else 0
  have htSub (nu : Param(P)) (hnu : nu ∈ s) : t nu ⊆ u := Finset.subset_biUnion_of_mem t hnu
  have hSum : fam.constantTerm Q f = ∑ lam ∈ u, E lam := by
    simp only [E]
    rw [Finset.sum_comm]
    calc
      _ = fam.constantTerm Q (fam.constantTerm P f) :=
        (fam.constantTerm_constantTerm_of_parabolicQuotient hQP hPR hf.2.1.1 hf.1).symm
      _ = ∑ nu ∈ s, fam.constantTerm Q (c nu) := by
        rw [hP.sum_eq]
        funext x
        simp only [constantTerm, subgroupConstantTerm, Finset.sum_apply]
        exact integral_finsetSum s fun nu hnu =>
          fam.integrable_constantTermIntegrand_of_le P Q hQP (hP.automorphic nu hnu).2.1.1
            (hP.automorphic nu hnu).1 x
      _ = _ := by
        apply Finset.sum_congr rfl
        intro nu hnu
        rw [(hte nu hnu).sum_eq, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (htSub nu hnu)]
  have hExp (x : Param(Q)) : fam.HasExponent Q x (E x) := by
    apply (fam.hasExponent_iff Q x _).mpr
    apply fam.hasUnnormalizedExponent_sum Q
    intro nu hnu
    by_cases h : x ∈ t nu
    · simpa only [ite_eq_left h] using (fam.hasExponent_iff Q x _).mp ((hte nu hnu).exponent x h)
    · simpa only [ite_eq_right h] using fam.hasUnnormalizedExponent_zero Q
        (x + halfModulusParameter F (fam.P Q))
  have hE : E lam = 0 := by
    apply Finset.sum_eq_zero
    intro nu hnu
    split_ifs with h
    · exact hvan nu hnu h
    · rfl
  have hFilter := fam.sum_filter_eq_of_hasExponent Q v u g E hQ.exponent (fun x _ => hExp x)
    (hQ.sum_eq.symm.trans hSum) (fun x => x = lam)
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left hlam] at hFilter
  simpa only [hE, ite_self] using hFilter

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- Vanishing of the outer weak term rules out any inner exponent with unitary restriction,
using the half-modulus comparison and finite exponent decompositions on the nested quotients. -/
def AdelicNestedUnitaryRestrictionVanishingStatement : Prop :=
  StandardNestedHalfModulusCompatibilityStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
      (Q P R : StandardIndex F G fam.i fam.ν), Q ≤ P → P ≤ R →
    ∀ (f : AdelicGroupPoints F G → ℂ), fam.IsAutomorphicOn hsmooth Kinf rho R f →
    ∀ (s : Finset (ComplexCharacterParameter F (fam.P P)))
      (c : ComplexCharacterParameter F (fam.P P) → AdelicGroupPoints F G → ℂ),
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho P (fam.constantTerm P f) s c →
      fam.unitaryExponentSum P s c = 0 →
    ∀ (v : Finset (ComplexCharacterParameter F (fam.P Q)))
      (g : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q f) v g →
      (∀ nu ∈ s, ∃ t e,
        fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q (c nu)) t e) →
    ∀ lam ∈ v, (∀ (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q),
      map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a →
        ‖parameterPower F (fam.P Q) lam b‖ = 1) → g lam = 0

theorem adelicNestedUnitaryRestrictionVanishing : AdelicNestedUnitaryRestrictionVanishingStatement := by
  intro hδ F _ _ G _ _ _ fam N d hsmooth Kinf rho Q P R hQP hPR f hf s c hP hw v g hQ hDec lam hlam hunit
  exact fam.exponentComponent_eq_zero_of_unitary_restriction hsmooth Kinf rho hQP hPR
    hδ hf hP hw hQ hDec hlam hunit

end Langlands.Global
