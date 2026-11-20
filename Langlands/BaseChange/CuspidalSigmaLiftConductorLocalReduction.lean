import Langlands.BaseChange.CuspidalSigmaLiftConductorStatement
import Langlands.AllField.Representation.RankinSelberg.LocalConverseStatement
import Langlands.AllField.HarmonicAnalysis.Conductor
import Langlands.Representation.RankinSelberg.LocalFactor

/-!
# Local reduction of the cuspidal sigma-lift conductor formula

Compare the exponents of the pair epsilon factors against the trivial character,
and use them to reduce the sigma-lift formula to local factor identities.
-/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open RankinSelberg (epsilonMonomial rankOneCharacter spectralPoint spectralPoint_ne_zero)
open scoped BigOperators

universe u v uV uW

/-- A finite product of epsilon monomials equals a single epsilon monomial up to a
constant unit. Allowing a unit keeps this comparison independent of the constant
normalizations in the local epsilon identity. -/
def EpsilonMonomialProductComparison {ι : Type*} (qF qE : ℕ) (X : Finset ι)
    (eF : ι → ℂˣ × ℤ) (eE : ℂˣ × ℤ) : Prop :=
  ∃ c : ℂˣ, ∀ z : ℂ,
    ∏ i ∈ X, epsilonMonomial qF (eF i).1 (eF i).2 z =
      (c : ℂ) * epsilonMonomial qE eE.1 eE.2 z

private theorem epsilonMonomial_prod {ι : Type*} (X : Finset ι) (e : ι → ℂˣ × ℤ)
    {q : ℕ} (hq : 1 < q) (z : ℂ) :
    ∏ i ∈ X, epsilonMonomial q (e i).1 (e i).2 z =
      epsilonMonomial q (∏ i ∈ X, (e i).1) (∑ i ∈ X, (e i).2) z := by
  classical
  induction X using Finset.induction_on with
  | empty => simp [epsilonMonomial]
  | @insert i X hi ih =>
    rw [Finset.prod_insert hi, ih, Finset.prod_insert hi, Finset.sum_insert hi]
    simp only [epsilonMonomial, Units.val_mul, zpow_add₀ (spectralPoint_ne_zero hq z)]
    ring

/-- The comparison of epsilon monomials gives the comparison of their integer
exponents. Comparing at zero cancels the unit coefficients, and comparing at one
uses `qE = qF ^ f`. -/
theorem EpsilonMonomialProductComparison.sum_eq {ι : Type*} {qF qE f : ℕ}
    {X : Finset ι} {eF : ι → ℂˣ × ℤ} {eE : ℂˣ × ℤ}
    (hqF : 1 < qF) (hq : qE = qF ^ f)
    (h : EpsilonMonomialProductComparison qF qE X eF eE) :
    ∑ i ∈ X, (eF i).2 = (f : ℤ) * eE.2 := by
  obtain ⟨c, hc⟩ := h
  have hzero : (↑(∏ i ∈ X, (eF i).1) : ℂ) = (c : ℂ) * (eE.1 : ℂ) := by
    simpa [epsilonMonomial, spectralPoint] using
      (epsilonMonomial_prod X eF hqF 0).symm.trans (hc 0)
  have hone := (epsilonMonomial_prod X eF hqF 1).symm.trans (hc 1)
  unfold epsilonMonomial at hone
  rw [← mul_assoc, ← hzero] at hone
  have hp := mul_left_cancel₀ (∏ i ∈ X, (eF i).1).ne_zero hone
  simp only [spectralPoint, Complex.cpow_neg_one, inv_zpow] at hp
  have hpow := inv_injective hp
  simp only [hq, Nat.cast_pow] at hpow
  rw [← zpow_natCast (qF : ℂ) f, ← zpow_mul] at hpow
  have hr : (qF : ℝ) ^ (∑ i ∈ X, (eF i).2) = (qF : ℝ) ^ ((f : ℤ) * eE.2) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast] using hpow
  have hqR : (1 : ℝ) < qF := by exact_mod_cast hqF
  exact zpow_right_injective₀ (zero_lt_one.trans hqR) hqR.ne' hr

section LocalFactors

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E]

/-- The additive characters have the trace relation and the indicated conductors
in the convention of the actual valuation lattices. -/
def TraceEpsilonCharacterCondition
    (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E) (d : ℕ) : Prop :=
  (∀ x : E, ψE x = ψF (Algebra.trace F E x)) ∧
    (LocalFieldData.ofInstances F).additiveConductor ψF = 0 ∧
    (LocalFieldData.ofInstances E).additiveConductor ψE = (d : ℤ)

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The Library pair epsilon factor against the trivial character of `GL₁`. -/
abbrev IsEpsilonFactorAgainstTrivialCharacter (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F; AdditiveHaarMeasure F)
    (ρ : Representation ℂ (GeneralLinear (r + 1) F) V) (e : ℂˣ × ℤ) : Prop :=
  AllField.RankinSelberg.IsPadicPairEpsilonFactor F ψ ν (n := 0) ρ
    (rankOneCharacter (1 : Fˣ →* ℂˣ)) e

/-- A finite fixed-level conductor and its exponent formula for the actual pair
epsilon factor against the trivial character. -/
def IsStandardEpsilonConductor (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F; AdditiveHaarMeasure F)
    (ρ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (a : ℕ) (e : ℂˣ × ℤ) : Prop :=
  IsEpsilonFactorAgainstTrivialCharacter ψ ν ρ e ∧ Conductor.IsNewvectorConductor ρ a ∧
    e.2 = (a : ℤ) + ((r + 1 : ℕ) : ℤ) * (LocalFieldData.ofInstances F).additiveConductor ψ

/-- The factor of the lifted representation is the product of the orbit block
factors, with all factors taken against the trivial character. -/
def OrbitProductEpsilonMultiplicativity (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F; AdditiveHaarMeasure F)
    (ρ : Representation ℂ (GeneralLinear (r + 1) F) V) {s : ℕ}
    (eOrbit : Fin s → ℂˣ × ℤ) (e : ℂˣ × ℤ) : Prop :=
  IsEpsilonFactorAgainstTrivialCharacter ψ ν ρ e ∧
    ∀ z : ℂ,
      ∏ i : Fin s, epsilonMonomial (LocalFieldData.ofInstances F).residueCardinality
          (eOrbit i).1 (eOrbit i).2 z =
        epsilonMonomial (LocalFieldData.ofInstances F).residueCardinality e.1 e.2 z

end LocalFactors

private theorem firstFixedLevel_eq_of_isNewvectorConductor
    {F : Type u} [Field F] [ValuativeRel F] {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear (r + 1) F) V} {a : ℕ}
    (ha : Conductor.IsNewvectorConductor ρ a) :
    Conductor.firstFixedLevel ρ = (a : WithTop ℕ) := by
  have h : Conductor.HasNewvectorLevel ρ := ⟨a, ha.1⟩
  rw [Conductor.firstFixedLevel_of_hasNewvectorLevel ρ h,
    (Conductor.newvectorConductor_eq_iff ρ h a).mpr ha]

/-- The local factor data needed at the extension in the cuspidal conductor
formula. Each orbit block has the same finite newvector conductor as `P₁`. -/
def CuspidalSigmaLiftLocalEpsilonDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (k : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), GeneralLinear.IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      GeneralLinear.IsSupercuspidal P₁ → P₁.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W)
      (hP : IsAdmissible P),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (A : SigmaIntertwiner σ (k + 1) P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_t2Space E (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (k + 1)
       IsSigmaLift σ l π hπ P hP A c) →
    ∀ f d : ℕ, IsResidueDegree F E f → IsDifferentExponent F E d →
    ∀ X : Finset (Fˣ →* ℂˣ), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
      ∃ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
        (νF : letI := borel F; AdditiveHaarMeasure F)
        (νE : letI := borel E; AdditiveHaarMeasure E)
        (aF : (Fˣ →* ℂˣ) → ℕ) (a₁ : ℕ)
        (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
        TraceEpsilonCharacterCondition ψF ψE d ∧
        (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF
          (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
        Conductor.IsNewvectorConductor P₁ a₁ ∧
        (∀ i : Fin s, IsStandardEpsilonConductor ψE νE
          (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) a₁ (eOrbit i)) ∧
        OrbitProductEpsilonMultiplicativity ψE νE P eOrbit eP ∧
        EpsilonMonomialProductComparison (LocalFieldData.ofInstances F).residueCardinality
          (LocalFieldData.ofInstances E).residueCardinality X eF eP

/-- The local epsilon-factor data imply the exact Library conductor formula. -/
def CuspidalSigmaLiftConductorFromLocalEpsilonStatement : Prop :=
  CuspidalSigmaLiftLocalEpsilonDataStatement.{u, v, uV, uW} →
    CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromLocalEpsilon :
    CuspidalSigmaLiftConductorFromLocalEpsilonStatement.{u, v, uV, uW} := by
  intro hdata F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k V _ _ π hπ hsuper hπirr
    s k₁ hrank W₁ _ _ P₁ hP₁super hP₁irr W _ _ P hP horbit A c hlift f d hf hd X hX
  obtain ⟨ψF, ψE, νF, νE, aF, a₁, eF, eOrbit, eP,
    hψ, hF, ha₁, hOrbit, hprod, hcomp⟩ :=
    hdata F E σ l hcyc k V π hπ hsuper hπirr s k₁ hrank W₁ P₁ hP₁super hP₁irr
      W P hP horbit A c hlift f d hf hd X hX
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  have hq : TE.residueCardinality = TF.residueCardinality ^ f := hf
  have hsum := EpsilonMonomialProductComparison.sum_eq TF.residueCardinality_gt_one hq hcomp
  have hOrbitProd : EpsilonMonomialProductComparison TE.residueCardinality
      TE.residueCardinality Finset.univ eOrbit eP :=
    ⟨1, fun z => by simpa using hprod.2 z⟩
  have hOrbitSum := EpsilonMonomialProductComparison.sum_eq TE.residueCardinality_gt_one
    (pow_one TE.residueCardinality).symm hOrbitProd
  have heF (κ) (hκ : κ ∈ X) : (eF κ).2 = (aF κ : ℤ) := by
    simpa [hψ.2.1] using (hF κ hκ).2.2
  have heOrbit (i : Fin s) : (eOrbit i).2 = (a₁ : ℤ) + (k₁ + 1) * (d : ℤ) := by
    simpa [hψ.2.2] using (hOrbit i).2.2
  have hrankInt : (s : ℤ) * (k₁ + 1) = k + 1 := by exact_mod_cast hrank
  have heP : eP.2 = (s : ℤ) * a₁ + (k + 1) * (d : ℤ) := by
    calc
      eP.2 = ∑ i : Fin s, (eOrbit i).2 := by simpa using hOrbitSum.symm
      _ = ∑ _ : Fin s, ((a₁ : ℤ) + (k₁ + 1) * (d : ℤ)) :=
        Finset.sum_congr rfl (fun i _ => heOrbit i)
      _ = (s : ℤ) * a₁ + (k + 1) * (d : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_add, ← mul_assoc, hrankInt]
  have hnat : ∑ κ ∈ X, aF κ = f * (s * a₁ + (k + 1) * d) := by
    have hsumF : ∑ κ ∈ X, (eF κ).2 = ∑ κ ∈ X, (aF κ : ℤ) :=
      Finset.sum_congr rfl heF
    rw [hsumF, heP] at hsum
    exact_mod_cast hsum
  calc
    (∑ κ ∈ X, Conductor.firstFixedLevel (twist (κ.comp GeneralLinear.determinant) π)) =
        ∑ κ ∈ X, (aF κ : WithTop ℕ) :=
      Finset.sum_congr rfl (fun κ hκ => firstFixedLevel_eq_of_isNewvectorConductor (hF κ hκ).2.1)
    _ = (f : WithTop ℕ) * ((s : WithTop ℕ) * Conductor.firstFixedLevel P₁ +
          ((k + 1 : ℕ) : WithTop ℕ) * (d : WithTop ℕ)) := by
      rw [firstFixedLevel_eq_of_isNewvectorConductor ha₁]
      exact_mod_cast hnat

end Langlands.BaseChange
