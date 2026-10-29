import Langlands.Representation.RankinSelberg.InducedTailDirectAssembly
import Langlands.Representation.RankinSelberg.InducedTailConditionalAssemblyStatement
import Langlands.Representation.Induction.HeterogeneousConstruction
import Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.RankinSelberg.LanglandsLFactor
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.HarmonicAnalysis.UnboundedConductorProof

/-!
# Conditional ramified-enlargement assembly

Proof of the six-input conditional assembly interface. The analytic
span, full-type, existence, associativity, opposite-divisibility and ramified
vanishing prerequisites remain explicit conditional inputs.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV₁ uV₂ uW u

/-- Reduce the unchanged heterogeneous parent to a carrier universe closed
under canonical normalized induction. -/
theorem inducedTailLFactor_of_commonUniverse
    (hCommon :
      InducedTailLFactorStatement.{uF, max uF uV₁ uV₂ uW,
        max uF uV₁ uV₂ uW, max uF uV₁ uV₂ uW}) :
    InducedTailLFactorStatement.{uF, uV₁, uV₂, uW} := by
  intro p hp F ψ ν a b t V₁ _ _ V₂ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ
  let := F.canonicalTopologicalData.topology
  let τ₁ := universeLiftRepresentation.{max uF uV₁ uV₂ uW} π₁
  let τ₂ := universeLiftRepresentation.{max uF uV₁ uV₂ uW} π₂
  let τσ := universeLiftRepresentation.{max uF uV₁ uV₂ uW} σ
  have e₁ := universeLiftEquiv.{max uF uV₁ uV₂ uW} π₁
  have e₂ := universeLiftEquiv.{max uF uV₁ uV₂ uW} π₂
  have eσ := universeLiftEquiv.{max uF uV₁ uV₂ uW} σ
  obtain ⟨Pfull, Ptail, hfull, htail, hdiv⟩ :=
    hCommon p F ψ ν a b t τ₁ τ₂ τσ
      (hπ₁.of_equiv e₁) (hπ₂.of_equiv e₂) (hσ.of_equiv eσ)
  change IsPadicSymmetricLPolynomial F ψ ν.val
    (F.heterogeneousPair (Nat.succ_pos a) (Nat.succ_pos b) τ₁ τ₂) τσ Pfull at hfull
  let eFull :=
    (F.heterogeneousPairToPairEquiv (Nat.succ_pos a) (Nat.succ_pos b) e₁ e₂).trans
      (F.heterogeneousPairToPairEquiv (Nat.succ_pos a) (Nat.succ_pos b)
        (Representation.Equiv.refl τ₁) (Representation.Equiv.refl τ₂)).symm
  refine ⟨Pfull, Ptail, ?_, ?_, hdiv⟩
  · exact (IsPadicSymmetricLPolynomial.congr_equiv eFull eσ).mpr hfull
  · exact (IsPadicSymmetricLPolynomial.congr_equiv e₂ eσ).mpr htail

namespace InducedTailRamifiedAssembly

private abbrev pairIndices (a b : ℕ) : Fin 2 → ℕ := ![a, b]

private theorem pairSum (a b : ℕ) :
    ∑ i, (pairIndices a b i + 1) = (a + 1 + b) + 1 := by
  simp only [pairIndices, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

private def successorPairFamily
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {a b : ℕ} {V₁ V₂ : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (i : Fin 2) :
    Representation ℂ (Langlands.GeneralLinear (pairIndices a b i + 1) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i) :=
  match i with
  | 0 => π₁
  | 1 => π₂

/-- The successor-indexed family of the finite-block interfaces and the
literal two-block family define equivalent actual inductions. -/
private def successorPairInducedEquiv
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    {a b : ℕ} {V₁ V₂ : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂) :
    letI := F.canonicalTopologicalData.topology
    Representation.Equiv
      (F.canonicalNormalizedProductInduced
        (succBlockShape (pairIndices a b) (pairSum a b)) (successorPairFamily π₁ π₂))
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂)) := by
  let D := Σ s : {s : Fin 2 → ℕ //
      (∀ i, 0 < s i) ∧ ∑ i, s i = (a + 1 + b) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i)
  let d₀ : D := ⟨⟨fun i => pairIndices a b i + 1,
    ⟨fun i => Nat.succ_pos _, pairSum a b⟩⟩, successorPairFamily π₁ π₂⟩
  let d₁ : D := ⟨⟨![a + 1, b + 1],
    ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
      by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega⟩⟩,
    Shahidi.pairFamily π₁ π₂⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let predicate : D → Prop := fun d =>
    Nonempty (Representation.Equiv
      (F.canonicalNormalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂)))
  have h : predicate d₀ := by
    rw [hd]
    exact ⟨Representation.Equiv.refl _⟩
  exact Classical.choice h

private theorem heterogeneousPair_whittakerType
    (htype : NormalizedProductWhittakerTypeStatement.{uF, u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {a b : ℕ} {V₁ V₂ : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (hπ₁ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) :
    letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType (a + 1 + b) (standardCharacter ψ (a + 1 + b))
      (F.heterogeneousPair (Nat.succ_pos a) (Nat.succ_pos b) π₁ π₂) := by
  let := F.canonicalTopologicalData.topology
  have hfam : ∀ i, IsOfWhittakerType (pairIndices a b i)
      (standardCharacter ψ (pairIndices a b i)) (successorPairFamily π₁ π₂ i) := by
    intro i
    fin_cases i
    · exact hπ₁
    · exact hπ₂
  have h := htype p F ψ (a + 1 + b) 2 (pairIndices a b) (pairSum a b)
    (successorPairFamily π₁ π₂) hfam
  exact h.of_equiv ((successorPairInducedEquiv F π₁ π₂).trans
    (F.heterogeneousPairToPairEquiv (Nat.succ_pos a) (Nat.succ_pos b)
      (Representation.Equiv.refl π₁) (Representation.Equiv.refl π₂)).symm)

private theorem symmetricLPolynomial_swap
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V : Type uV₁} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P ↔
      IsPadicSymmetricLPolynomial F ψ ν.val σ π P := by
  rcases lt_trichotomy r t with h | h | h
  · exact (isPadicSymmetricLPolynomial_of_lt h).trans
      (isPadicSymmetricLPolynomial_of_le h.le).symm
  · subst t
    exact (isPadicSymmetricLPolynomial_of_le le_rfl).trans
      ((isPadicPairLPolynomial_swap_equalRank F ψ ν.val π σ P).trans
        (isPadicSymmetricLPolynomial_of_le le_rfl).symm)
  · exact (isPadicSymmetricLPolynomial_of_le h.le).trans
      (isPadicSymmetricLPolynomial_of_lt h).symm

private theorem heterogeneousPair_oppositeDivisibility
    (hopp : TwoBlockLFactorMultiplicativityStatement.{uF, u, u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {a b t : ℕ} {V₁ V₂ W : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hπ₁ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ)
    (P P₁ P₂ : ℂ[X])
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (F.heterogeneousPair (Nat.succ_pos a) (Nat.succ_pos b) π₁ π₂) σ P)
    (hP₁ : IsPadicSymmetricLPolynomial F ψ ν.val π₁ σ P₁)
    (hP₂ : IsPadicSymmetricLPolynomial F ψ ν.val π₂ σ P₂) :
    ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * (P₁ * P₂) = Q * P := by
  let := F.canonicalTopologicalData.topology
  have hfam : ∀ i, IsOfWhittakerType (pairIndices a b i)
      (standardCharacter ψ (pairIndices a b i)) (successorPairFamily π₁ π₂ i) := by
    intro i
    fin_cases i
    · exact hπ₁
    · exact hπ₂
  obtain ⟨P', Pi, hP', hPi, Q, e, hrel⟩ :=
    hopp p F ψ ν t (a + 1 + b) (pairIndices a b) (pairSum a b)
      σ (successorPairFamily π₁ π₂) hσ hfam
  have eFull := (successorPairInducedEquiv F π₁ π₂).trans
    (F.heterogeneousPairToPairEquiv (Nat.succ_pos a) (Nat.succ_pos b)
      (Representation.Equiv.refl π₁) (Representation.Equiv.refl π₂)).symm
  have hP'full := (IsPadicSymmetricLPolynomial.congr_equiv
    (Representation.Equiv.refl σ) eFull).mp hP'
  have hP'eq : P' = P :=
    ((symmetricLPolynomial_swap F ψ ν _ σ P').mpr hP'full).unique hP
  have hPi₀ : Pi 0 = P₁ :=
    ((symmetricLPolynomial_swap F ψ ν π₁ σ (Pi 0)).mpr (hPi 0)).unique hP₁
  have hPi₁ : Pi 1 = P₂ :=
    ((symmetricLPolynomial_swap F ψ ν π₂ σ (Pi 1)).mpr (hPi 1)).unique hP₂
  refine ⟨Q, e, ?_⟩
  simpa only [Fin.prod_univ_two, hPi₀, hPi₁, hP'eq] using hrel

private theorem symmetricLPolynomial_rankCast
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r s t : ℕ} (h : r = s) {V : Type uV₁} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (s + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν.val
      (π.comp (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (congrArg (· + 1) h))).toMonoidHom) σ P ↔
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P := by
  subst s
  have hπ : π.comp (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (congrArg (· + 1) (rfl : r = r)))).toMonoidHom = π := by
    apply MonoidHom.ext
    intro g
    have hg : GeneralLinear.reindex (R := F.Carrier)
        (finCongr (congrArg (· + 1) (rfl : r = r))) g = g := by
      apply Units.ext
      ext i j
      rfl
    exact congrArg π hg
  rw [hπ]

private theorem ramifiedCharacter_exists
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {t : ℕ} {W : Type u} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) :
    ∃ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      IsPadicSymmetricLPolynomial F ψ ν.val
        (universeLiftRepresentation.{u} (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))) σ 1 := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨A, hA⟩ := hram p F ψ ν 0 t (rankOneCharacter 1) σ
    (rankOneWhittakerType p F ψ 1) hσ
  obtain ⟨χ, hχ⟩ := padicQuasicharacterUnboundedConductor p F A
  have htwist : Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
      (rankOneCharacter 1) = rankOneCharacter (χ : F.Carrierˣ →* ℂˣ) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (χ (determinant g) : ℂ) * (1 * v) = (χ (determinant g) : ℂ) * v
    rw [one_mul]
  have hcert := hA χ hχ
  rw [htwist] at hcert
  exact ⟨χ, (IsPadicSymmetricLPolynomial.congr_equiv
    (universeLiftEquiv.{u} _) (Representation.Equiv.refl σ)).mp hcert⟩

set_option maxHeartbeats 800000 in
private theorem heterogeneousPair_assoc
    (hassoc : Parabolic.ThreeBlockInductionAssociativityStatement.{
      uF, max uF u, max uF u, max uF u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    {C A B : ℕ} (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
    {U₀ U₁ U₂ : Type (max uF u)}
    [AddCommGroup U₀] [Module ℂ U₀]
    [AddCommGroup U₁] [Module ℂ U₁]
    [AddCommGroup U₂] [Module ℂ U₂]
    (ρ₀ : Representation ℂ (Langlands.GeneralLinear C F.Carrier) U₀)
    (ρ₁ : Representation ℂ (Langlands.GeneralLinear A F.Carrier) U₁)
    (ρ₂ : Representation ℂ (Langlands.GeneralLinear B F.Carrier) U₂)
    (hρ₀ : letI := F.canonicalTopologicalData.topology; IsSmooth ρ₀)
    (hρ₁ : letI := F.canonicalTopologicalData.topology; IsSmooth ρ₁)
    (hρ₂ : letI := F.canonicalTopologicalData.topology; IsSmooth ρ₂) :
    letI := F.canonicalTopologicalData.topology
    Nonempty (Representation.Equiv
      ((F.heterogeneousPair hC (Nat.add_pos_left hA B) ρ₀
        (F.heterogeneousPair hA hB ρ₁ ρ₂)).comp
        (GeneralLinear.reindex (R := F.Carrier)
          (finCongr (Nat.add_assoc C A B))).toMonoidHom)
      (F.heterogeneousPair (Nat.add_pos_left hC A) hB
        (F.heterogeneousPair hC hA ρ₀ ρ₁) ρ₂)) := by
  let := F.canonicalTopologicalData.topology
  dsimp only [PadicField.heterogeneousPair]
  exact hassoc p F C A B hC hA hB ρ₀ ρ₁ ρ₂ hρ₀ hρ₁ hρ₂

private theorem remove_X_power {P A : ℂ[X]} {e : ℕ}
    (hP : P.coeff 0 = 1) (hdiv : P ∣ X ^ e * A) : P ∣ A := by
  have hcop : IsCoprime P X := by
    refine ⟨1, -P.divX, ?_⟩
    have hx := Polynomial.X_mul_divX_add P
    rw [hP, Polynomial.C_1] at hx
    calc
      1 * P + -P.divX * X = P - X * P.divX := by ring
      _ = 1 := sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx.symm)
  exact hcop.pow_right.dvd_of_dvd_mul_left hdiv

end InducedTailRamifiedAssembly

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency.types false in
open InducedTailRamifiedAssembly in
/-- Conditional all-rank assembly in a carrier universe closed under actual
normalized induction. Every open analytic and structural input is explicit. -/
theorem inducedTailLFactor_of_inputs_commonUniverse
    (hspans : InducedTailSpanStatement.{uF, max uF u, max uF u, max uF u})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hexists : SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u})
    (hopp : TwoBlockLFactorMultiplicativityStatement.{uF, max uF u, max uF u})
    (hassoc : Parabolic.ThreeBlockInductionAssociativityStatement.{
      uF, max uF u, max uF u, max uF u})
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF u}) :
    InducedTailLFactorStatement.{uF, max uF u, max uF u, max uF u} := by
  intro p hp F ψ ν a b t V₁ _ _ V₂ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ
  let := F.canonicalTopologicalData.topology
  obtain ⟨Ptail, htail⟩ := hexists p F ψ ν b t V₂ W π₂ σ hπ₂ hσ
  have hrec : ∀ (d c : ℕ)
      {U : Type (max uF u)} [AddCommGroup U] [Module ℂ U]
      (ρ : Representation ℂ (Langlands.GeneralLinear (c + 1) F.Carrier) U),
      IsOfWhittakerType c (standardCharacter ψ c) ρ →
      t + 1 - (c + 1 + b) ≤ d →
      ∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val
        (F.heterogeneousPair (Nat.succ_pos c) (Nat.succ_pos b) ρ π₂) σ P →
        Ptail ∣ P := by
    intro d
    induction d with
    | zero =>
      intro c U _ _ ρ hρ hbound P hP
      exact inducedTailDirectPolynomialDivisibility_of_spans hspans p F ψ ν c b t
        ρ π₂ σ hρ hπ₂ hσ (by omega) P Ptail hP htail
    | succ d ih =>
      intro c U _ _ ρ hρ hbound P hP
      by_cases hsmall : t + 1 < (c + 1) + (b + 1)
      · exact inducedTailDirectPolynomialDivisibility_of_spans hspans p F ψ ν c b t
          ρ π₂ σ hρ hπ₂ hσ hsmall P Ptail hP htail
      · have hlarge : (c + 1) + (b + 1) ≤ t + 1 := by omega
        obtain ⟨χ, hχ⟩ := ramifiedCharacter_exists hram F ψ ν σ hσ
        let μ := universeLiftRepresentation.{max uF u}
          (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
        have hμ : IsOfWhittakerType 0 (standardCharacter ψ 0) μ :=
          (rankOneWhittakerType p F ψ χ).of_equiv (universeLiftEquiv.{max uF u} _)
        let ξ := F.heterogeneousPair (Nat.succ_pos c) (Nat.succ_pos b) ρ π₂
        have hξ := heterogeneousPair_whittakerType htype F ψ ρ π₂ hρ hπ₂
        let τ := F.heterogeneousPair (Nat.succ_pos 0) (Nat.succ_pos c) μ ρ
        have hτ := heterogeneousPair_whittakerType htype F ψ μ ρ hμ hρ
        let η := F.heterogeneousPair (Nat.succ_pos 0) (Nat.succ_pos (c + 1 + b)) μ ξ
        have hη := heterogeneousPair_whittakerType htype F ψ μ ξ hμ hξ
        obtain ⟨Pη, hPη⟩ :=
          hexists p F ψ ν (0 + 1 + (c + 1 + b)) t _ W η σ hη hσ
        obtain ⟨e⟩ := heterogeneousPair_assoc hassoc F
          (Nat.succ_pos 0) (Nat.succ_pos c) (Nat.succ_pos b)
          μ ρ π₂ hμ.1.1 hρ.1.1 hπ₂.1.1
        have hPηcast := (symmetricLPolynomial_rankCast F ψ ν
          (show (1 + c) + 1 + b = 0 + 1 + (c + 1 + b) by omega) η σ Pη).mpr hPη
        have hright := (IsPadicSymmetricLPolynomial.congr_equiv e
          (Representation.Equiv.refl σ)).mp hPηcast
        have hdiv := ih (1 + c) τ hτ (by omega) Pη hright
        obtain ⟨Q, k, hrel⟩ :=
          heterogeneousPair_oppositeDivisibility hopp F ψ ν μ ξ σ
            hμ hξ hσ Pη 1 P hPη hχ hP
        have hcleared : Ptail ∣ X ^ k * P := by
          rw [one_mul] at hrel
          rw [hrel]
          exact dvd_mul_of_dvd_right hdiv Q
        exact remove_X_power htail.coeff_zero hcleared
  let ξ := F.heterogeneousPair (Nat.succ_pos a) (Nat.succ_pos b) π₁ π₂
  have hξ := heterogeneousPair_whittakerType htype F ψ π₁ π₂ hπ₁ hπ₂
  obtain ⟨Pfull, hfull⟩ := hexists p F ψ ν (a + 1 + b) t _ W ξ σ hξ hσ
  exact ⟨Pfull, Ptail, hfull, htail,
    hrec (t + 1 - (a + 1 + b)) a π₁ hπ₁ le_rfl Pfull hfull⟩

/-- Conditional support only: this proves the separate six-input assembly
interface, not the closed parent proposition. -/
theorem inducedTailConditionalAssembly :
    InducedTailConditionalAssemblyStatement.{uF, uV₁, uV₂, uW} := by
  intro hspans htype hexists hopp hassoc hram
  exact inducedTailLFactor_of_commonUniverse
    (inducedTailLFactor_of_inputs_commonUniverse.{uF, max uV₁ uV₂ uW}
      hspans htype hexists hopp hassoc hram)

end Langlands.RankinSelberg
