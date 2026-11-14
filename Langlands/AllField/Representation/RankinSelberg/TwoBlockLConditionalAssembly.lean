import Langlands.Representation.RankinSelberg.TwoBlockLConditionalAssembly
import Langlands.AllField.Representation.RankinSelberg.EqualRankFactorSwapStatement
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeStatement
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedStatement
/-!
# Conditional two-block L-polynomial rank descent

Internal support for the two-stage descent of JPSS Section 7. The polynomial
relation preserves the powers of `X` permitted by the published target. Every
analytic input, including the separate equal-rank reverse comparison, remains
an explicit hypothesis. No closed multiplicativity theorem is asserted here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly
open Langlands.RankinSelberg.TwoBlockLConditionalAssembly hiding EqualRankReverseAt twoBlockLMultiplicativity_of_inputs_commonUniverse
open Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaMultiplicativityStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLFactorMultiplicativityStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerTypeHighlyRamifiedLVanishingStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW u

private theorem polynomialLDivides_of_dvd {P A : ℂ[X]} (h : P ∣ A) :
    PolynomialLDivides P A := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, 0, by rw [pow_zero, one_mul, hQ, mul_comm]⟩

private theorem polynomialLDivides_trans {P A B : ℂ[X]}
    (hPA : PolynomialLDivides P A) (hAB : PolynomialLDivides A B) :
    PolynomialLDivides P B := by
  obtain ⟨Q, e, he⟩ := hPA
  obtain ⟨R, f, hf⟩ := hAB
  refine ⟨R * Q, e + f, ?_⟩
  calc
    X ^ (e + f) * B = X ^ e * (X ^ f * B) := by rw [pow_add, mul_assoc]
    _ = X ^ e * (R * A) := by rw [hf]
    _ = R * (X ^ e * A) := by ring
    _ = R * (Q * P) := by rw [he]
    _ = R * Q * P := by ring

private theorem polynomialLDivides_mul {P₀ A₀ P₁ A₁ : ℂ[X]}
    (h₀ : PolynomialLDivides P₀ A₀) (h₁ : PolynomialLDivides P₁ A₁) :
    PolynomialLDivides (P₀ * P₁) (A₀ * A₁) := by
  obtain ⟨Q₀, e₀, he₀⟩ := h₀
  obtain ⟨Q₁, e₁, he₁⟩ := h₁
  refine ⟨Q₀ * Q₁, e₀ + e₁, ?_⟩
  calc
    X ^ (e₀ + e₁) * (A₀ * A₁) = (X ^ e₀ * A₀) * (X ^ e₁ * A₁) := by
      rw [pow_add]
      ring
    _ = (Q₀ * P₀) * (Q₁ * P₁) := by rw [he₀, he₁]
    _ = Q₀ * Q₁ * (P₀ * P₁) := by ring

private theorem polynomialLDivides_prod {P A : Fin 2 → ℂ[X]}
    (h : ∀ i, PolynomialLDivides (P i) (A i)) :
    PolynomialLDivides (∏ i, P i) (∏ i, A i) := by
  simpa only [Fin.prod_univ_two] using polynomialLDivides_mul (h 0) (h 1)

/-- The polynomial part of either descent step in JPSS Section 7. -/
private theorem polynomialLDivides_descent {P Paux : ℂ[X]}
    {Pi Piaux : Fin 2 → ℂ[X]} (hreverse : P ∣ Paux)
    (haux : PolynomialLDivides Paux (∏ i, Piaux i))
    (hblocks : ∀ i, PolynomialLDivides (Piaux i) (Pi i)) :
    PolynomialLDivides P (∏ i, Pi i) :=
  polynomialLDivides_trans (polynomialLDivides_of_dvd hreverse)
    (polynomialLDivides_trans haux (polynomialLDivides_prod hblocks))

section Certificates

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F}
  {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
  {r t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}

/-- Away from equal rank, exchanging the symmetric L relation is definitional;
at equal rank it uses precisely the separate equal-rank swap input. -/
private theorem symmetricLPolynomial_swap
    (hswap : EqualRankFactorSwapStatement.{uF, uV, uW})
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ)
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P ↔
      IsPadicSymmetricLPolynomial F ψ ν.val σ π P := by
  by_cases hrt : r = t
  · subst t
    simpa only [IsPadicSymmetricLPolynomial, le_refl, ↓reduceIte] using
      (hswap F ψ ν r π σ hπ hσ).1 P
  · rcases lt_or_gt_of_ne hrt with hlt | hgt
    · simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr hlt,
        Nat.le_of_lt hlt, ↓reduceIte]
    · simp only [IsPadicSymmetricLPolynomial, Nat.not_le.mpr hgt,
        Nat.le_of_lt hgt, ↓reduceIte]

end Certificates

/-- One fixed two-block conclusion, with the same certified polynomial data as
the published closed target. This private definition only shortens the draft. -/
private def TwoBlockLConclusion (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {r t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) : Prop :=
  ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
    IsPadicSymmetricLPolynomial F ψ ν.val π
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
    (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
    PolynomialLDivides P (∏ i, Pi i)

/-- Uniqueness lets a base-case witness or induction hypothesis be used with
any already chosen certified polynomials for the same actual representations. -/
private theorem twoBlockLConclusion_relation 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)}
    (hconclusion : TwoBlockLConclusion F ψ ν m h π σ)
    {P : ℂ[X]} {Pi : Fin 2 → ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P)
    (hPi : ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) :
    PolynomialLDivides P (∏ i, Pi i) := by
  obtain ⟨P', Pi', hP', hPi', hrelation⟩ := hconclusion
  have hPP : P' = P := hP'.unique hP
  have hPiPi : Pi' = Pi := funext fun i => (hPi' i).unique (hPi i)
  simpa only [hPP, hPiPi] using hrelation

section AuxiliaryInduction

private abbrev auxiliaryRanks (r : ℕ) : Fin 2 → ℕ := ![0, r]

private theorem auxiliaryRankSum (r : ℕ) :
    ∑ i, (auxiliaryRanks r i + 1) = (1 + r) + 1 := by
  simp only [auxiliaryRanks, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

private def auxiliaryFamily {F : Type uF} [Field F]
    {r : ℕ} {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (auxiliaryRanks r i + 1) F)
      (Shahidi.pairCarrier C V i) :=
  match i with
  | 0 => χrep
  | 1 => π

private theorem auxiliaryFamily_heq {F : Type uF} [Field F]
    {r : ℕ} {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V) :
    HEq (auxiliaryFamily χrep π) (Shahidi.pairFamily χrep π) := by
  apply Function.hfunext rfl
  intro i j hij
  have hij' : i = j := eq_of_heq hij
  subst j
  fin_cases i <;> rfl

set_option maxHeartbeats 800000 in
private theorem auxiliaryInduced_certificate 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν.val σ
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
          (auxiliaryFamily χrep π)) P ↔
      IsPadicSymmetricLPolynomial F ψ ν.val σ
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (Shahidi.twoBlocks 1 (r + 1) (Nat.succ_pos 0) (Nat.succ_pos r))
          (Shahidi.pairFamily χrep π)) P := by
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧ ∑ i, s i = (1 + r) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F)
      (Shahidi.pairCarrier C V i)
  let d₀ : D := ⟨⟨fun i => auxiliaryRanks r i + 1,
    ⟨fun i => Nat.succ_pos _, auxiliaryRankSum r⟩⟩, auxiliaryFamily χrep π⟩
  let d₁ : D := ⟨⟨![1, r + 1], ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily χrep π⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · exact auxiliaryFamily_heq χrep π
  let certificate : D → Prop := fun d =>
    IsPadicSymmetricLPolynomial F ψ ν.val σ
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2) P
  change certificate d₀ ↔ certificate d₁
  rw [hd]

private theorem auxiliaryFamily_whittakerType 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    (htype : NormalizedProductWhittakerTypeStatement.{uF, u})
    {r : ℕ} {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    {χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    (hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χrep)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π) :
    IsOfWhittakerType (1 + r) (standardCharacter ψ (1 + r))
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
        (auxiliaryFamily χrep π)) := by
  apply htype F ψ (1 + r) 2 (auxiliaryRanks r) (auxiliaryRankSum r)
    (auxiliaryFamily χrep π)
  intro i
  fin_cases i
  · exact hχ
  · exact hπ

private theorem auxiliaryConclusion_relation 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    (hconclusion : TwoBlockLConclusion F ψ ν (auxiliaryRanks r) (auxiliaryRankSum r)
      σ (auxiliaryFamily χrep π))
    {Pbase Paux : ℂ[X]}
    (hχ : IsPadicSymmetricLPolynomial F ψ ν.val σ χrep 1)
    (hPbase : IsPadicSymmetricLPolynomial F ψ ν.val σ π Pbase)
    (hPaux : IsPadicSymmetricLPolynomial F ψ ν.val σ
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
        (auxiliaryFamily χrep π)) Paux) :
    PolynomialLDivides Paux Pbase := by
  have hPi : ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val σ
      (auxiliaryFamily χrep π i) (![1, Pbase] i) := by
    intro i
    fin_cases i
    · exact hχ
    · exact hPbase
  have hrel := twoBlockLConclusion_relation hconclusion hPaux hPi
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    using hrel

/-- A certified concrete descent step. Analytic reverse comparison, cross
vanishing, and all uses of multiplicativity remain explicit inputs. -/
private theorem twoBlockLConclusion_descent 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {C V : Type u} [AddCommGroup C] [Module ℂ C]
    [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)}
    (hswapBase : EqualRankFactorSwapStatement.{uF, u, uW})
    (hswapAux : EqualRankFactorSwapStatement.{uF, max uF u, uW})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, u})
    (hχtype : IsOfWhittakerType 0 (standardCharacter ψ 0) χrep)
    (hπtype : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hreverse : ∃ P Paux : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      IsPadicSymmetricLPolynomial F ψ ν.val
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
          (auxiliaryFamily χrep π))
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) Paux ∧
      P ∣ Paux)
    (hbase : ∀ i, ∃ Pi : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) Pi)
    (haux : TwoBlockLConclusion F ψ ν m h
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
        (auxiliaryFamily χrep π)) σ)
    (hblocks : ∀ i, TwoBlockLConclusion F ψ ν
      (auxiliaryRanks r) (auxiliaryRankSum r) (σ i) (auxiliaryFamily χrep π))
    (hcross : ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val (σ i) χrep 1) :
    TwoBlockLConclusion F ψ ν m h π σ := by
  classical
  obtain ⟨P, Paux, hP, hPaux, hreverse⟩ := hreverse
  choose Pi hPi using hbase
  obtain ⟨Paux', Piaux, hPaux', hPiaux, hrelAux⟩ := haux
  have hPauxEq : Paux' = Paux := hPaux'.unique hPaux
  have hauxType := auxiliaryFamily_whittakerType htype hχtype hπtype
  have hblockRelations : ∀ i, PolynomialLDivides (Piaux i) (Pi i) := by
    intro i
    apply auxiliaryConclusion_relation (hblocks i) (hcross i)
    · exact (symmetricLPolynomial_swap hswapBase hπtype (hσtype i)).mp (hPi i)
    · exact (symmetricLPolynomial_swap hswapAux hauxType (hσtype i)).mp (hPiaux i)
  refine ⟨P, Pi, hP, hPi, ?_⟩
  apply polynomialLDivides_descent hreverse
  · simpa only [hPauxEq] using hrelAux
  · exact hblockRelations

end AuxiliaryInduction

section AuxiliaryCharacter

private abbrev scalarCharacterLift {F : Type uF} [Field F] (χ : Fˣ →* ℂˣ) :
    Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{u} ℂ) :=
  (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp (rankOneCharacter χ)

private def scalarCharacterLiftEquiv {F : Type uF} [Field F] (χ : Fˣ →* ℂˣ) :
    (rankOneCharacter χ).Equiv (scalarCharacterLift.{uF, u} χ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)

private theorem twist_rankOneCharacter_one {F : Type uF} [Field F]
    (χ : Fˣ →* ℂˣ) :
    Langlands.twist (χ.comp determinant) (rankOneCharacter 1) = rankOneCharacter χ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (χ (determinant g) : ℂ) * (1 * v) = (χ (determinant g) : ℂ) * v
  rw [one_mul]

/-- Only the two block cross factors are needed for the cleared descent. -/
private theorem auxiliaryCharacter_exists 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {m : Fin 2 → ℕ}
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)}
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, uW})
    (hrankOne : RankOneWhittakerTypeStatement.{uF})
    (hswap : EqualRankFactorSwapStatement.{uF, 0, uW})
    (hcharacters : ∀ A : ℕ, ∃ χ :
      (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    ∃ χ : (Quasicharacter F),
      (IsOfWhittakerType 0 (standardCharacter ψ 0)
          (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ))) ∧
      ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val (σ i)
        (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)) 1 := by
  classical
  have htrivial := hrankOne F ψ (1 : Quasicharacter F)
  have hbounds : ∀ i, ∃ A : ℕ, ∀ χ : Quasicharacter F,
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ →
        IsPadicSymmetricLPolynomial F ψ ν.val
          (rankOneCharacter (χ : Fˣ →* ℂˣ)) (σ i) 1 := by
    intro i
    obtain ⟨A, hA⟩ := hram F ψ ν 0 (m i) (rankOneCharacter 1) (σ i) htrivial (hσ i)
    refine ⟨A, fun χ hχ => ?_⟩
    have hcert := hA χ hχ
    rw [twist_rankOneCharacter_one (χ : Fˣ →* ℂˣ)] at hcert
    exact hcert
  choose A hA using hbounds
  obtain ⟨χ, hχ⟩ := hcharacters (max (A 0) (A 1))
  have hχtype := hrankOne F ψ χ
  refine ⟨χ, hχtype.of_equiv (scalarCharacterLiftEquiv.{uF, u} _), ?_⟩
  intro i
  have hAi : A i ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ := by
    apply le_trans _ hχ
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hcert := (symmetricLPolynomial_swap hswap hχtype (hσ i)).mp (hA i χ hAi)
  exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl (σ i))
    (scalarCharacterLiftEquiv.{uF, u} _)).mp hcert

end AuxiliaryCharacter

section RestrictedReverse

/-- The restricted Lemma 5.5 comparison, in the certificate orientation used
by the concrete descent. Its original strict rank margin is retained. -/
private theorem auxiliaryReverse_safe 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    (hrestricted : RankOneExtensionLDivisibilityStatement.{uF, uW, u})
    (hswapBase : EqualRankFactorSwapStatement.{uF, u, uW})
    (hswapAux : EqualRankFactorSwapStatement.{uF, max uF u, uW})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, u})
    (χ : Quasicharacter F)
    (hrange : r + 3 ≤ t + 1)
    (hχtype : IsOfWhittakerType 0 (standardCharacter ψ 0)
        (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)))
    (hπtype : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : IsOfWhittakerType t (standardCharacter ψ t) σ) :
    ∃ P Paux : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧
      IsPadicSymmetricLPolynomial F ψ ν.val
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
          (auxiliaryFamily (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)) π)) σ Paux ∧
      P ∣ Paux := by
  obtain ⟨P, Paux, hP, hPaux, hdiv⟩ :=
    hrestricted F ψ ν t r σ π χ hrange hσtype hπtype
  have hPauxNative := (auxiliaryInduced_certificate
    (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)) π σ Paux).mpr hPaux
  have hauxType := auxiliaryFamily_whittakerType htype hχtype hπtype
  exact ⟨P, Paux, (symmetricLPolynomial_swap hswapBase hπtype hσtype).mpr hP,
    (symmetricLPolynomial_swap hswapAux hauxType hσtype).mpr hPauxNative, hdiv⟩

end RestrictedReverse

section FirstRankDescent

set_option maxHeartbeats 800000 in
/-- The first descent: a rank-one first upper block, with arbitrary original
rank-one representation and with all analytic premises still explicit. -/
private theorem twoBlockL_firstRankOne 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    (hdominant : TwoBlockLDominantRankStatement.{uF, max uF u, max uF u})
    (hadjacent : TwoBlockLAdjacentRankStatement.{uF, max uF u, max uF u})
    (hrankBase : TwoBlockLRankOneStatement.{uF, max uF u, max uF u})
    (hrestricted : RankOneExtensionLDivisibilityStatement.{uF, max uF u, max uF u})
    (hexists : SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u})
    (hswap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF u})
    (hrankOne : RankOneWhittakerTypeStatement.{uF})
    (hscalarSwap : EqualRankFactorSwapStatement.{uF, 0, max uF u})
    (hcharacters : ∀ A : ℕ, ∃ χ :
      (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ)
    {r t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type (max uF u)} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)}
    (hmzero : m 0 = 0)
    (hπtype : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    TwoBlockLConclusion F ψ ν m h π σ := by
  have htotalType := htype F ψ t 2 m h σ hσtype
  have hsum : m 0 + 1 + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  have hdesc : ∀ d r, t - r = d →
      ∀ {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
      (IsOfWhittakerType r (standardCharacter ψ r) π) →
      TwoBlockLConclusion F ψ ν m h π σ := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hdr V _ _ π hπtype
      by_cases hdom : t ≤ r
      · exact hdominant F ψ ν r t m h π σ hdom hπtype hσtype
      by_cases hadj : t = r + 1
      · exact hadjacent F ψ ν r t m h π σ hadj hmzero hπtype hσtype
      have hrange : r + 3 ≤ t + 1 := by omega
      obtain ⟨χ, hχtype, hcross⟩ := auxiliaryCharacter_exists.{uF, max uF u, max uF u}
        hram hrankOne hscalarSwap hcharacters hσtype
      let χrep := scalarCharacterLift.{uF, max uF u} (χ : Fˣ →* ℂˣ)
      let σaux := auxiliaryFamily χrep π
      have hσauxType : ∀ i, IsOfWhittakerType (auxiliaryRanks r i)
            (standardCharacter ψ (auxiliaryRanks r i)) (σaux i) := by
        intro i
        fin_cases i
        · exact hχtype
        · exact hπtype
      have hauxType := auxiliaryFamily_whittakerType htype hχtype hπtype
      have haux : TwoBlockLConclusion F ψ ν m h
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced
            (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r)) σaux) σ := by
        exact ih (t - (1 + r)) (by omega) (1 + r) rfl _ hauxType
      have hblocks : ∀ i, TwoBlockLConclusion F ψ ν
          (auxiliaryRanks r) (auxiliaryRankSum r) (σ i) σaux := by
        intro i
        fin_cases i
        · exact hrankBase F ψ ν (m 0) (1 + r) (auxiliaryRanks r)
            (auxiliaryRankSum r) (σ 0) σaux hmzero (hσtype 0) hσauxType
        · exact hdominant F ψ ν (m 1) (1 + r) (auxiliaryRanks r)
            (auxiliaryRankSum r) (σ 1) σaux (by omega) (hσtype 1) hσauxType
      apply twoBlockLConclusion_descent hswap hswap htype hχtype hπtype hσtype
      · exact auxiliaryReverse_safe hrestricted hswap hswap htype χ hrange
          hχtype hπtype htotalType
      · intro i
        exact hexists F ψ ν r (m i) _ _ π (σ i) hπtype (hσtype i)
      · exact haux
      · exact hblocks
      · exact hcross
  exact hdesc (t - r) r rfl π hπtype

end FirstRankDescent

section GeneralRankDescent

/-- The fieldwise equal-rank reverse comparison required by the second
descent. This internal predicate is an explicit input, with no proof asserted. -/
def EqualRankReverseAt (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ) : Prop :=
  ∀ (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 2) F) V)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) W)
    (χ : Quasicharacter F),
    (IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) τ) →
    (IsOfWhittakerType r (standardCharacter ψ r) π) →
    ∃ Pbase Pind : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val τ π Pbase ∧
      IsPadicSymmetricLPolynomial F ψ ν.val τ
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (Shahidi.twoBlocks 1 (r + 1) (Nat.succ_pos 0) (Nat.succ_pos r))
          (Shahidi.pairFamily
            (scalarCharacterLift.{uF, uW} (χ : Fˣ →* ℂˣ)) π)) Pind ∧
      Pbase ∣ Pind

private theorem auxiliaryReverse_all 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    {r t : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    (hrestricted : RankOneExtensionLDivisibilityStatement.{uF, uW, u})
    (hequal : EqualRankReverseAt.{uF, uW, u} F ψ ν)
    (hswapBase : EqualRankFactorSwapStatement.{uF, u, uW})
    (hswapAux : EqualRankFactorSwapStatement.{uF, max uF u, uW})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, u})
    (χ : Quasicharacter F)
    (hrange : r < t)
    (hχtype : IsOfWhittakerType 0 (standardCharacter ψ 0)
        (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)))
    (hπtype : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : IsOfWhittakerType t (standardCharacter ψ t) σ) :
    ∃ P Paux : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧
      IsPadicSymmetricLPolynomial F ψ ν.val
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r))
          (auxiliaryFamily (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)) π)) σ Paux ∧
      P ∣ Paux := by
  by_cases heq : t = r + 1
  · subst t
    obtain ⟨P, Paux, hP, hPaux, hdiv⟩ := hequal r σ π χ hσtype hπtype
    have hPauxNative := (auxiliaryInduced_certificate
      (scalarCharacterLift.{uF, u} (χ : Fˣ →* ℂˣ)) π σ Paux).mpr hPaux
    have hauxType := auxiliaryFamily_whittakerType htype hχtype hπtype
    exact ⟨P, Paux, (symmetricLPolynomial_swap hswapBase hπtype hσtype).mpr hP,
      (symmetricLPolynomial_swap hswapAux hauxType hσtype).mpr hPauxNative, hdiv⟩
  · exact auxiliaryReverse_safe hrestricted hswapBase hswapAux htype χ (by omega)
      hχtype hπtype hσtype

set_option maxHeartbeats 800000 in
/-- The second concrete descent in the stable carrier universe. The missing
analytic endpoint and all separately owned analytic results remain premises. -/
private theorem twoBlockL_allRanks 
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {ψ : UnitaryAdditiveCharacter F}
    {ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ}
    (hdominant : TwoBlockLDominantRankStatement.{uF, max uF u, max uF u})
    (hadjacent : TwoBlockLAdjacentRankStatement.{uF, max uF u, max uF u})
    (hrankBase : TwoBlockLRankOneStatement.{uF, max uF u, max uF u})
    (hrestricted : RankOneExtensionLDivisibilityStatement.{uF, max uF u, max uF u})
    (hequal : EqualRankReverseAt.{uF, max uF u, max uF u} F ψ ν)
    (hexists : SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u})
    (hswap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF u})
    (hrankOne : RankOneWhittakerTypeStatement.{uF})
    (hscalarSwap : EqualRankFactorSwapStatement.{uF, 0, max uF u})
    (hcharacters : ∀ A : ℕ, ∃ χ :
      (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ)
    {r t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type (max uF u)} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    {σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)}
    (hπtype : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    TwoBlockLConclusion F ψ ν m h π σ := by
  have htotalType := htype F ψ t 2 m h σ hσtype
  have hdesc : ∀ d r, t - r = d →
      ∀ {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
      (IsOfWhittakerType r (standardCharacter ψ r) π) →
      TwoBlockLConclusion F ψ ν m h π σ := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hdr V _ _ π hπtype
      by_cases hdom : t ≤ r
      · exact hdominant F ψ ν r t m h π σ hdom hπtype hσtype
      have hrange : r < t := by omega
      obtain ⟨χ, hχtype, hcross⟩ := auxiliaryCharacter_exists.{uF, max uF u, max uF u}
        hram hrankOne hscalarSwap hcharacters hσtype
      let χrep := scalarCharacterLift.{uF, max uF u} (χ : Fˣ →* ℂˣ)
      let σaux := auxiliaryFamily χrep π
      have hσauxType : ∀ i, IsOfWhittakerType (auxiliaryRanks r i)
            (standardCharacter ψ (auxiliaryRanks r i)) (σaux i) := by
        intro i
        fin_cases i
        · exact hχtype
        · exact hπtype
      have hauxType := auxiliaryFamily_whittakerType htype hχtype hπtype
      have haux : TwoBlockLConclusion F ψ ν m h
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced
            (succBlockShape (auxiliaryRanks r) (auxiliaryRankSum r)) σaux) σ := by
        exact ih (t - (1 + r)) (by omega) (1 + r) rfl _ hauxType
      have hblocks : ∀ i, TwoBlockLConclusion F ψ ν
          (auxiliaryRanks r) (auxiliaryRankSum r) (σ i) σaux := by
        intro i
        exact twoBlockL_firstRankOne hdominant hadjacent hrankBase hrestricted hexists
          hswap htype hram hrankOne hscalarSwap hcharacters rfl (hσtype i) hσauxType
      apply twoBlockLConclusion_descent hswap hswap htype hχtype hπtype hσtype
      · exact auxiliaryReverse_all hrestricted hequal hswap hswap htype χ hrange
          hχtype hπtype htotalType
      · intro i
        exact hexists F ψ ν r (m i) _ _ π (σ i) hπtype (hσtype i)
      · exact haux
      · exact hblocks
      · exact hcross
  exact hdesc (t - r) r rfl π hπtype

/-- Packaging of the two actual descents as the full published target in a
stable carrier universe. Every missing analytic result is still a premise. -/
theorem twoBlockLMultiplicativity_of_inputs_commonUniverse
    (hdominant : TwoBlockLDominantRankStatement.{uF, max uF u, max uF u})
    (hadjacent : TwoBlockLAdjacentRankStatement.{uF, max uF u, max uF u})
    (hrankBase : TwoBlockLRankOneStatement.{uF, max uF u, max uF u})
    (hrestricted : RankOneExtensionLDivisibilityStatement.{uF, max uF u, max uF u})
    (hequal : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      (ψ : UnitaryAdditiveCharacter F)
      (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ),
      EqualRankReverseAt.{uF, max uF u, max uF u} F ψ ν)
    (hexists : SymmetricLPolynomialExistenceStatement.{uF, max uF u, max uF u})
    (hswap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hram : WhittakerTypeHighlyRamifiedLVanishingStatement.{uF, 0, max uF u})
    (hrankOne : RankOneWhittakerTypeStatement.{uF})
    (hscalarSwap : EqualRankFactorSwapStatement.{uF, 0, max uF u})
    (hcharacters : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (A : ℕ),
      ∃ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ) :
    TwoBlockLFactorMultiplicativityStatement.{uF, max uF u, max uF u} := by
  intro F _ _ _ _ ψ ν r t m h V _ _ W _ _ π σ hπtype hσtype
  exact twoBlockL_allRanks hdominant hadjacent hrankBase hrestricted (hequal F ψ ν)
    hexists hswap htype hram hrankOne hscalarSwap (hcharacters F) hπtype hσtype

end GeneralRankDescent

end Langlands.AllField.RankinSelberg.TwoBlockLConditionalAssembly
