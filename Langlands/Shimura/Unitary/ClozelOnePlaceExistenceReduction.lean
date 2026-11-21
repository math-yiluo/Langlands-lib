import Langlands.Shimura.Unitary.ClozelOnePlaceExistenceStatement
import Langlands.Shimura.Unitary.DivisionFromBrauerOrder
import Langlands.Shimura.Unitary.RealReflex
import Langlands.Shimura.Unitary.UnitaryLocalProfileRealizationStatement
import Langlands.Global.RealTensorSplitting

/-! # From a compatible local profile to Clozel's one-place algebra -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local

variable (E : Type u) [Field E] [NumberField E] [IsTotallyReal E]

private theorem card_real_embeddings :
    Fintype.card (E →+* ℝ) = Module.finrank ℚ E :=
  (Fintype.card_congr (TotallyReal.realComplexEmbeddings E)).trans
    (NumberField.Embeddings.card E ℂ)

open scoped Classical in
private theorem onePlace_profile_compatible (n : ℕ) (hn : 1 < n)
    (p₀ : Langlands.Global.FinitePlace E) (τ₀ : E →+* ℝ)
    (parity : Odd n ∨ 4 ∣ n ∨ (Even n ∧ Even (Module.finrank ℚ E))) :
    CompatibleUnitaryLocalProfile E (s := {p₀}) (fun _ ↦ (1 : ZMod n))
      (fun τ ↦ if τ = τ₀ then n - 1 else n) := by
  classical
  intro hnEven
  have hProduct : 2 ∣ Fintype.card (E →+* ℝ) * (n / 2) := by
    rcases parity with hnOdd | hnFour | ⟨_, hDegree⟩
    · obtain ⟨m, hm⟩ := hnOdd
      obtain ⟨k, hk⟩ := hnEven
      omega
    · apply dvd_mul_of_dvd_right
      obtain ⟨m, hm⟩ := hnFour
      exact ⟨m, by omega⟩
    · rw [card_real_embeddings E]
      exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp hDegree) _
  have hZero := (ZMod.natCast_eq_zero_iff _ 2).mpr hProduct
  have hNegative (τ : E →+* ℝ) :
      n - (if τ = τ₀ then n - 1 else n) = if τ = τ₀ then 1 else 0 := by
    split_ifs <;> omega
  have hReal : (∑ τ : E →+* ℝ, ((n - (if τ = τ₀ then n - 1 else n) : ℕ) : ZMod 2)) =
      1 := by
    simp_rw [hNegative, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp
  have hFinite : (∑ p : ({p₀} : Finset _), ZMod.castHom hnEven (ZMod 2) (1 : ZMod n)) =
      1 := by
    simp [ZMod.cast_one hnEven]
  rw [hFinite, hZero, hReal]
  decide

private theorem denominator_addOrderOf (n : ℕ) (hn : 0 < n) (a : ZMod n) :
    addOrderOf ((denominatorEquiv n hn a : denominatorSubgroup n) : RationalModIntegers) =
      addOrderOf a :=
  (addOrderOf_injective (denominatorSubgroup n).subtype Subtype.val_injective
    (denominatorEquiv n hn a)).trans ((denominatorEquiv n hn).addOrderOf_eq a)

variable (K : Type v) [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- Global realization of unitary local profiles implies the published existence
statement at each prescribed split finite place. -/
def ClozelOnePlaceExistenceReductionStatement : Prop :=
  UnitaryLocalProfileRealizationStatement (E := E) (K := K) →
    ∀ (n : ℕ) (v₀ : Langlands.Global.FinitePlace E), ClozelOnePlaceExistenceStatement E K n v₀

/-- Realize the one-place division algebra with its nondefinite signature at
the supplied real embedding. -/
theorem clozelOnePlaceExistence_at_of_localProfile
    (realize : UnitaryLocalProfileRealizationStatement (E := E) (K := K))
    (n : ℕ) (v₀ : Langlands.Global.FinitePlace E) (τ₀ : E →+* ℝ)
    (hn : 1 < n) (hSplit : IsSplitPlace E K v₀)
    (hParity : Odd n ∨ 4 ∣ n ∨ (Even n ∧ Even (Module.finrank ℚ E))) :
    ∃ (A : Type (max u v)) (ringA : Ring A),
      letI : Ring A := ringA
      ∃ algE : Algebra E A,
        letI : Algebra E A := algE
        ∃ algK : Algebra K A,
          letI : Algebra K A := algK
          ∃ tower : IsScalarTower E K A,
            letI : IsScalarTower E K A := tower
            ∃ D : CentralSimpleUnitaryData E K A n,
              D.IsDivision ∧
                (HasSignature D.toSecondKindInvolution τ₀ n (n - 1) ∧
                  ∀ τ, τ ≠ τ₀ → HasSignature D.toSecondKindInvolution τ n n) ∧
                IsDivisionAbove (K := K) (A := A) v₀ ∧
                ∀ p : Langlands.Global.FinitePlace E, p ≠ v₀ →
                  IsQuasiSplitAt D.toSecondKindInvolution n p := by
  classical
  let s : Finset (Langlands.Global.FinitePlace E) := {v₀}
  have hp (p : s) : p.val = v₀ := Finset.mem_singleton.mp p.property
  let p₀ : s := ⟨v₀, Finset.mem_singleton_self _⟩
  let positive (p : s) : FinitePlacesAbove K p.val := placeAbove K p.val
  let r (τ : E →+* ℝ) : ℕ := if τ = τ₀ then n - 1 else n
  have hr (τ : E →+* ℝ) : r τ ≤ n := by
    dsimp only [r]
    split_ifs <;> omega
  have hsSplit (p : s) : IsSplitPlace E K p.val := hp p ▸ hSplit
  have hCompatible := onePlace_profile_compatible E n hn v₀ τ₀ hParity
  obtain ⟨A, ringA, algE, algK, tower, D, hReal, hFinite, hBrauer⟩ :=
    realize n hn s hsSplit positive (fun _ ↦ 1) r hr hCompatible
  let _ : Ring A := ringA
  let _ : Algebra E A := algE
  let _ : Algebra K A := algK
  let _ : IsScalarTower E K A := tower
  have hAbove : IsDivisionAbove (K := K) (A := A) v₀ := by
    intro q hq
    obtain ⟨B, ⟨e⟩, hInv⟩ := hBrauer p₀ ⟨q, hq⟩
    apply isDivisionAt_of_brauer_order D q B e
    rw [← (finiteBrauerInvariant K q).addOrderOf_eq (Brauer.classOf B), hInv,
      denominator_addOrderOf]
    split <;> simp [ZMod.addOrderOf_one]
  refine ⟨A, ringA, algE, algK, tower, D,
    isDivision_of_isDivisionAbove D v₀ hAbove, ⟨?_, ?_⟩, hAbove, ?_⟩
  · simpa [r] using hReal τ₀
  · intro τ hτ
    simpa [r, hτ] using hReal τ
  · intro p hp₀
    exact hFinite p (by simpa only [s, Finset.mem_singleton] using hp₀)

/-- Global realization gives the published one-place existence proposition. -/
theorem clozelOnePlaceExistence_of_localProfile : ClozelOnePlaceExistenceReductionStatement E K := by
  intro realize n v₀ hn hSplit hParity
  let τ₀ : E →+* ℝ :=
    (TotallyReal.realComplexEmbeddings E).symm (Classical.choice inferInstance)
  obtain ⟨A, ringA, algE, algK, tower, D, hDivision, ⟨hτ₀, hOthers⟩, hAbove, hFinite⟩ :=
    clozelOnePlaceExistence_at_of_localProfile E K realize n v₀ τ₀ hn hSplit hParity
  exact ⟨A, ringA, algE, algK, tower, D, hDivision, ⟨hn, τ₀, hτ₀, hOthers⟩, hAbove, hFinite⟩

variable {E K} {A : Type*} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]

/-- With a Harris CM section, the one-place parity hypothesis covers the real
reflex comparison also in rank two. -/
theorem realReflexField_eq_distinguishedImage_of_onePlaceParity
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {F : Type*} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
    {j : F →+* K} {τF : F →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τF))
    (hParity : Odd n ∨ 4 ∣ n ∨ (Even n ∧ Even (Module.finrank ℚ E))) :
    D.realReflexField C = C.distinguishedImage := by
  apply D.realReflexField_eq_distinguishedImage C
  by_cases hn : 3 ≤ n
  · exact Or.inl hn
  have hn2 : n = 2 := by
    have := D.rank_gt_one
    omega
  have hEvenDegree : Even (Module.finrank ℚ E) := by
    rcases hParity with hnOdd | hnFour | ⟨_, hEven⟩
    · obtain ⟨m, hm⟩ := hnOdd
      omega
    · omega
    · exact hEven
  have hCard : 1 < Fintype.card (E →+* ℝ) := by
    rw [card_real_embeddings E]
    obtain ⟨d, hd⟩ := hEvenDegree
    have hPos : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  exact Or.inr (Fintype.exists_ne_of_one_lt_card hCard C.distinguished)

end Langlands.Shimura.FiniteUnitary
