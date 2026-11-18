import Langlands.Representation.Archimedean.RealClearedCompactDegeneration
import Langlands.Representation.Archimedean.RealGenericCharacterBraidReduction

/-! # Canonical mixed character words from a full compact polynomial braid -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCanonicalCharacterBraid

open Langlands.LocalFactor.Archimedean RealBlockMultiplier
  RealRationalCompactFamilies RealSignedTailPolynomial RealClearedCompactDegeneration
  RealStandardFiltration RealBlockFrobeniusMap RealCharacterPair RealCharacterPairReducible
  RealGenericCompactCharacter RealKTypeCount RealCompactPolynomialFourierRelation
  MvPolynomial

/-- Each choice retains the canonical symmetry for the fixed pair parity. -/
inductive Choice (ε : ℤ) : Type
  | generic (ν : ℂ) (hden : ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + ν ≠ 0)
  | binomial (ℓ : ℕ) (pos : 0 < ℓ) (parity : Even ((ℓ : ℤ) - 1 - ε))
  | tail (r : ℕ)

namespace Choice

variable {ε : ℤ}

def parameter : Choice ε → ℂ
  | .generic ν _ => ν
  | .binomial ℓ _ _ => (ℓ : ℂ)
  | .tail r => pole ε r

def multiplier : Choice ε → ℤ → ℂ
  | .generic ν _ => genericMultiplier ν ε
  | .binomial ℓ _ _ => binomialMultiplier ℓ ε
  | .tail r => tailMultiplier (ε.toNat + 2 * r + 1) ε ((-1 : ℂ) ^ ε.natAbs)

def cutoff : Choice ε → ℕ
  | .generic _ _ => 0
  | .binomial _ _ _ => 0
  | .tail r => r + 1

def scale (N : ℕ) : Choice ε → ℂ
  | .generic ν _ => ∏ i ∈ Finset.range N, ((ε : ℂ) + 2 * i + 1 + ν)
  | .binomial ℓ _ _ => positiveScale ℓ N ε
  | .tail r => tailScale ε N r

theorem symmetric (hε : ε = 0 ∨ ε = 1) (c : Choice ε) :
    IsSymmetric ε ((-1 : ℂ) ^ ε.natAbs) c.multiplier := by
  cases c with
  | generic ν hd => exact isSymmetric_genericMultiplier ν hε
  | binomial ℓ hp he => exact isSymmetric_binomialMultiplier ℓ hε
  | tail r =>
    apply isSymmetric_tailMultiplier (by omega) hε _ (neg_one_pow_sq ε.natAbs)
    rw [Int.even_iff]
    have hh : ((ε.toNat : ℕ) : ℤ) = ε := Int.toNat_of_nonneg (by omega)
    omega

theorem scale_ne_zero (hε : ε = 0 ∨ ε = 1) (c : Choice ε) (N : ℕ) :
    c.scale N ≠ 0 := by
  cases c with
  | generic ν hd =>
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  | binomial ℓ hp he => exact positiveScale_ne_zero hp hε he N
  | tail r => exact tailScale_ne_zero hε N r

def operator (N : ℕ) {p : ℕ} (hp : p + 1 < 3) (c : Choice ε) :
    Module.End ℂ (degreeLE 3 N) :=
  spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
    (Finset.Icc (-(N : ℤ)) N) c.multiplier

theorem compactCleared_eq (hε : ε = 0 ∨ ε = 1) (c : Choice ε) (N : ℕ)
    (hN : c.cutoff ≤ N) {p : ℕ} (hp : p + 1 < 3)
    (q : PV) (z : Parameters) (hq : eval z q = c.parameter) :
    compactCleared N hp ε q z = c.scale N • c.operator N hp := by
  cases c with
  | generic ν hd =>
    have hden : eval z (denominator ε N q) ≠ 0 := by
      rw [eval_denominator, hq]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
    rw [RealRationalCompactFamilies.compactCleared_eq N hp ε q z hden]
    simp only [compactGeneric, operator, multiplier, scale, eval_denominator,
      parameter] at hq ⊢
    rw [hq]
  | binomial ℓ hp' he =>
    exact compact_binomial hp hp' hε he q z hq
  | tail r =>
    exact compact_tail hp hε rfl (by change r + 1 ≤ N at hN; omega) q z hq

end Choice

section ActualMaps

variable {n : ℕ} {pre post : List RealBlock} {a b : RealCharacterData}

theorem data
    (hn : realRank (pre ++ .character a :: .character b :: post) = n)
    (c : Choice (pairParity a b)) :
    IsBlockFrobData n (pre ++ .character a :: .character b :: post)
      (pre ++ .character b :: .character a :: post) (realRank pre) (pairParity a b)
      ((-1 : ℂ) ^ (pairParity a b).natAbs) c.multiplier := by
  have hn' : realRank (pre ++ .character b :: .character a :: post) = n := by
    simpa [dc] using realRank_dc_mid hn
  have hs : IsSymmetric (pairParity b a) (sigma0 b a) c.multiplier := by
    simpa only [sigma0, RealInducedSwapGeneric.pairParity_comm b a] using
      c.symmetric (pairParity_eq a b)
  have hh := data_swap (c := b) (d := a) (pre := pre) (post := post) hn' hs
  simpa only [dc, sigma0, RealInducedSwapGeneric.pairParity_comm b a,
    List.append_assoc, List.cons_append, List.nil_append] using hh

def crossing
    (hn : realRank (pre ++ .character a :: .character b :: post) = n)
    (c : Choice (pairParity a b)) :
    KF n (pre ++ .character a :: .character b :: post) →ₗ[ℂ]
      KF n (pre ++ .character b :: .character a :: post) :=
  blockFrobMap (data hn c)

def swap0 (a b c : RealCharacterData) (A : Choice (pairParity a b)) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source b a c) :=
  crossing (n := 3) (pre := []) (post := [.character c]) (a := a) (b := b) rfl A

def swap1 (a b c : RealCharacterData) (B : Choice (pairParity b c)) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source a c b) :=
  crossing (n := 3) (pre := [.character a]) (post := []) (a := b) (b := c) rfl B

def leftWord (a b c : RealCharacterData) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source c b a) :=
  ((swap0 b c a B).comp (swap1 b a c C)).comp (swap0 a b c A)

def rightWord (a b c : RealCharacterData) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    KF 3 (source a b c) →ₗ[ℂ] KF 3 (source c b a) :=
  ((swap1 c a b A).comp (swap0 a c b C)).comp (swap1 a b c B)

def leftOperator {ε η κ : ℤ} (N : ℕ) (A : Choice ε) (B : Choice η) (C : Choice κ) :
    Module.End ℂ (degreeLE 3 N) :=
  B.operator N (p := 0) (by decide) * C.operator N (p := 1) (by decide) *
    A.operator N (p := 0) (by decide)

def rightOperator {ε η κ : ℤ} (N : ℕ) (A : Choice ε) (B : Choice η) (C : Choice κ) :
    Module.End ℂ (degreeLE 3 N) :=
  A.operator N (p := 1) (by decide) * C.operator N (p := 0) (by decide) *
    B.operator N (p := 1) (by decide)

theorem leftWord_action (N : ℕ) (a b c : RealCharacterData) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    CompactAction N (leftWord a b c A B C) (leftOperator N A B C) :=
  CompactAction.comp (frob_action N (data (n := 3) (pre := []) (post := [.character c])
      (a := a) (b := b) rfl A))
    (CompactAction.comp (frob_action N (data (n := 3) (pre := [.character b]) (post := [])
        (a := a) (b := c) rfl C))
      (frob_action N (data (n := 3) (pre := []) (post := [.character a])
        (a := b) (b := c) rfl B)))

theorem rightWord_action (N : ℕ) (a b c : RealCharacterData) (A : Choice (pairParity a b))
    (B : Choice (pairParity b c)) (C : Choice (pairParity a c)) :
    CompactAction N (rightWord a b c A B C) (rightOperator N A B C) :=
  CompactAction.comp (frob_action N (data (n := 3) (pre := [.character a]) (post := [])
      (a := b) (b := c) rfl B))
    (CompactAction.comp (frob_action N (data (n := 3) (pre := []) (post := [.character b])
        (a := a) (b := c) rfl C))
      (frob_action N (data (n := 3) (pre := [.character c]) (post := [])
        (a := a) (b := b) rfl A)))

end ActualMaps

section Clearing

variable {ε η κ : ℤ} (A : Choice ε) (B : Choice η) (C : Choice κ)
  (hε : ε = 0 ∨ ε = 1) (hη : η = 0 ∨ η = 1) (hκ : κ = 0 ∨ κ = 1)
  (hparam : C.parameter = A.parameter + B.parameter)

include hε hη hκ hparam

theorem leftNumerator_eq (N : ℕ) (hA : A.cutoff ≤ N) (hB : B.cutoff ≤ N)
    (hC : C.cutoff ≤ N) :
    RealRationalCompactFamilies.leftNumerator N ε η κ ![A.parameter, B.parameter] =
      (B.scale N * C.scale N * A.scale N) • leftOperator N A B C := by
  unfold RealRationalCompactFamilies.leftNumerator leftOperator
  rw [B.compactCleared_eq hη N hB (p := 0) (by decide) (X 1) _ (by simp),
    C.compactCleared_eq hκ N hC (p := 1) (by decide) (X 0 + X 1) _
      (by simpa using hparam.symm),
    A.compactCleared_eq hε N hA (p := 0) (by decide) (X 0) _ (by simp)]
  simp only [smul_mul_smul]

theorem rightNumerator_eq (N : ℕ) (hA : A.cutoff ≤ N) (hB : B.cutoff ≤ N)
    (hC : C.cutoff ≤ N) :
    RealRationalCompactFamilies.rightNumerator N ε η κ ![A.parameter, B.parameter] =
      (B.scale N * C.scale N * A.scale N) • rightOperator N A B C := by
  unfold RealRationalCompactFamilies.rightNumerator rightOperator
  rw [A.compactCleared_eq hε N hA (p := 1) (by decide) (X 0) _ (by simp),
    C.compactCleared_eq hκ N hC (p := 0) (by decide) (X 0 + X 1) _
      (by simpa using hparam.symm),
    B.compactCleared_eq hη N hB (p := 1) (by decide) (X 1) _ (by simp)]
  simp only [smul_mul_smul]
  congr 1
  ring

end Clearing

open RealGenericCharacterBraidReduction in
/-- All mixed words retain the explicit full polynomial braid premise. -/
theorem braid_of_polynomial (hPoly : ∀ N n m, PolynomialBraid N n m)
    (a b c : RealCharacterData) (A : Choice (pairParity a b)) (B : Choice (pairParity b c))
    (C : Choice (pairParity a c)) (hparam : C.parameter = A.parameter + B.parameter) :
    leftWord a b c A B C = rightWord a b c A B C := by
  have hε := pairParity_eq a b
  have hη := pairParity_eq b c
  have hκ := pairParity_eq a c
  have hε0 : 0 ≤ pairParity a b := by rcases hε with h | h <;> omega
  have hη0 : 0 ≤ pairParity b c := by rcases hη with h | h <;> omega
  have hκ0 : 0 ≤ pairParity a c := by rcases hκ with h | h <;> omega
  apply LinearMap.ext
  intro f
  obtain ⟨N0, hf0⟩ :=
    RealPolynomialFourierPropagation.exists_degreeLE (RealBlockJacquet.continuous_coe f) f.2.2
  let N := max N0 (max A.cutoff (max B.cutoff C.cutoff))
  have hA : A.cutoff ≤ N := by dsimp [N]; omega
  have hB : B.cutoff ≤ N := by dsimp [N]; omega
  have hC : C.cutoff ≤ N := by dsimp [N]; omega
  have hf : restrictLinear 3 (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ degreeLE 3 N :=
    degreeLE_mono (le_max_left _ _) hf0
  have hgrid : ∀ z ∈ Set.pi Set.univ (grid (pairParity a b) (pairParity b c)),
      ∀ v ∈ sourceVectors N a b c,
        RealRationalCompactFamilies.leftWord N (pairParity a b) (pairParity b c) (pairParity a c) z v =
          RealRationalCompactFamilies.rightWord N (pairParity a b) (pairParity b c) (pairParity a c) z v := by
    intro z hz v hv
    obtain ⟨g, hg, rfl⟩ := hv
    exact CompactAction.operator_eq
      (RealGenericCompactCharacter.leftWord_action N a b c z)
      (RealGenericCompactCharacter.rightWord_action N a b c z)
      (grid_braid_of_polynomial hPoly a b c z hz) g hg
  have heq := threeCrossing_numerators_eq_of_grid N hε0 hη0 hκ0
    (sourceVectors N a b c) hgrid ![A.parameter, B.parameter]
    (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hf) ⟨f, hf, rfl⟩
  rw [leftNumerator_eq A B C hε hη hκ hparam N hA hB hC,
    rightNumerator_eq A B C hε hη hκ hparam N hA hB hC] at heq
  have hs : B.scale N * C.scale N * A.scale N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (B.scale_ne_zero hη N) (C.scale_ne_zero hκ N))
      (A.scale_ne_zero hε N)
  have hh := congrArg (fun v : degreeLE 3 N => (B.scale N * C.scale N * A.scale N)⁻¹ • v) heq
  have hop : leftOperator N A B C (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hf) =
      rightOperator N A B C (vector (f : Langlands.GeneralLinear 3 ℝ → ℂ) hf) := by
    simpa only [LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hs, one_smul] using hh
  exact CompactAction.eq_apply (leftWord_action N a b c A B C)
    (rightWord_action N a b c A B C) f hf hop

end Langlands.Archimedean.RealCanonicalCharacterBraid

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealCharacterPair RealCanonicalCharacterBraid

/-- Canonical mixed generic, binomial and tail words under the explicit full polynomial premise. -/
def RealCanonicalCharacterBraidStatement : Prop :=
  (∀ N n m, RealGenericCharacterBraidReduction.PolynomialBraid N n m) →
    ∀ (a b c : RealCharacterData) (A : Choice (pairParity a b))
      (B : Choice (pairParity b c)) (C : Choice (pairParity a c)),
      C.parameter = A.parameter + B.parameter →
        leftWord a b c A B C = rightWord a b c A B C

theorem realCanonicalCharacterBraid : RealCanonicalCharacterBraidStatement :=
  fun hPoly a b c A B C hparam => braid_of_polynomial hPoly a b c A B C hparam

end Langlands.Archimedean
