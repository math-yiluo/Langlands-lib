import Langlands.Representation.Archimedean.RealBlockNonvanishing
import Langlands.Representation.Archimedean.RealTiedIrreducible

/-!
# The Langlands quotient of a Langlands-ordered real principal series (character blocks)

For a list of character blocks of `GL_1(ℝ)` in Langlands order (real parts of the exponents
non-increasing, ties allowed), the `O(n)`-finite functions of the standard module have a largest
proper `(𝔤, K)`-submodule, assuming the two block statements `RealBlockChartIntegrableStatement`,
`RealBlockParabolicIntegrationStatement` and the tempered irreducibility statement
`RealTemperedStandardIrreducibleStatement`. The tie classes of the exponents form a block
decomposition; every proper submodule lies in the kernel of the block Jacquet functional
(`RealBlockFunctional`), which is not identically zero (`RealBlockNonvanishing`).
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealCharacterLanglandsQuotient

open PartialJacquet StrictPrincipalSeriesQuotient RealBlockJacquet RealBlockFunctional
  RealStrictCharacterLanglandsQuotient GramFormula Langlands.GeneralLinear
  Langlands.LocalFactor.Archimedean

/-- **Tie classes.** If the real parts of `e_0, …, e_{n-1}` are non-increasing, the maximal
classes of equal real parts form a block decomposition `ks` of `n` with `BlockOrdered ks e`. -/
theorem exists_blocks (e : ℕ → ℂ) : ∀ n : ℕ, (∀ l : ℕ, l + 1 < n → (e (l + 1)).re ≤ (e l).re) →
    ∃ ks : List ℕ, dim ks = n ∧ BlockOrdered ks e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hord
    rcases n with _ | m
    · exact ⟨[], rfl, trivial⟩
    · classical
      have hex : ∃ a, a ≤ m ∧ ∀ j, a ≤ j → j ≤ m → (e j).re = (e m).re :=
        ⟨m, le_rfl, fun j h1 h2 => by rw [le_antisymm h2 h1]⟩
      have hspec := Nat.find_spec hex
      obtain ⟨ks', hdim, hks'⟩ := ih (Nat.find hex) (by omega)
        (fun l hl => hord l (by omega))
      refine ⟨(m - Nat.find hex) :: ks', ?_, ?_⟩
      · change dim ks' + (m - Nat.find hex + 1) = m + 1
        rw [hdim]
        omega
      · show IsBlockDominant e (dim ks') (m - Nat.find hex) ∧ BlockOrdered ks' e
        refine ⟨?_, hks'⟩
        rw [hdim]
        refine ⟨fun j hj => ?_, fun l hl => hord l (by omega), fun l hl => ?_⟩
        · rw [hspec.2 (Nat.find hex + j) (by omega) (by omega),
            hspec.2 (Nat.find hex) le_rfl hspec.1]
        · have hmin := Nat.find_min hex (show l < Nat.find hex by omega)
          have hle := hord l (by omega)
          rcases lt_or_eq_of_le hle with h | h
          · exact h
          · exfalso
            refine hmin ⟨by omega, fun j hj1 hj2 => ?_⟩
            rcases eq_or_lt_of_le hj1 with hj | hj
            · rw [← hj, ← h, hl]
              exact hspec.2 _ le_rfl hspec.1
            · exact hspec.2 j (by omega) hj2

/-- The exponents of a Langlands-ordered list of character blocks are non-increasing in real
part. -/
theorem exponent_ord : ∀ {ds : List RealBlock}, IsCharacterList ds → IsRealLanglandsOrdered ds →
    ∀ l : ℕ, l + 1 < realRank ds →
      (realPositionExponent ds (l + 1)).re ≤ (realPositionExponent ds l).re
  | [], _, _ => fun l hl => by simp [realRank] at hl
  | .induced d :: _, h, _ => by
      obtain ⟨c, hc⟩ := h _ (List.mem_cons_self ..)
      cases hc
  | .character d :: ds, h, hs => by
      have h' : IsCharacterList ds := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hs' : IsRealLanglandsOrdered ds := (List.pairwise_cons.mp hs).2
      have ih := exponent_ord h' hs'
      intro l hl
      rw [realRank_cons] at hl
      simp only [RealBlock.rank] at hl
      cases l with
      | zero =>
          cases ds with
          | nil => simp [realRank] at hl
          | cons b ds'' =>
              obtain ⟨c, rfl⟩ := h' b (List.mem_cons_self ..)
              have hrel := (List.pairwise_cons.mp hs).1 _ (List.mem_cons_self ..)
              simpa [realPositionExponent, realBlockExponent] using hrel
      | succ l =>
          simp only [realPositionExponent]
          exact ih l (by omega)

/-- **The largest proper submodule.** For a block decomposition with `BlockOrdered ks e` and
signed-power characters with signs `(−1)^{p_l}`, the sum of all proper `(𝔤, K)`-stable subspaces
of the `O(n)`-finite principal series is proper and `(𝔤, K)`-stable. -/
theorem isProperGKStable_largestProper_block (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) {ks : List ℕ}
    {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ) (hχ : IsSignedPower χ e)
    (hp : ∀ l : ℕ, χ l (-1) = (-1) ^ p l) (hks : BlockOrdered ks e) :
    IsProperGKStable (dim ks) χ (largestProper (dim ks) χ) := by
  have hker : largestProper (dim ks) χ ≤ jacKernel hT1 ks p hχ hp hks := iSup_le fun W => by
    obtain ⟨⟨hWX, hWK, hWD⟩, f, hf, hfW⟩ := W.2
    exact jac_eq_zero_of_proper hT1 hT3 hirr p hχ hp hks _ hWX hWK hWD hf hfW
  refine ⟨isGKStable_largestProper, ?_⟩
  obtain ⟨av, L, -, hne⟩ := RealBlockNonvanishing.exists_jac_testVector_ne_zero hT1 ks p hχ hp hks
  exact ⟨_, RealBlockNonvanishing.testVector_mem hχ hp av L, fun hfR => hne (hker hfR).2⟩

end RealCharacterLanglandsQuotient

/-- **Statement (Langlands quotient of a Langlands-ordered real principal series), assuming
`RealBlockChartIntegrableStatement`, `RealBlockParabolicIntegrationStatement` and
`RealTemperedStandardIrreducibleStatement`.** Let `ds` be a list of real character blocks
(characters `sgn^ε |·|^t` of `GL_1(ℝ)`) of total rank `n` in Langlands order (real parts of the
exponents non-increasing). Then the `O(n)`-finite functions of the standard module of `ds` have a
largest proper `(𝔤, K)`-submodule. -/
def RealCharacterLanglandsQuotientStatement : Prop :=
  RealBlockChartIntegrableStatement → RealBlockParabolicIntegrationStatement →
  RealTemperedStandardIrreducibleStatement →
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    RealStrictCharacterLanglandsQuotient.IsCharacterList ds → IsRealLanglandsOrdered ds →
    ∃ R : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R ∧ R ≠ ⊤ ∧
        ∀ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
          IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ → W ≤ R

open PartialJacquet StrictPrincipalSeriesQuotient RealBlockFunctional
  RealStrictCharacterLanglandsQuotient RealCharacterLanglandsQuotient GramFormula
  Langlands.GeneralLinear Langlands.LocalFactor.Archimedean in
theorem realCharacterLanglandsQuotient : RealCharacterLanglandsQuotientStatement := by
  intro hT1 hT3 htemp n ds hn hchar hord
  set χ := realPositionCharacter ds
  have hχ := isSignedPower ds
  obtain ⟨p, hp⟩ := exists_signs ds
  obtain ⟨ks, hdim, hks⟩ := exists_blocks (realPositionExponent ds) (realRank ds)
    (exponent_ord hchar hord)
  have hn' : dim ks = n := hdim.trans hn
  subst hn'
  have hprop := isProperGKStable_largestProper_block hT1 hT3 (realTiedIrreducible htemp) p hχ hp hks
  set n := dim ks with hndef
  obtain ⟨⟨hRX, hRK, hRD⟩, f₀, hf₀, hf₀R⟩ := hprop
  have hS : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
    rw [realStandardModule_eq hchar]
  set S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) with hSdef
  refine ⟨(largestProper n χ).comap S.subtype, ⟨fun κ f hf => ?_, fun Y => ?_⟩, ?_,
    fun W hW hW' => ?_⟩
  · change ((realStandardRep n ds κ f : S) : Langlands.GeneralLinear n ℝ → ℂ) ∈ largestProper n χ
    rw [realStandardRep_apply_coe]
    exact hRK _ κ.2 _ hf
  · induction Y using TensorProduct.inductionOn with
    | tmul c X =>
        intro w hw
        have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, map_smul, LinearMap.smul_apply]
        refine Submodule.smul_mem _ c ?_
        change ((realStandardLie n ds (1 ⊗ₜ X) w : S) : Langlands.GeneralLinear n ℝ → ℂ) ∈
          largestProper n χ
        rw [realStandardLie_one_tmul_apply_coe]
        exact hRD X _ hw
    | add Y Z hY hZ =>
        intro w hw
        rw [map_add, LinearMap.add_apply]
        exact add_mem (hY w hw) (hZ w hw)
  · intro htop
    have hf₀S : f₀ ∈ S := hS ▸ hf₀
    have : (⟨f₀, hf₀S⟩ : S) ∈ (largestProper n χ).comap S.subtype := by
      rw [htop]
      trivial
    exact hf₀R this
  · obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : S, g ∉ W := by
      by_contra hcon
      exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
    have hWX : W.map S.subtype ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
      rintro _ ⟨w, -, rfl⟩
      exact hS ▸ w.2
    have hprop : IsProperGKStable n χ (W.map S.subtype) := by
      refine ⟨⟨hWX, fun k hk _ hw => ?_, fun X _ hw => ?_⟩, g, hS ▸ hgS, ?_⟩
      · obtain ⟨w, hwW, rfl⟩ := hw
        refine ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w,
          hW.1 _ w hwW, ?_⟩
        change ((realStandardRep n ds _ w : S) : Langlands.GeneralLinear n ℝ → ℂ) = _
        rw [realStandardRep_apply_coe]
        have hku : Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
            Matrix.unitaryGroup (Fin n) ℝ) = k := Units.ext rfl
        rw [hku]
        rfl
      · obtain ⟨w, hwW, rfl⟩ := hw
        exact ⟨realStandardLie n ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
          realStandardLie_one_tmul_apply_coe n ds X w⟩
      · rintro ⟨w, hwW, hw⟩
        apply hgW
        have : w = ⟨g, hgS⟩ := Subtype.ext hw
        rw [← this]
        exact hwW
    intro w hw
    exact le_largestProper hprop ⟨w, hw, rfl⟩

end Langlands.Archimedean
