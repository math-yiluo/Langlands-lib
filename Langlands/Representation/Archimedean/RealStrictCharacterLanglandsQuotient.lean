import Langlands.Representation.Archimedean.StrictPrincipalSeriesQuotient
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# The Langlands quotient of a strictly ordered real principal series
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealStrictCharacterLanglandsQuotient

open PartialJacquet StrictPrincipalSeriesQuotient GramFormula Langlands.GeneralLinear
  Langlands.LocalFactor.Archimedean

/-- All blocks of `ds` are characters of `GL_1(ℝ)`. -/
def IsCharacterList (ds : List RealBlock) : Prop := ∀ b ∈ ds, ∃ c, b = RealBlock.character c

/-- The real parts of the exponents of the blocks of `ds` strictly decrease. -/
def IsStrictlyOrdered (ds : List RealBlock) : Prop :=
  ds.Pairwise fun x y => realBlockExponent y < realBlockExponent x

theorem realInducedBlockAt_eq_none : ∀ {ds : List RealBlock}, IsCharacterList ds →
    ∀ p, realInducedBlockAt ds p = none
  | [], _, _ => rfl
  | .induced d :: _, h, _ => by
      obtain ⟨c, hc⟩ := h _ (List.mem_cons_self ..)
      cases hc
  | .character _ :: _, _, 0 => rfl
  | .character _ :: ds, h, p + 1 =>
      realInducedBlockAt_eq_none (ds := ds) (fun b hb => h b (List.mem_cons_of_mem _ hb)) p

theorem realStandardModule_eq {n : ℕ} {ds : List RealBlock} (h : IsCharacterList ds) :
    realStandardModule n ds = principalSeries ℝ n (realPositionCharacter ds) := by
  ext f
  constructor
  · exact fun hf => hf.1
  · intro hf
    refine ⟨hf, fun p d hd => ?_⟩
    rw [realInducedBlockAt_eq_none h p] at hd
    cases hd

theorem realPositionCharacter_one : ∀ (ds : List RealBlock) (l : ℕ),
    realPositionCharacter ds l 1 = 1
  | [], _ => rfl
  | .character d :: _, 0 => by simp [realPositionCharacter]
  | .character _ :: ds, l + 1 => realPositionCharacter_one ds l
  | .induced d :: _, 0 => by simp [realPositionCharacter, realInducedFirstCharacter]
  | .induced d :: _, 1 => by simp [realPositionCharacter, realInducedSecondCharacter]
  | .induced _ :: ds, l + 2 => realPositionCharacter_one ds l

theorem neg_one_pow_eq (k : ℕ) : ((-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1) := by
  rcases Nat.even_or_odd k with hk | hk
  · exact Or.inl hk.neg_one_pow
  · exact Or.inr hk.neg_one_pow

theorem realPositionCharacter_neg_one : ∀ (ds : List RealBlock) (l : ℕ),
    realPositionCharacter ds l (-1) = 1 ∨ realPositionCharacter ds l (-1) = -1
  | [], _ => Or.inl rfl
  | .character d :: _, 0 => by
      simp only [realPositionCharacter]
      rw [d.character_eq]
      simpa using neg_one_pow_eq d.parity.val
  | .character _ :: ds, l + 1 => realPositionCharacter_neg_one ds l
  | .induced d :: _, 0 => by
      simp only [realPositionCharacter, realInducedFirstCharacter]
      simpa using neg_one_pow_eq (d.weight.natAbs + 1)
  | .induced d :: _, 1 => by
      simp [realPositionCharacter, realInducedSecondCharacter]
  | .induced _ :: ds, l + 2 => realPositionCharacter_neg_one ds l

theorem isSignedPower (ds : List RealBlock) :
    IsSignedPower (realPositionCharacter ds) (realPositionExponent ds) where
  eq := realPositionCharacter_eq_signUnit_mul ds
  one := realPositionCharacter_one ds
  norm_neg_one l := by
    rcases realPositionCharacter_neg_one ds l with h | h <;> simp [h]

theorem exists_signs (ds : List RealBlock) :
    ∃ p : ℕ → ℕ, ∀ l, realPositionCharacter ds l (-1) = (-1) ^ p l := by
  classical
  refine ⟨fun l => if realPositionCharacter ds l (-1) = 1 then 0 else 1, fun l => ?_⟩
  rcases realPositionCharacter_neg_one ds l with h | h
  · simp [h]
  · have : realPositionCharacter ds l (-1) ≠ 1 := by
      rw [h]
      norm_num
    simp [h]

theorem isStrictlyDominant : ∀ {ds : List RealBlock}, IsCharacterList ds → IsStrictlyOrdered ds →
    IsStrictlyDominant (realPositionExponent ds) (realRank ds - 1)
  | [], _, _ => fun l hl => by simp [realRank] at hl
  | .induced d :: _, h, _ => by
      obtain ⟨c, hc⟩ := h _ (List.mem_cons_self ..)
      cases hc
  | .character d :: ds, h, hs => by
      have h' : IsCharacterList ds := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hs' : IsStrictlyOrdered ds := (List.pairwise_cons.mp hs).2
      have ih := isStrictlyDominant h' hs'
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

/-- **Statement (Langlands quotient of a strictly ordered real principal series).** Let `ds` be
a list of real character blocks (characters `sgn^ε |·|^t` of `GL_1(ℝ)`) of total rank `n`,
whose exponents have strictly decreasing real parts. Then the `O(n)`-finite functions of the
standard module of `ds` have a largest proper `(𝔤, K)`-submodule. -/
def RealStrictCharacterLanglandsQuotientStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsCharacterList ds → IsStrictlyOrdered ds →
    ∃ R : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) R ∧ R ≠ ⊤ ∧
        ∀ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
          IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ → W ≤ R

theorem realStrictCharacterLanglandsQuotient : RealStrictCharacterLanglandsQuotientStatement := by
  intro n ds hn hchar hord
  subst hn
  set n := realRank ds
  set χ := realPositionCharacter ds
  have hχ := isSignedPower ds
  have he := isStrictlyDominant hchar hord
  obtain ⟨p, hp⟩ := exists_signs ds
  obtain ⟨⟨⟨hRX, hRK, hRD⟩, f₀, hf₀, hf₀R⟩, -⟩ := isProperGKStable_largestProper hχ he hp
  have hS : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
    rw [realStandardModule_eq hchar]
  set S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) with hSdef
  refine ⟨(largestProper n χ).comap S.subtype, ⟨fun κ f hf => ?_, fun Y => ?_⟩, ?_, fun W hW hW' => ?_⟩
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

end RealStrictCharacterLanglandsQuotient

end Langlands.Archimedean
