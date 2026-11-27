import Langlands.BushnellKutzko.SplitTypeExistenceStatement
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof

/-! # The four steps of the proof of BK93 (8.1.5)

Four propositions, one for each branch of the proof of BK93 (8.1.5), and the
deduction of `SplitTypeExistenceStatement` from them. The propositions are not proved here.

In the docstrings, as in BK93, `N` is the ambient rank (the Lean variable `n`) and a stratum is
written `[𝔄, n, m, β]`, where the level `n` is the field `S.n` of the stratum `S`.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ uρ

section Containment

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- `π` contains the character `χ` of a subgroup `U` of `Aut_F(F^N)`: some nonzero vector
transforms by `χ` under `U`, which acts through the identification `toLin` of `GL_N(F)` with
`Aut_F(F^N)`. -/
def ContainsAutCharacter (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    {U : Subgroup (Module.End F (Fin n → F))ˣ} (χ : U →* ℂˣ) : Prop :=
  ∃ v : π, v ≠ 0 ∧ ∀ u : U,
    π.representation (Matrix.GeneralLinearGroup.toLin.symm (u : (Module.End F (Fin n → F))ˣ)) v =
      (χ u : ℂ) • v

/-- `π` has a nonzero vector fixed by `U^1(𝔄)`, for the hereditary order `𝔄` of `L`. -/
def HasUnitFiltrationOneFixedVector (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (L : LatticeChain 𝒪[F] F (Fin n → F)) : Prop :=
  ContainsAutCharacter π (1 : L.unitFiltration 1 →* ℂˣ)

/-- `π` contains a simple character of the stratum `S = [𝔄, n, m, β]`: `S` is simple, `m ≥ 0`,
and for some defining sequence of `S` there is `θ ∈ C(𝔄, m, β)`, a character of
`H^{m+1}(β, 𝔄)`, contained in `π`. -/
def ContainsSimpleCharacter (ψF : AddChar F ℂ) (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (S : Stratum 𝒪[F] F (Fin n → F)) : Prop :=
  S.IsSimple ∧ 0 ≤ S.r ∧ ∃ q : S.DefiningSequenceChoice,
    ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail S.r.toNat, ContainsAutCharacter π θ

end Containment

/-- **BK93 (8.1.5), level zero (printed pp. 267–268).** An irreducible smooth representation
of `GL_N(F)` with a nonzero vector fixed by `U^1(𝔄)`, for some hereditary order `𝔄`, contains a
simple type or a split type of level `(0, 0)`. -/
def LevelZeroTypeContainmentStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)), π.IsIrreducible →
    (∃ L : LatticeChain 𝒪[F] F (Fin n → F), HasUnitFiltrationOneFixedVector π L) →
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      (IsGLSimpleType (n := n) ψF ρ ∨
        IsLevelZeroSplitType (V := Fin n → F) (glRepresentationToAut ρ))

/-- **BK93 (8.1.5), positive level (printed p. 268).** An irreducible smooth representation of
`GL_N(F)` with no nonzero vector fixed by `U^1(𝔄)`, for every hereditary order `𝔄`, contains a
split type of level `(x, x)` or a simple character of a simple stratum. -/
def PositiveLevelInitialStepStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)), π.IsIrreducible →
    (∀ L : LatticeChain 𝒪[F] F (Fin n → F), ¬ HasUnitFiltrationOneFixedVector π L) →
    (∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
        ∃ x : ℚ, IsDiagonalPositiveSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ)) ∨
      ∃ S : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π S

/-- **BK93 (8.1.5), simple characters of depth zero (printed pp. 268–270).** An irreducible
smooth representation of `GL_N(F)` containing a simple character `θ ∈ C(𝔄, 0, β)` of a simple
stratum `[𝔄, n, 0, β]` contains a simple type or a split type of level `(x, 0)`. -/
def ZeroDepthCharacterStepStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)), π.IsIrreducible →
    ∀ S : Stratum 𝒪[F] F (Fin n → F), S.r = 0 → ContainsSimpleCharacter ψF π S →
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      (IsGLSimpleType (n := n) ψF ρ ∨
        ∃ x : ℚ, IsPositiveZeroSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ))

/-- **BK93 (8.1.5), simple characters of positive depth (printed pp. 270–275).** An irreducible
smooth representation of `GL_N(F)` containing a simple character `θ ∈ C(𝔄, m, β)` of a simple
stratum `[𝔄, n, m, β]` with `m ≥ 1` contains a split type of level `(x, y)` with `y > 0`, or a
simple character `θ' ∈ C(𝔄', m', β')` of a simple stratum `[𝔄', n', m', β']` with
`m' / e(𝔄') < m / e(𝔄)`. -/
def PositiveDepthCharacterStepStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)), π.IsIrreducible →
    ∀ S : Stratum 𝒪[F] F (Fin n → F), 0 < S.r → ContainsSimpleCharacter ψF π S →
    (∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
        ∃ x y : ℚ,
          IsUnequalPositiveSplitType (V := Fin n → F) ψF x y (glRepresentationToAut ρ)) ∨
      ∃ T : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π T ∧
        T.r * (S.chain.period : ℤ) < S.r * (T.chain.period : ℤ)

/-- The four steps imply BK93 (8.1.5), at the same universes. -/
def SplitTypeExistenceReductionStatement : Prop :=
  LevelZeroTypeContainmentStatement.{uF, uπ, uρ} →
  PositiveLevelInitialStepStatement.{uF, uπ, uρ} →
  ZeroDepthCharacterStepStatement.{uF, uπ, uρ} →
  PositiveDepthCharacterStepStatement.{uF, uπ, uρ} →
  SplitTypeExistenceStatement.{uF, uπ, uρ}

/-- The depth `m / e(𝔄)` of a stratum, scaled by `N!` to a natural number. For lattice chains in
`F^N` the period divides `N!`. -/
private def scaledDepth (n : ℕ) {F : Type uF} [Field F] [ValuativeRel F]
    (S : Stratum 𝒪[F] F (Fin n → F)) : ℕ :=
  S.r.toNat * (n.factorial / S.chain.period)

private theorem scaledDepth_lt {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} {S T : Stratum 𝒪[F] F (Fin n → F)}
    (hT : 0 ≤ T.r) (hS : 0 ≤ S.r)
    (hlt : T.r * (S.chain.period : ℤ) < S.r * (T.chain.period : ℤ)) :
    scaledDepth n T < scaledDepth n S := by
  have hdT : T.chain.period ∣ n.factorial :=
    Nat.dvd_factorial T.chain.period_pos (by simpa using T.chain.period_le_card)
  have hdS : S.chain.period ∣ n.factorial :=
    Nat.dvd_factorial S.chain.period_pos (by simpa using S.chain.period_le_card)
  obtain ⟨a, ha⟩ := hdT
  obtain ⟨b, hb⟩ := hdS
  have hpT := T.chain.period_pos
  have hpS := S.chain.period_pos
  have hf := Nat.factorial_pos n
  unfold scaledDepth
  rw [ha, Nat.mul_div_cancel_left _ hpT]
  rw [ha] at hb
  rw [hb, Nat.mul_div_cancel_left _ hpS]
  -- `T.r * eS < S.r * eT` and `eT * a = eS * b` give `T.r * a < S.r * b`.
  have hpos : (0 : ℤ) < (T.chain.period : ℤ) * (S.chain.period : ℤ) := by positivity
  have hab : (T.chain.period : ℤ) * a = (S.chain.period : ℤ) * b := by exact_mod_cast hb
  have key : (T.r.toNat : ℤ) * a * ((T.chain.period : ℤ) * (S.chain.period : ℤ)) <
      (S.r.toNat : ℤ) * b * ((T.chain.period : ℤ) * (S.chain.period : ℤ)) := by
    rw [Int.toNat_of_nonneg hT, Int.toNat_of_nonneg hS]
    have ha0 : (0 : ℤ) < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; simp at ha; omega
      · exact_mod_cast h
    calc T.r * a * ((T.chain.period : ℤ) * (S.chain.period : ℤ))
        = (T.r * S.chain.period) * ((T.chain.period : ℤ) * a) := by ring
      _ < (S.r * T.chain.period) * ((T.chain.period : ℤ) * a) := by
          apply mul_lt_mul_of_pos_right hlt; positivity
      _ = (S.r * T.chain.period) * ((S.chain.period : ℤ) * b) := by rw [hab]
      _ = S.r * b * ((T.chain.period : ℤ) * (S.chain.period : ℤ)) := by ring
  have := lt_of_mul_lt_mul_right key hpos.le
  exact_mod_cast this

/-- **BK93 (8.1.5) from its four steps.** -/
theorem splitTypeExistenceReduction : SplitTypeExistenceReductionStatement.{uF, uπ, uρ} := by
  intro h₁ h₂ h₃ h₄ F _ _ _ _ n hn ψF hψ π hπ hnone
  by_cases h₀ : ∃ L : LatticeChain 𝒪[F] F (Fin n → F), HasUnitFiltrationOneFixedVector π L
  · obtain ⟨K, ρ, hc, hs | hs⟩ := h₁ F n hn ψF hψ π hπ h₀
    · exact absurd ⟨K, ρ, hs, hc⟩ hnone
    · exact ⟨K, ρ, Or.inr (Or.inl hs), hc⟩
  · simp only [not_exists] at h₀
    rcases h₂ F n hn ψF hψ π hπ h₀ with ⟨K, ρ, hc, x, hs⟩ | ⟨S, hS⟩
    · exact ⟨K, ρ, Or.inl (Or.inl ⟨x, hs⟩), hc⟩
    · -- Descent on the scaled depth of a contained simple character.
      have key : ∀ N : ℕ, ∀ S : Stratum 𝒪[F] F (Fin n → F), scaledDepth n S = N →
          ContainsSimpleCharacter ψF π S →
          ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K),
            IsGLSplitType (n := n) ψF ρ ∧ ContainsType π ρ := by
        intro N
        induction N using Nat.strong_induction_on with
        | _ N ih =>
          intro S hN hS
          rcases (show S.r = 0 ∨ 0 < S.r by have := hS.2.1; omega) with hr | hr
          · obtain ⟨K, ρ, hc, hs | ⟨x, hs⟩⟩ := h₃ F n hn ψF hψ π hπ S hr hS
            · exact absurd ⟨K, ρ, hs, hc⟩ hnone
            · exact ⟨K, ρ, Or.inr (Or.inr ⟨x, hs⟩), hc⟩
          · rcases h₄ F n hn ψF hψ π hπ S hr hS with ⟨K, ρ, hc, x, y, hs⟩ | ⟨T, hT, hlt⟩
            · exact ⟨K, ρ, Or.inl (Or.inr ⟨x, y, hs⟩), hc⟩
            · exact ih _ (hN ▸ scaledDepth_lt hT.2.1 hS.2.1 hlt) T rfl hT
      exact key _ S rfl hS

end Langlands.BushnellKutzko
