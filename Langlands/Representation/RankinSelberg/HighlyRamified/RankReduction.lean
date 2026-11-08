import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.GammaMultiplicativityProof
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistGamma
import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.Representation.Whittaker.FunctionalExistence

/-!
# Reduction of gamma stability to adjacent ranks

Jacquet and Shalika 1985, §4.3 (printed page 327): stability for candidates of
rank `r + 1` against tests of every rank follows from the adjacent case (test
rank `r`) and the rank-one case. A test of smaller rank is induced, together with
an unramified character `μ_z`, to a test of one more rank; candidates of rank at
most the test rank are induced in the same way to candidates of one more rank.
Multiplicativity of gamma factors (`gammaMultiplicativity`) splits off the
factor of `μ_z`, which is cancelled. The induced representation must stay
generic; this holds for all but finitely many `z`, the hypothesis
`PairInductionGenericity`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime]

/-- The exponents of the block sizes `(n + 1, 1)`. -/
abbrev pairSizes (n : ℕ) : Fin 2 → ℕ := ![n, 0]

theorem pairSizes_sum (n : ℕ) : ∑ i, (pairSizes n i + 1) = n + 1 + 1 := by
  simp [Fin.sum_univ_two]

section Family

variable (F : PadicField.{uF} p) {n : ℕ}

/-- The two blocks `(A, B)` of the standard parabolic of type `(n + 1, 1)`. -/
def pairFamily
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier)) :
    letI := F.canonicalTopologicalData.topology
    ∀ i : Fin 2, SmoothRep.{0, uF, uX} ℂ
      (Langlands.GeneralLinear (pairSizes n i + 1) F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  Fin.cases A (Fin.cases B finZeroElim)

/-- The normalized induction `A × B` of `GL_(n+1) × GL_1` to `GL_(n+2)`. -/
abbrev pairInduced
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier)) :=
  letI := F.canonicalTopologicalData.topology
  F.canonicalNormalizedProductInduced (succBlockShape (pairSizes n) (pairSizes_sum n))
    (fun i => (pairFamily F A B i).representation)

/-- The rank-one unramified character `x ↦ z ^ ord(x)` on the lifted line. -/
def unramifiedRankOne (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier) :=
  letI := F.canonicalTopologicalData.topology
  SmoothRep.of
    (rankOneExtensionCharacter.{uF, uX} F
      (F.canonicalTopologicalData.unramifiedCharacterContinuous z))
    ((padicUnitaryAdditiveCharacterExists F F.canonicalTopologicalData).elim fun ψ =>
      rankOneExtensionCharacter_isSmooth F ψ _)

end Family

/-- The genericity input of the reduction: for a generic representation `A` of
`GL_(n+1)(F)`, the induced representation `A × μ_z` of `GL_(n+2)(F)` is generic
for all but finitely many `z`. -/
def PairInductionGenericity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ)
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)),
    (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n A.representation) →
    {z : ℂˣ | ¬ (letI := F.canonicalTopologicalData.topology
      Whittaker.IsGeneric ψ (n + 1) (pairInduced F A (unramifiedRankOne.{uF, uX} F z)))}.Finite


/-- The unit group of `ℂ` is infinite: it contains the images of `n + 1`. -/
theorem infinite_units_complex : Infinite ℂˣ :=
  Infinite.of_injective (fun n : ℕ => Units.mk0 ((n : ℂ) + 1) (Nat.cast_add_one_ne_zero n))
    fun a b h => by
      have h' := congrArg Units.val h
      simpa using h'

theorem finrank_ulift_complex : Module.finrank ℂ (ULift.{uX} ℂ) = 1 :=
  ULift.moduleEquiv.finrank_eq.trans (Module.finrank_self ℂ)

/-- The rank-one character `μ_z` has scalar character `a ↦ μ_z(det(a))`. -/
theorem hasScalarCharacter_unramifiedRankOne (F : PadicField.{uF} p) (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    Classification.HasScalarCharacter (unramifiedRankOne.{uF, uX} F z).representation
      GeneralLinear.scalar
      (((F.canonicalTopologicalData.unramifiedCharacter z).comp (determinant (n := 1))).comp
        (GeneralLinear.scalar (n := 1))) := by
  intro c v
  rfl

section Canonical

local instance rankReductionNormedField (F : PadicField.{uF} p) :
    NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField

/-- The rank-one character `μ_z` is generic: its line is irreducible, and it is
admissible with a nonzero Whittaker functional. -/
theorem isGeneric_unramifiedRankOne (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (z : ℂˣ) :
    Whittaker.IsGeneric ψ 0 (unramifiedRankOne.{uF, uX} F z).representation := by
  have := Classification.UnlinkedSegmentSocleProductIrreducibleProof.isIrreducible_of_finrank_eq_one
    (unramifiedRankOne.{uF, uX} F z).representation finrank_ulift_complex
  exact Whittaker.isGeneric_rankOne ψ _
    (rankOneExtensionCharacter_isOfWhittakerType.{uF, uX} F ψ
      (F.canonicalTopologicalData.unramifiedCharacterContinuous z)).1

/-- A gamma factor of a pair of generic representations is nonzero: it is the
constructed unit `genericSymmetricGammaFactor`. -/
theorem gammaFactor_ne_zero_of_isGeneric (F : PadicField.{uF} p)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ t σ) {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val π σ G) : G ≠ 0 := fun h =>
  Units.ne_zero _ ((genericSymmetricGammaFactor_eq F ψ ν.val ν.property π σ hπ hσ hG).trans h)

/-- Jacquet and Shalika 1985, §4.3, induction on the test rank: stability against
tests of rank `t + 2` and of rank one gives stability against tests of rank
`t + 1`. A generic test `σ` is induced with `μ_z` to a generic test `σ × μ_z`;
multiplicativity splits its gamma factor, and the factor of `μ_z` is cancelled. -/
theorem pairStability_of_succ_test {r t : ℕ}
    (hnext : PairStability.{uF, uV, max uF uX} r (t + 1))
    (hone : PairStability.{uF, uV, uX} r 0)
    (hgen : PairInductionGenericity.{uF, uX}) :
    PairStability.{uF, uV, uX} r t := by
  intro p _ F ψ ν hψ V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  have := infinite_units_complex
  let σs : SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) :=
    SmoothRep.of σ hσ.2.1.1
  obtain ⟨z, hz⟩ := (hgen p F ψ t σs hσ).exists_notMem
  have hzg : Whittaker.IsGeneric ψ (t + 1)
      (pairInduced F σs (unramifiedRankOne.{uF, uX} F z)) := not_not.mp hz
  have hμ := isGeneric_unramifiedRankOne.{uF, uX} F ψ z
  obtain ⟨A₁, hA₁⟩ := hnext p F ψ ν hψ π₁ π₂ _ hπ₁ hπ₂ hzg hc
  obtain ⟨A₂, hA₂⟩ := hone p F ψ ν hψ π₁ π₂ _ hπ₁ hπ₂ hμ hc
  refine ⟨max A₁ A₂, fun χ hχ G₁ G₂ h₁ h₂ => ?_⟩
  have hblocks : ∀ i, IsOfWhittakerType (pairSizes t i) (standardCharacter ψ (pairSizes t i))
      (pairFamily F σs (unramifiedRankOne.{uF, uX} F z) i).representation :=
    Fin.forall_fin_two.mpr
      ⟨isOfWhittakerType_of_isGeneric F hσ, isOfWhittakerType_of_isGeneric F hμ⟩
  have hχ₁ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁
  have hχ₂ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂
  obtain ⟨H₁, hH₁, hP₁⟩ := gammaMultiplicativity p F ψ ν r (t + 1) 2 (pairSizes t)
    (pairSizes_sum t) _
    (fun i => (pairFamily F σs (unramifiedRankOne.{uF, uX} F z) i).representation)
    (isOfWhittakerType_of_isGeneric F hχ₁) hblocks
  obtain ⟨H₂, hH₂, hP₂⟩ := gammaMultiplicativity p F ψ ν r (t + 1) 2 (pairSizes t)
    (pairSizes_sum t) _
    (fun i => (pairFamily F σs (unramifiedRankOne.{uF, uX} F z) i).representation)
    (isOfWhittakerType_of_isGeneric F hχ₂) hblocks
  have hprod : H₁ 0 * H₁ 1 = H₂ 0 * H₂ 1 := by
    have h := hA₁ χ (le_of_max_le_left hχ) _ _ hP₁ hP₂
    rwa [Fin.prod_univ_two, Fin.prod_univ_two] at h
  have hlast : H₁ 1 = H₂ 1 := hA₂ χ (le_of_max_le_right hχ) _ _ (hH₁ 1) (hH₂ 1)
  have hne : H₂ 1 ≠ 0 := gammaFactor_ne_zero_of_isGeneric F ψ ν hχ₂ hμ (hH₂ 1)
  rw [hlast] at hprod
  exact (h₁.unique (hH₁ 0)).trans ((mul_right_cancel₀ hne hprod).trans (h₂.unique (hH₂ 0)).symm)

/-- Jacquet and Shalika 1985, §4.3, induction on the candidate rank: stability
of candidates of rank `r + 2` gives stability of candidates of rank `r + 1`.
Two candidates `π₁, π₂` are induced with a common `μ_z` to generic candidates
`π_i × μ_z` with equal central characters. A determinant twist of `π_i × μ_z` is
the induction of the twists of `π_i` and `μ_z`; multiplicativity splits its gamma
factor against `σ`, and the common factor of the twist of `μ_z` is cancelled. -/
theorem pairStability_of_succ_candidate {r t : ℕ}
    (hnext : PairStability.{uF, max uF uX, uW} (r + 1) t)
    (hgen : PairInductionGenericity.{uF, uX}) :
    PairStability.{uF, uX, uW} r t := by
  intro p _ F ψ ν hψ V₁ V₂ _ _ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ hc
  have := infinite_units_complex
  let T := F.canonicalTopologicalData
  let A₁ : SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    SmoothRep.of π₁ hπ₁.2.1.1
  let A₂ : SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    SmoothRep.of π₂ hπ₂.2.1.1
  obtain ⟨z, hz⟩ := ((hgen p F ψ r A₁ hπ₁).union (hgen p F ψ r A₂ hπ₂)).exists_notMem
  rw [Set.mem_union, not_or] at hz
  have hz₁ : Whittaker.IsGeneric ψ (r + 1)
      (pairInduced F A₁ (unramifiedRankOne.{uF, uX} F z)) := not_not.mp hz.1
  have hz₂ : Whittaker.IsGeneric ψ (r + 1)
      (pairInduced F A₂ (unramifiedRankOne.{uF, uX} F z)) := not_not.mp hz.2
  have hμ := isGeneric_unramifiedRankOne.{uF, uX} F ψ z
  have hcz : SameGLCentralCharacter F (pairInduced F A₁ (unramifiedRankOne.{uF, uX} F z))
      (pairInduced F A₂ (unramifiedRankOne.{uF, uX} F z)) := by
    obtain ⟨ω, h₁, h₂⟩ := hc
    let c : Fin 2 → (F.Carrierˣ →* ℂˣ) :=
      ![ω, ((T.unramifiedCharacter z).comp (determinant (n := 1))).comp
        (GeneralLinear.scalar (n := 1))]
    have hB : ∀ B : SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier),
        Classification.HasGLCentralCharacter F.Carrier (r + 1) B.representation ω →
        Classification.HasGLCentralCharacter F.Carrier (r + 1 + 1)
          (pairInduced F B (unramifiedRankOne.{uF, uX} F z)) (∏ i, c i) := by
      intro B hB
      have hblocks : ∀ i, Classification.HasScalarCharacter
          (pairFamily F B (unramifiedRankOne.{uF, uX} F z) i).representation
          GeneralLinear.scalar (c i) :=
        Fin.forall_fin_two.mpr ⟨hB, hasScalarCharacter_unramifiedRankOne.{uF, uX} F z⟩
      exact T.hasScalarCharacter_normalizedProductInduced _ hblocks
    exact ⟨_, hB A₁ h₁, hB A₂ h₂⟩
  obtain ⟨A, hA⟩ := hnext p F ψ ν hψ _ _ σ hz₁ hz₂ hσ hcz
  refine ⟨A, fun χ hχ G₁ G₂ h₁ h₂ => ?_⟩
  have hσw := isOfWhittakerType_of_isGeneric F hσ
  have hμχ := isGeneric_quasicharacter_twist T ψ χ hμ
  have hχ₁ := isGeneric_quasicharacter_twist T ψ χ hπ₁
  have hχ₂ := isGeneric_quasicharacter_twist T ψ χ hπ₂
  have key : ∀ (B : SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)),
      Whittaker.IsGeneric ψ r B.representation →
      Whittaker.IsGeneric ψ (r + 1) (pairInduced F B (unramifiedRankOne.{uF, uX} F z)) →
      ∃ H : Fin 2 → RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val σ
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) B.representation) (H 0) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val σ
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
            (unramifiedRankOne.{uF, uX} F z).representation) (H 1) ∧
        IsPadicSymmetricGammaFactor F ψ ν.val
          (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
            (pairInduced F B (unramifiedRankOne.{uF, uX} F z))) σ (H 0 * H 1) := by
    intro B hB hBz
    have hblocks : ∀ i, IsOfWhittakerType (pairSizes r i) (standardCharacter ψ (pairSizes r i))
        (twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
          (pairFamily F B (unramifiedRankOne.{uF, uX} F z) i).representation) :=
      Fin.forall_fin_two.mpr
        ⟨isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hB),
          isOfWhittakerType_of_isGeneric F hμχ⟩
    obtain ⟨H, hH, hP⟩ := gammaMultiplicativity p F ψ ν t (r + 1) 2 (pairSizes r)
      (pairSizes_sum r) σ
      (fun i => twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
        (pairFamily F B (unramifiedRankOne.{uF, uX} F z) i).representation) hσw hblocks
    refine ⟨H, hH 0, hH 1, ?_⟩
    have e := T.normalizedProductDeterminantTwistEquiv
      (succBlockShape (pairSizes r) (pairSizes_sum r)) (quasicharacterSmoothCharacter T χ)
      (fun i => (pairFamily F B (unramifiedRankOne.{uF, uX} F z) i).representation)
    have hP' := (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl σ)
      e.symm).mp hP
    rw [Fin.prod_univ_two] at hP'
    exact (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val σ _ hσw
      (isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ χ hBz)) _).mp hP'
  obtain ⟨H₁, hH₁₀, hH₁₁, hP₁⟩ := key A₁ hπ₁ hz₁
  obtain ⟨H₂, hH₂₀, hH₂₁, hP₂⟩ := key A₂ hπ₂ hz₂
  have hprod : H₁ 0 * H₁ 1 = H₂ 0 * H₂ 1 := hA χ hχ _ _ hP₁ hP₂
  have hlast : H₁ 1 = H₂ 1 := hH₁₁.unique hH₂₁
  have hne : H₂ 1 ≠ 0 := gammaFactor_ne_zero_of_isGeneric F ψ ν hσ hμχ hH₂₁
  rw [hlast] at hprod
  have g₁ := (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val _ σ
    (isOfWhittakerType_of_isGeneric F hχ₁) hσw G₁).mp h₁
  have g₂ := (Padic.isPadicSymmetricGammaFactor_comm F ψ ν.val _ σ
    (isOfWhittakerType_of_isGeneric F hχ₂) hσw G₂).mp h₂
  exact (g₁.unique hH₁₀).trans ((mul_right_cancel₀ hne hprod).trans (g₂.unique hH₂₀).symm)

end Canonical

/-- Jacquet and Shalika 1985, §4.3: stability for every pair of ranks follows from
the adjacent case (candidate rank one more than the test rank) and the rank-one
case (tests of rank one). Candidates of rank at most the test rank are reached by
induction on the candidate rank (`pairStability_of_succ_candidate`), downward from
the adjacent case; tests of rank at least two less than the candidate rank are
reached by induction on the test rank (`pairStability_of_succ_test`), downward
from the adjacent case. The induced representations live in the universe
`max uF uV` or `max uF uW`, so the adjacent and rank-one cases are also needed
there. -/
theorem pairStability_of_adjacent_of_rankOne
    (hadj : ∀ n, PairStability.{uF, uV, uW} (n + 1) n)
    (hadjV : ∀ n, PairStability.{uF, max uF uV, uW} (n + 1) n)
    (hadjW : ∀ n, PairStability.{uF, uV, max uF uW} (n + 1) n)
    (hone : ∀ r, PairStability.{uF, uV, uW} r 0)
    (honeW : ∀ r, PairStability.{uF, uV, max uF uW} r 0)
    (hgenV : PairInductionGenericity.{uF, uV})
    (hgenV' : PairInductionGenericity.{uF, max uF uV})
    (hgenW : PairInductionGenericity.{uF, uW})
    (hgenW' : PairInductionGenericity.{uF, max uF uW})
    (r t : ℕ) : PairStability.{uF, uV, uW} r t := by
  have claimD : ∀ d r, r + d = t + 1 → PairStability.{uF, max uF uV, uW} r t := by
    intro d
    induction d with
    | zero =>
      intro r h
      rw [show r = t + 1 by omega]
      exact hadjV t
    | succ d ih =>
      intro r h
      exact pairStability_of_succ_candidate (ih (r + 1) (by omega)) hgenV'
  have claimC : ∀ d t, t + 1 + d = r → PairStability.{uF, uV, max uF uW} r t := by
    intro d
    induction d with
    | zero =>
      intro t h
      rw [show r = t + 1 by omega]
      exact hadjW t
    | succ d ih =>
      intro t h
      exact pairStability_of_succ_test (ih (t + 1) (by omega)) (honeW r) hgenW'
  rcases lt_trichotomy r (t + 1) with h | h | h
  · exact pairStability_of_succ_candidate (claimD (t - r) (r + 1) (by omega)) hgenV
  · rw [h]
    exact hadj t
  · exact pairStability_of_succ_test (claimC (r - (t + 2)) (t + 1) (by omega)) (hone r) hgenW

/-- `HighlyRamifiedGammaStabilityStatement` follows from the adjacent and rank-one
cases of stability and the genericity input, through
`pairStability_of_adjacent_of_rankOne`. -/
theorem highlyRamifiedGammaStability_of_adjacent_of_rankOne
    (hadj : ∀ n, PairStability.{uF, uV, uW} (n + 1) n)
    (hadjV : ∀ n, PairStability.{uF, max uF uV, uW} (n + 1) n)
    (hadjW : ∀ n, PairStability.{uF, uV, max uF uW} (n + 1) n)
    (hone : ∀ r, PairStability.{uF, uV, uW} r 0)
    (honeW : ∀ r, PairStability.{uF, uV, max uF uW} r 0)
    (hgenV : PairInductionGenericity.{uF, uV})
    (hgenV' : PairInductionGenericity.{uF, max uF uV})
    (hgenW : PairInductionGenericity.{uF, uW})
    (hgenW' : PairInductionGenericity.{uF, max uF uW}) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_pairStability fun r t =>
    pairStability_of_adjacent_of_rankOne hadj hadjV hadjW hone honeW hgenV hgenV' hgenW hgenW' r t

end Langlands.RankinSelberg.HighlyRamified
