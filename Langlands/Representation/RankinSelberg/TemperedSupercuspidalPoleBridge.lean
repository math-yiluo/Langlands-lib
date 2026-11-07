import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification
import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleAssembly
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof

/-!
# Supercuspidal partners of selected tempered blocks

The classification and smooth-duality inputs construct an actual partner.
The three JPSS formulas and tempered block exhaustion remain explicit premises.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Polynomial
open TemperedSupercuspidalPoleAssembly

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

namespace TemperedSupercuspidalPoleBridge

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- A square-integrable block's top centered supercuspidal factor has a smooth
dual partner whose pair polynomial has a root at one, under (8.1)(ii) and (8.2).
The centered seed and rank identity are supplied unchanged. -/
theorem exists_partner_of_centered_component
    (H81 : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (H82 : SquareIntegrableLFactorStatement.{uF, max uF uV, max uF uV,
      max uF uV, max uF uV})
    {a d r : ℕ} (hr : ∑ _ : Fin (d + 1), (a + 1) = r + 1)
    (π₀ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + 1) F.Carrier))
    (hiπ₀ : Representation.IsIrreducible π₀.representation)
    (hsπ₀ : GeneralLinear.IsSupercuspidal π₀.representation)
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
    (heσ : F.canonicalTopologicalData.IsEssentiallySquareIntegrable σ.representation)
    (hcσ : IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
        (centeredSegmentBlocks F d π₀.representation)) σ.representation) :
    ∃ ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      Representation.IsIrreducible ρ.representation ∧
      GeneralLinear.IsSupercuspidal ρ.representation ∧
      F.canonicalTopologicalData.IsEssentiallySquareIntegrable ρ.representation ∧
      ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν.val
        σ.representation ρ.representation P ∧ P.IsRoot 1 := by
  let T := F.canonicalTopologicalData
  let := T.generalLinearTopologicalGroup (a + 1)
  have hi : Representation.IsIrreducible (centeredSegmentBlocks F d π₀.representation 0) :=
    isIrreducible_centeredSegmentBlocks d hiπ₀ 0
  have hs : GeneralLinear.IsSupercuspidal (centeredSegmentBlocks F d π₀.representation 0) :=
    isSupercuspidal_centeredSegmentBlocks d hsπ₀ 0
  let top : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + 1) F.Carrier) :=
    SmoothRep.of (centeredSegmentBlocks F d π₀.representation 0) hs.1.1
  let ρ := top.contragredient
  have hiρ : Representation.IsIrreducible ρ.representation :=
    (SmoothRep.isIrreducible_contragredient_iff
      (compactOpen_cofinal F T (a + 1)) top hs.1).mpr hi
  have hsρ : GeneralLinear.IsSupercuspidal ρ.representation :=
    isSupercuspidal_smoothContragredient F T (a + 1) _ top.representation hs
  have heρ := supercuspidal_isEssentiallySquareIntegrable F a ρ hiρ hsρ
  obtain ⟨ℓ, hℓ⟩ :=
    Whittaker.SupercuspidalKirillovProof.exists_functional T ψ a ρ hiρ hsρ
  have hwρ : IsOfWhittakerType a (standardCharacter ψ a) ρ.representation :=
    isOfWhittakerType_of_isGeneric F ⟨hiρ, hsρ.1, ℓ, hℓ⟩
  have hd : Nonempty ((centeredSegmentBlocks F d π₀.representation 0).Equiv
      (smoothContragredient ρ.representation)) :=
    ⟨SmoothRep.equivOfIso (SmoothRep.bidualIso (compactOpen_cofinal F T (a + 1)) top hs.1)⟩
  exact ⟨ρ, hiρ, hsρ, heρ,
    exists_squareIntegrable_isRoot_one ν H82 H81 hr hiπ₀ hsπ₀ hiρ hsρ
      heσ hcσ heρ hwρ hd⟩

/-- A full polynomial/root certificate together with the selected block,
centered seed and exact rank identity used to construct its partner. -/
def HasSelectedBlockPole (k : ℕ)
    (τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) : Prop :=
  ∃ (l : ℕ) (m : Fin l → ℕ) (hm : ∑ j, (m j + 1) = k + 1)
    (σ : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m j + 1) F.Carrier)),
    (∀ j, Representation.IsIrreducible (σ j).representation ∧
      F.canonicalTopologicalData.IsSquareIntegrable (σ j).representation ∧
      IsUnitarizable (σ j).representation) ∧
    Nonempty (τ.representation.Equiv
      (F.canonicalNormalizedProductInduced (succBlockShape m hm)
        (fun j => (σ j).representation))) ∧
    ∃ (i : Fin l) (a d : ℕ) (hr : ∑ _ : Fin (d + 1), (a + 1) = m i + 1)
      (π₀ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + 1) F.Carrier)),
      Representation.IsIrreducible π₀.representation ∧
      GeneralLinear.IsSupercuspidal π₀.representation ∧
      IsIrreducibleComponent
        (F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)
          (centeredSegmentBlocks F d π₀.representation)) (σ i).representation ∧
      ∃ ρ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + 1) F.Carrier),
        Representation.IsIrreducible ρ.representation ∧
        GeneralLinear.IsSupercuspidal ρ.representation ∧
        HasPadicRankPoleAtZero F ψ ν τ.representation ρ.representation

/-- Classification and the three explicit JPSS formulas give a selected block
pole certificate. No rank-bound assertion or formula proof is inferred. -/
theorem hasSelectedBlockPole_of
    (exhaustion : Classification.TemperedBlockExhaustion.{uF, uV}
      F F.canonicalTopologicalData)
    (H81 : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (H82 : SquareIntegrableLFactorStatement.{uF, max uF uV, max uF uV,
      max uF uV, max uF uV})
    (H84 : TemperedLFactorStatement.{uF, max uF uV, max uF uV})
    (k : ℕ) (τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (hiτ : Representation.IsIrreducible τ.representation)
    (htτ : F.canonicalTopologicalData.IsTempered τ.representation) :
    HasSelectedBlockPole F ψ ν k τ := by
  let T := F.canonicalTopologicalData
  obtain ⟨l, m, hm, σ, hσ, ⟨e⟩⟩ :=
    temperedSquareIntegrableBlockDecomposition F exhaustion k τ hiτ htτ
  have hl : l ≠ 0 := by
    intro h
    subst l
    simp at hm
  let i : Fin l := ⟨0, Nat.pos_of_ne_zero hl⟩
  have heσ := (hσ i).2.1.isEssentiallySquareIntegrable
  obtain ⟨a, d, hr, π₀, hiπ₀, hsπ₀, hcσ⟩ :=
    essentiallySquareIntegrableCenteredSegmentComponent F (m i) (σ i) (hσ i).1 heσ
  obtain ⟨ρ, hiρ, hsρ, heρ, R, hR, hroot⟩ :=
    exists_partner_of_centered_component F ψ ν H81 H82 hr π₀ hiπ₀ hsπ₀
      (σ i) heσ hcσ
  obtain ⟨z, hz⟩ := heρ
  let γ := T.segmentFactor ρ (-z)
  have hiγ : Representation.IsIrreducible γ.representation :=
    (SmoothRep.isIrreducible_twist_iff _ _ ρ).mpr hiρ
  have hrec : realPowerTwist (T.determinantNorm (a + 1)) z γ.representation =
      ρ.representation :=
    realPowerTwist_cancel_neg (T.determinantNorm (a + 1)) z ρ.representation
  have ha : a ≤ m i :=
    (le_iff_of_centeredSegment_rank hr
      (show ∑ _ : Fin (0 + 1), (a + 1) = a + 1 by simp)).mpr (Nat.zero_le d)
  have hRrank : IsPadicRankLPolynomial F ψ ν.val (σ i).representation
      ρ.representation R :=
    (isPadicSymmetricLPolynomial_of_le ha).mpr hR
  have hRtw : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (T.determinantNorm (m i + 1)) 0 (σ i).representation)
      (realPowerTwist (T.determinantNorm (a + 1)) z γ.representation) R := by
    simpa only [realPowerTwist_zero, hrec] using hRrank
  have hpole := exists_induced_isRoot_one F ψ ν H84 (Nat.succ_pos k)
    (succBlockShape m hm) (fun j => (σ j).representation)
    (fun j => (hσ j).1) (fun j => (hσ j).2.1) γ.representation hiγ γ.isSmooth
    hz e.symm 0 z i hRtw hroot
  refine ⟨l, m, hm, σ, hσ, ⟨e⟩, i, a, d, hr, π₀, hiπ₀, hsπ₀, hcσ,
    ρ, hiρ, hsρ, ?_⟩
  change HasPadicRankPoleAtZero F ψ ν
    (realPowerTwist (T.determinantNorm (k + 1)) 0 τ.representation)
    (realPowerTwist (T.determinantNorm (a + 1)) z γ.representation) at hpole
  simpa only [realPowerTwist_zero, hrec] using hpole

end TemperedSupercuspidalPoleBridge

end Langlands.RankinSelberg
