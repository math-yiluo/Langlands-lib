import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.Assembly
import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.DeltaPairing
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.Twist.ContinuousCharacterProof

/-!
# Invariant pairings with the Gelfand–Graev representation of `GL_(n+1)`

The general statement `exists_pairing_intertwiner`, specialized to the upper unipotent subgroup
of `GL_(n+1)(F)` with the standard character, proves `DeltaPairingStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration Induction

universe uF uE

/-- Coefficients of the evaluation functional of an intertwiner recover the intertwiner. -/
theorem coefficientMap_evaluationFunctional {G : Type*} [Group G] {N : Subgroup G}
    {θ : N →* ℂˣ} {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (Φ : π.IntertwiningMap (functionRepresentation N θ)) (e : V) :
    coefficientMap π (evaluationFunctional π Φ) e = Φ e :=
  congrArg (fun f : π.IntertwiningMap (functionRepresentation N θ) => f e)
    ((functionalEquiv π).apply_symm_apply Φ)

set_option maxHeartbeats 800000 in
/-- **The delta pairing lemma for `GL_(n+1)`.** A `G`-invariant bilinear form on the
Gelfand–Graev representation and a smooth representation `π` is integration against the
coefficient functions of an inverse-character Whittaker functional of `π`. -/
theorem deltaPairing : DeltaPairingStatement.{uF, uE} := by
  classical
  intro p _ F ψ n
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let _ : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let _ : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro _ μ hμ E _ _ π hπ β hβ
  let _ : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (n + 1)
  have : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    T.generalLinearSigmaCompactSpace (n + 1)
  have : NonarchimedeanGroup (upperUnipotent (n + 1) F.Carrier) :=
    T.upperUnipotentNonarchimedean (n + 1)
  have : IsFiniteMeasureOnCompacts μ := hμ.regular.toIsFiniteMeasureOnCompacts
  have hθ : IsOpen ((standardCharacter ψ n).ker : Set (upperUnipotent (n + 1) F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  have hcof : ∀ U ∈ nhds (1 : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
          (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ⊆ U := by
    intro U hU
    let L := T.generalLinearCompactOpen (n + 1) U hU
    exact ⟨L.1, L.2.1, L.2.2⟩
  obtain ⟨Φ, hΦ⟩ := exists_pairing_intertwiner (N := upperUnipotent (n + 1) F.Carrier)
    (θ := standardCharacter ψ n) μ hμ.nonzero hμ.right_invariant hcof hθ π hπ β hβ
  let ℓ' : glInverseFunctionals ψ n π := evaluationFunctional π Φ
  refine ⟨ℓ', fun x e => ?_⟩
  obtain ⟨hf, hx⟩ := hΦ x e
  rw [hx]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change eval _ _ x.1 g * (Φ e).val g =
      eval _ _ x.1 g * (coefficientMap π ℓ' e).val g
    congr 1
    have h := congrArg Subtype.val (coefficientMap_evaluationFunctional π Φ e)
    exact (congrFun h g).symm

end Langlands.RankinSelberg.SupercuspidalCompleteness
