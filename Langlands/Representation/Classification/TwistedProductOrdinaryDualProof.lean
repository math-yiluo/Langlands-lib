import Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Category.Contragredient

/-!
# Ordinary smooth duality of twisted block products

The smooth contragredient of a normalized product of twisted blocks
`ν^(s_i) δ_i` is equivalent to the normalized product, over the same upper block
parabolic, of the twisted block duals `ν^(-s_i) δ_i~`.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The smooth dual of `ν^s δ` is `ν^(-s)` twisting the smooth dual of `δ`;
the identification keeps every underlying functional. -/
def segmentFactorSmoothDualEquiv {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup r
    (smoothContragredient (T.segmentFactor A s).representation).Equiv
      (twist (T.determinantPowerCharacter r (-s))
        (smoothContragredient A.representation)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup r
  (smoothContragredientTwistEquiv (T.determinantPowerCharacter r s) A.representation
      (T.isOpen_ker_determinantPowerCharacter r s)).trans
    (equivOfRepresentationEq (by
      rw [PadicField.TopologicalData.determinantPowerCharacter,
        PadicField.TopologicalData.determinantPowerCharacter, realPowerCharacter_neg]))

/-- Ordinary smooth duality of twisted block products: the smooth dual of
`i(ν^(s_1) δ_1, …, ν^(s_r) δ_r)` is equivalent to
`i(ν^(-s_1) δ_1~, …, ν^(-s_r) δ_r~)` for admissible blocks `δ_i`. -/
theorem twistedProductOrdinaryDual :
    TwistedProductOrdinaryDualClause.{uF, uV} F T := by
  let := T.topology
  intro n _ B δ s hadm δv
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  let := T.leviTopologicalGroup B
  let τ := fun i => (T.twistedBlocks B δ s i).representation
  have hτ : ∀ i, IsAdmissible (τ i) := fun i =>
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter (B.size i) (s i))).mpr
      (hadm i)
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor τ)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external τ hτ
  obtain ⟨EI, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 p F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap τ) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ τ,
      FiniteTensor.smoothDualTensorMap_surjective τ hτ
      (fun i => GeneralLinear.compactOpen_cofinal F T (B.size i))⟩
  let e2 : (FiniteTensor.external (fun i => smoothContragredient (τ i))).Equiv
      (smoothContragredient (FiniteTensor.external τ)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner τ).isIntertwining'
  let e3 := fun i => segmentFactorSmoothDualEquiv F T (δ i) (s i)
  exact ⟨(EI σ hσ).trans ((T.normalizedParabolicInducedEquiv B e2.symm).trans
    (T.normalizedProductInducedEquiv B e3))⟩

end Langlands.Classification
