import Langlands.BaseChange.LocalGaloisStabilizer
import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.LocalField.PadicBridge
import Langlands.Representation.Classification.BernsteinUnitaryProductIrreducibilityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Unitary.Restriction

/-! # Distinct factors and irreducibility of a local Galois orbit product -/

noncomputable section

universe uK uL uW

set_option autoImplicit false

namespace Langlands.BaseChange

/-- Pullbacks by different powers below the order of the generator are
inequivalent when the original representation has trivial stabilizer. -/
theorem not_nonempty_orbitFactorEquiv_of_trivialStabilizer
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) {d n : ℕ} (horder : orderOf σ = d)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear n L) W) (htriv : HasTrivialGaloisStabilizer K τ)
    {i j : Fin d} (hij : i ≠ j) :
    ¬ Nonempty (Representation.Equiv (τ.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
      (τ.comp (entrywiseAut (σ ^ (j : ℕ)) n).toMonoidHom)) := by
  rintro ⟨e⟩
  let a := σ ^ (i : ℕ)
  let b := σ ^ (j : ℕ)
  have hi : (i : ℕ) ∈ Set.Iio (orderOf σ) := horder.symm ▸ i.isLt
  have hj : (j : ℕ) ∈ Set.Iio (orderOf σ) := horder.symm ▸ j.isLt
  have hab : a ≠ b := fun h => hij (Fin.ext (pow_injOn_Iio_orderOf hi hj h))
  have hb : b * a⁻¹ ≠ 1 := fun h => hab (mul_inv_eq_one.mp h).symm
  apply htriv (b * a⁻¹) hb
  refine ⟨Representation.Equiv.mk e.toLinearEquiv (fun g => ?_)⟩
  have h := e.toIntertwiningMap.isIntertwining' (entrywiseAut a⁻¹ n g)
  change e.toLinearEquiv.toLinearMap.comp
      (τ (entrywiseAut a n (entrywiseAut a⁻¹ n g))) =
    (τ (entrywiseAut b n (entrywiseAut a⁻¹ n g))).comp e.toLinearEquiv.toLinearMap at h
  rw [← entrywiseAut_mul_apply a, ← entrywiseAut_mul_apply b,
    mul_inv_cancel, entrywiseAut_one_apply] at h
  exact h

/-- Every finite normalized Galois orbit product of a smooth, irreducible
unitarizable action is irreducible and unitarizable on the supplied p-adic
topology, for a continuous automorphism. -/
def SigmaOrbitProductIrreducibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PadicField.{uL} p)
    (K : Type uK) [Field K] [Algebra K L.Carrier] (T : L.TopologicalData)
    (σ : L.Carrier ≃ₐ[K] L.Carrier) (d n : ℕ) (hn : 0 < n)
    (W : Type (max uL uW)) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear n L.Carrier) W),
    τ.IsIrreducible → IsUnitarizable τ →
    let := T.topology
    let := T.valuativeRel
    have := T.localField
    Continuous σ → IsSmooth τ →
      Representation.IsIrreducible (sigmaOrbitProduct σ d hn τ) ∧
      IsUnitarizable (sigmaOrbitProduct σ d hn τ)

section Unitary

variable {p : ℕ} [Fact p.Prime] {L : PadicField.{uL} p}

private theorem allField_leviHalfCharacter_eq (T : L.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    T.toLocalFieldData.leviHalfCharacter B = T.leviHalfCharacter B := rfl

set_option maxHeartbeats 400000 in
/-- Apply Bernstein's unitary product theorem to the smooth orbit factors. -/
theorem sigmaOrbitProduct_irreducible_unitarizable :
    SigmaOrbitProductIrreducibilityStatement.{uK, uL, uW} := by
  intro p hp L K _ _ T σ d n hn W _ _ τ hirr hu
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hRing : @IsTopologicalRing L.Carrier T.topology _ := inferInstance
  dsimp only
  intro hσ hτ
  have hpow (i : ℕ) : Continuous (σ ^ i) := by
    induction i with
    | zero =>
      rw [pow_zero]
      exact continuous_id
    | succ i hi =>
      rw [pow_succ]
      exact hi.comp hσ
  let B := GeneralLinear.BlockShape.uniform d n hn
  let A (i : Fin B.length) : SmoothRep.{0, uL, max uL uW} ℂ (GeneralLinear (B.size i) L.Carrier) :=
    SmoothRep.of (τ.comp (entrywiseAut (σ ^ (i : ℕ)) n).toMonoidHom)
      (isSmooth_comp _ (hpow i).generalLinearGroup_map hτ)
  have hA (i : Fin B.length) :
      Representation.IsIrreducible (A i).representation ∧
        IsUnitarizable (A i).representation :=
    ⟨(CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ (entrywiseAut _ _)).mpr hirr,
      hu.comp _⟩
  have h := Classification.bernsteinUnitaryProductIrreducibility L T (d * n) B A hA
  rw [T.normalizedProductInductionFunctor_obj] at h
  unfold PadicField.TopologicalData.normalizedProductInduced
    PadicField.TopologicalData.normalizedParabolicInduced at h
  unfold sigmaOrbitProduct LocalFieldData.normalizedProductInduced
    LocalFieldData.normalizedParabolicInduced
  let propertyOfInduction (χ : Induction.SmoothCharacter ℂ (B.Levi L.Carrier)) : Prop :=
    let ρ := @GeneralLinear.BlockShape.normalizedInducedOf L.Carrier _ T.topology hRing
      _ B _ _ _ χ (B.blockTensor (fun i => (A i).representation))
    Representation.IsIrreducible ρ ∧ IsUnitarizable ρ
  change propertyOfInduction (T.toLocalFieldData.leviHalfCharacter B)
  rw [allField_leviHalfCharacter_eq]
  exact h

end Unitary

end Langlands.BaseChange
