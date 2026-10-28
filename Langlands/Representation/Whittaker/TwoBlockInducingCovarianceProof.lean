import Langlands.Representation.Whittaker.TwoBlockInducingCovarianceStatement
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! # Proof of scalar Whittaker covariance for actual two-block induction -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

section Tensor

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) (a b : ℕ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
  (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂)

/-- Tensor linearity transports the two factor Whittaker identities to the
actual block tensor representation, without a topology on its carrier. -/
theorem pairFunctional_blockTensor_unipotent
    (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (hℓ₁ : ℓ₁ ∈ glFunctionals ψ a π₁)
    (ℓ₂ : V₂ →ₗ[ℂ] ℂ) (hℓ₂ : ℓ₂ ∈ glFunctionals ψ b π₂)
    (u₁ : upperUnipotent (a + 1) F) (u₂ : upperUnipotent (b + 1) F)
    (v : PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) :
    Shahidi.pairFunctional ℓ₁ ℓ₂
        ((twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂)
          ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm
            (u₁.val, u₂.val)) v) =
      ((standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)) *
        Shahidi.pairFunctional ℓ₁ ℓ₂ v := by
  have h : (Shahidi.pairFunctional ℓ₁ ℓ₂).comp
        ((twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂)
          ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm
            (u₁.val, u₂.val))) =
      ((standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)) •
        Shahidi.pairFunctional ℓ₁ ℓ₂ := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change Shahidi.pairFunctional ℓ₁ ℓ₂
        ((twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂) _
          (PiTensorProduct.tprod ℂ x)) = _
    rw [BlockShape.blockTensor_tprod, Shahidi.pairFunctional_tprod]
    change ℓ₁ (π₁ u₁.val (x 0)) * ℓ₂ (π₂ u₂.val (x 1)) =
      ((standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)) *
        Shahidi.pairFunctional ℓ₁ ℓ₂ (PiTensorProduct.tprod ℂ x)
    erw [hℓ₁ u₁, hℓ₂ u₂, Shahidi.pairFunctional_tprod]
    dsimp only [Shahidi.pairFactorFunctional]
    exact mul_mul_mul_comm _ _ _ _
  exact LinearMap.congr_fun h v

end Tensor

/-- The actual normalized covariance law and determinant-one of the two
unipotent blocks give the required scalar left covariance. -/
theorem twoBlockInducingWhittakerCovariance :
    TwoBlockInducingWhittakerCovarianceStatement.{uF, uV} := by
  intro p _ F ψ a b V₁ _ _ V₂ _ _ π₁ π₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ f u₁ u₂ g
  let m : (twoBlockShape a b).Levi F.Carrier :=
    (Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm
      (u₁.val, u₂.val)
  have hnorm (r : ℕ) (u : upperUnipotent r F.Carrier) :
      T.determinantNorm r u.val = 1 := by
    have hd : GeneralLinear.determinant u.val = 1 :=
      Units.ext (RankinSelberg.unipotent_det u)
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hd, map_one]
  have hmod : T.leviModulus (twoBlockShape a b) m = 1 := by
    rw [T.leviModulus_twoBlocks]
    change T.determinantNorm (a + 1) u₁.val ^ (b + 1) /
      T.determinantNorm (b + 1) u₂.val ^ (a + 1) = 1
    simp only [hnorm, one_pow, div_one]
  have he : ((twoBlockShape a b).leviInParabolic F.Carrier m).val =
      blockSum (u₁.val, u₂.val) := by
    exact Shahidi.twoBlocks_leviEmbedding (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier m
  have hc := T.normalizedProductInduced_covariant (twoBlockShape a b)
    (Shahidi.pairFamily π₁ π₂) f
    ((twoBlockShape a b).leviInParabolic F.Carrier m) g
  rw [he, BlockShape.leviProjection_section, hmod] at hc
  simp only [Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, one_smul] at hc
  change Shahidi.pairFunctional ℓ₁ ℓ₂
    (Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂)
      f (blockSum (u₁.val, u₂.val) * g)) = _
  rw [hc]
  exact pairFunctional_blockTensor_unipotent ψ a b π₁ π₂ ℓ₁ hℓ₁ ℓ₂ hℓ₂ u₁ u₂ _

end Langlands.Whittaker
