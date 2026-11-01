import Langlands.Representation.Exponents.CuspidalTensorRealPartsStatement
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.Exponents.DescendingIntervalBlockScalarProof

/-! # Actual cuspidal scalar characters and their rank-weighted real parts -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uF uV

/-- Removing an actual unitarizing determinant twist recovers the original
scalar character and retains its rank in the norm formula. -/
theorem supercuspidalRealScalarCharacter
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (hn : 0 < n) :
    letI := T.topology
    ∀ A : GeneralLinear.SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := n),
      ∃ (t : ℝ) (c : F.Carrierˣ →* ℂˣ),
        IsUnitarizable (realPowerTwist (T.determinantNorm n) t A.obj.representation) ∧
        Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar c ∧
        ∀ a : F.Carrierˣ, ‖(c a : ℂ)‖ =
          T.normalizedAbs (a : F.Carrier) ^ (-((n : ℝ) * t)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A
  obtain ⟨t, hu, _⟩ := supercuspidalRepRealUnitarization F T n hn A
  let B := GeneralLinear.SupercuspidalRep.twist (T.determinantPowerCharacter n t)
    (T.isOpen_ker_determinantPowerCharacter n t)
    (T.ker_determinant_le_ker_determinantPowerCharacter n t) A
  obtain ⟨cB⟩ := unitarizableCentralCharacter B.obj.representation
    B.property.2.1 B.property.1 hu
  let θ := (T.determinantPowerCharacter n t).comp GeneralLinear.scalar
  let c := (cB.character.comp GeneralLinear.scalarToCenter) * θ⁻¹
  refine ⟨t, c, hu, ?_, ?_⟩
  · intro a v
    have h := cB.acts (GeneralLinear.scalarToCenter a) v
    change (θ a : ℂ) • A.obj.representation (GeneralLinear.scalar a) v =
      (cB.character (GeneralLinear.scalarToCenter a) : ℂ) • v at h
    calc
      A.obj.representation (GeneralLinear.scalar a) v =
          (θ a : ℂ)⁻¹ • ((θ a : ℂ) •
            A.obj.representation (GeneralLinear.scalar a) v) := by
        rw [smul_smul, inv_mul_cancel₀ (θ a).ne_zero, one_smul]
      _ = (c a : ℂ) • v := by
        rw [h, smul_smul]
        simp only [c, MonoidHom.mul_apply, MonoidHom.comp_apply,
          MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
        rw [mul_comm]
  · intro a
    simp only [c, MonoidHom.mul_apply, MonoidHom.comp_apply,
      MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [norm_mul, cB.norm_eq_one, one_mul, norm_inv]
    change (‖(T.determinantPowerCharacter n t (GeneralLinear.scalar a) : ℂ)‖)⁻¹ = _
    rw [T.norm_determinantPowerCharacter_scalar,
      Real.rpow_neg (T.normalizedAbs_nonneg _)]

/-- The actual block tensor carries the product character, with exactly the
negative rank-weighted coordinates of the original cuspidal factors. -/
theorem cuspidalTensorRealParts {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    CuspidalTensorRealPartsStatement.{uF,uV} F T := by
  classical
  let := T.topology
  intro n B C
  choose t c hu hc hn using fun i =>
    supercuspidalRealScalarCharacter F T (B.size i) (B.positive i) (C i)
  refine ⟨t, c, hu, hc, hn, B.hasScalarCharacter_blockTensor_splitCentre F.Carrier hc, ?_⟩
  intro a
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ => hn i (a i)

end Langlands
