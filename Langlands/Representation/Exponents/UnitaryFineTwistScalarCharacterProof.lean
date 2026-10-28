import Langlands.Representation.Exponents.UnitaryFineTwistScalarCharacterStatement
import Langlands.Representation.Unitary.CentralCharacterProof

/-!
# Scalar real parts of fine twists of unitary data

Restrict the actual unitary central character to block scalars, multiply by the
negative real determinant character, and cancel the flattened Levi maps.
-/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV

/-- The actual scalar character of the fine negative determinant twist has
the size-weighted negative real exponent. -/
theorem unitaryFineTwistScalarCharacter :
    UnitaryFineTwistScalarCharacterStatement.{uF, uV} := by
  classical
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n D R ω hi ha hu v₀
  let B := D.flatten R
  let := T.leviTopologicalGroup B
  obtain ⟨c⟩ := unitarizableCentralCharacter ω.ρ ha hi hu
  let f : (Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier) :=
    (B.blockScalarLevi F.Carrier).codRestrict _ (B.blockScalarLevi_mem_center F.Carrier)
  let ψ : (Fin B.length → F.Carrierˣ) →* ℂˣ := c.character.comp f
  let θ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    (T.leviRealPowerCharacter B (-v₀)).comp (B.blockScalarLevi F.Carrier)
  let χ := ψ * θ
  have hcont : Continuous (B.blockScalarLevi F.Carrier) := by
    change Continuous fun a : Fin B.length → F.Carrierˣ =>
      fun k => GeneralLinear.scalar (n := B.size k) (a k)
    exact continuous_pi fun k =>
      GeneralLinear.scalarContinuous.continuous.comp (continuous_apply k)
  have hf : Continuous f := hcont.subtype_mk _
  have hψ : IsOpen (ψ.ker : Set (Fin B.length → F.Carrierˣ)) :=
    c.isOpen_ker.preimage hf
  have hθ : IsOpen (θ.ker : Set (Fin B.length → F.Carrierˣ)) :=
    (T.isOpen_ker_leviRealPowerCharacter B (-v₀)).preimage hcont
  have hχ : IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) := by
    refine Subgroup.isOpen_mono (H₁ := ψ.ker ⊓ θ.ker) ?_ (hψ.inter hθ)
    intro a ha
    obtain ⟨h1, h2⟩ := ha
    change ψ a * θ a = 1
    rw [show ψ a = 1 from h1, show θ a = 1 from h2, one_mul]
  have hscalar : Classification.HasScalarCharacter
      (T.leviRealPowerTwist B (-v₀) ω.ρ) (B.blockScalarLevi F.Carrier) χ := by
    intro a w
    change (T.leviRealPowerCharacter B (-v₀) (B.blockScalarLevi F.Carrier a) : ℂ) •
      ω.ρ (B.blockScalarLevi F.Carrier a) w = (χ a : ℂ) • w
    rw [show ω.ρ (B.blockScalarLevi F.Carrier a) w =
      (c.character (f a) : ℂ) • w from c.acts (f a) w]
    simp only [χ, ψ, θ, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul,
      smul_smul]
    rw [mul_comm]
  refine ⟨χ, hχ, ?_, ?_⟩
  · intro a w
    change (T.leviRealPowerTwist B
      (fun k => -v₀ k + (0 : Fin D.length → ℝ) ((D.flattenBlockEquiv R).symm k).1)
        ω.ρ)
      ((flattenedLeviEquiv F.Carrier D R).symm
        (flattenedLeviEquiv F.Carrier D R (B.blockScalarLevi F.Carrier a))) w =
      (χ a : ℂ) • w
    rw [show (fun k => -v₀ k + (0 : Fin D.length → ℝ)
      ((D.flattenBlockEquiv R).symm k).1) = -v₀ by
        funext k
        simp, MulEquiv.symm_apply_apply]
    exact hscalar a w
  · intro a
    change ‖(ψ a : ℂ) * (θ a : ℂ)‖ = _
    rw [norm_mul, show ‖(ψ a : ℂ)‖ = 1 from c.norm_eq_one (f a), one_mul]
    change ‖(T.leviRealPowerCharacter B (-v₀)
      (B.blockScalarLevi F.Carrier a) : ℂ)‖ = _
    rw [T.coe_leviRealPowerCharacter_blockScalar B, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun k _ =>
        Real.rpow_nonneg (T.normalizedAbs_nonneg _) _)]
    simp only [Pi.neg_apply, mul_neg]
    rfl

end Langlands.Exponents
