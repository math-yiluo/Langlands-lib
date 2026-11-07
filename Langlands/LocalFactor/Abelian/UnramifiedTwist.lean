import Langlands.LocalFactor.Abelian.GaussEpsilon
import Langlands.LocalFactor.Abelian.LocalAnalysisHelpers

/-!
# Unramified twists of the actual abelian epsilon expression

The conductor is intrinsic, and the twisting factor is a genuine complex unit.
No nonabelian local-constant system is used.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- The intrinsic unit multiplying the epsilon expression under an unramified
twist of a character with conductor `a`. -/
def abelianUnramifiedTwistFactor (ω : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (a : ℕ) : ℂˣ :=
  ω (T.abelianScale (T.additiveConductor ψ + (a : ℤ)))

/-- An unramified twist preserves the actual least conductor, including zero. -/
theorem multiplicativeConductor_mul_unramified (χ ω : MultiplicativeCharacter)
    (hω : T.IsUnramifiedQuasicharacter ω) :
    T.multiplicativeConductor (χ * ω) = T.multiplicativeConductor χ := by
  symm
  apply (LocalFactor.PadicAbelian.conductorAt_iff T (χ * ω) _).mp
  exact LocalFactor.PadicAbelian.conductorAt_mul_unramified T χ ω _
    ((LocalFactor.PadicAbelian.conductorAt_iff T χ _).mpr rfl)
    ((LocalFactor.PadicAbelian.conductorAt_iff T ω 0).mpr
      ((T.multiplicativeConductor_eq_zero_iff ω).mpr hω).symm)

/-- Any actual uniformizer computes the intrinsic twisting factor. -/
theorem abelianUnramifiedTwistFactor_eq_uniformizer
    (ω : MultiplicativeCharacter) (hω : T.IsUnramifiedQuasicharacter ω)
    (ψ : AdditiveCharacter) (a : ℕ) (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) :
    T.abelianUnramifiedTwistFactor ω ψ a =
      ω π ^ (T.additiveConductor ψ + (a : ℤ)) := by
  apply Units.ext
  change (ω (T.abelianScale (T.additiveConductor ψ + (a : ℤ))) : ℂ) = _
  rw [LocalFactor.PadicAbelian.chi_eq_zpow_ord T ω
    ((LocalFactor.PadicAbelian.conductorAt_iff T ω 0).mpr
      ((T.multiplicativeConductor_eq_zero_iff ω).mpr hω).symm) hπ,
    T.abelianScale_order]
  simp only [Units.val_zpow_eq_zpow_val]

/-- Deligne (3.4.3.5) for the actual integral expression and its actual conductor. -/
theorem abelianEpsilonExpression_mul_unramified (χ ω : MultiplicativeCharacter)
    (hω : T.IsUnramifiedQuasicharacter ω)
    (ψ : AdditiveCharacter) (μ : LocalHaar) :
    T.abelianEpsilonExpression (χ * ω) ψ μ =
      (T.abelianUnramifiedTwistFactor ω ψ (T.multiplicativeConductor χ) : ℂ) *
        T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  rw [← LocalFactor.PadicAbelian.deligneConstant_eq_abelianEpsilonExpression T (χ * ω),
    ← LocalFactor.PadicAbelian.deligneConstant_eq_abelianEpsilonExpression T χ,
    T.abelianUnramifiedTwistFactor_eq_uniformizer ω hω ψ _
      (LocalFactor.PadicAbelian.uniformizerUnit T)
      (LocalFactor.PadicAbelian.uniformizerUnit_ord T)]
  unfold LocalFactor.PadicAbelian.deligneConstant LocalFactor.PadicAbelian.epsilon
  rw [T.multiplicativeConductor_mul_unramified χ ω hω]
  simp only [Units.val_zpow_eq_zpow_val]
  exact LocalFactor.PadicAbelian.epsilonAt_mul_unramified T _
    (LocalFactor.PadicAbelian.uniformizerUnit_ord T) χ ω
    ((LocalFactor.PadicAbelian.conductorAt_iff T ω 0).mpr
      ((T.multiplicativeConductor_eq_zero_iff ω).mpr hω).symm) _ _ _ _ _

/-- In the quotient of two twisting factors the additive conductor cancels. -/
theorem abelianUnramifiedTwistFactor_div
    (ω : MultiplicativeCharacter) (hω : T.IsUnramifiedQuasicharacter ω)
    (ψ : AdditiveCharacter) (a b : ℕ) (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) :
    T.abelianUnramifiedTwistFactor ω ψ a /
        T.abelianUnramifiedTwistFactor ω ψ b =
      ω π ^ ((a : ℤ) - (b : ℤ)) := by
  rw [T.abelianUnramifiedTwistFactor_eq_uniformizer ω hω ψ a π hπ,
    T.abelianUnramifiedTwistFactor_eq_uniformizer ω hω ψ b π hπ,
    div_eq_mul_inv, ← zpow_sub]
  congr 1
  omega

/-- The degree-zero abelian ratio has only the conductor-difference twist
factor, for any supplied Haar measure and any actual uniformizer. -/
theorem abelianEpsilonExpression_ratio_mul_unramified
    (χ η ω : MultiplicativeCharacter) (hω : T.IsUnramifiedQuasicharacter ω)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) :
    T.abelianEpsilonExpression (χ * ω) ψ μ /
        T.abelianEpsilonExpression (η * ω) ψ μ =
      (ω π : ℂ) ^ ((T.multiplicativeConductor χ : ℤ) -
          (T.multiplicativeConductor η : ℤ)) *
        (T.abelianEpsilonExpression χ ψ μ / T.abelianEpsilonExpression η ψ μ) := by
  rw [T.abelianEpsilonExpression_mul_unramified χ ω hω,
    T.abelianEpsilonExpression_mul_unramified η ω hω, mul_div_mul_comm]
  have h := congrArg (fun z : ℂˣ => (z : ℂ))
    (T.abelianUnramifiedTwistFactor_div ω hω ψ
      (T.multiplicativeConductor χ) (T.multiplicativeConductor η) π hπ)
  simpa only [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val] using
    congrArg (fun z : ℂ => z *
      (T.abelianEpsilonExpression χ ψ μ / T.abelianEpsilonExpression η ψ μ)) h

end Langlands.PadicField.TopologicalData
