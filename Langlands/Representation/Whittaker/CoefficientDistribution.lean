import Langlands.Representation.Whittaker.Distribution
import Langlands.Representation.Whittaker.GeneralizedCoefficient
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-! # Generalized Whittaker coefficients as bi-equivariant distributions -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uF uV

section Submodule

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The actual subspace of distributions satisfying the published Whittaker law. -/
def biEquivariantDistributions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Submodule ℂ (Distribution (GeneralLinear (n + 1) F)) where
  carrier := {D | IsBiEquivariantDistribution ψ n D}
  zero_mem' := by intro u₁ u₂ f; simp
  add_mem' := by
    intro D E hD hE u₁ u₂ f
    change D _ + E _ = _ * (D f + E f)
    rw [hD, hE, mul_add]
  smul_mem' := by
    intro c D hD u₁ u₂ f
    change c * D _ = _ * (c * D f)
    rw [hD, mul_left_comm]

@[simp] theorem mem_biEquivariantDistributions (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (D : Distribution (GeneralLinear (n + 1) F)) :
    D ∈ biEquivariantDistributions ψ n ↔ IsBiEquivariantDistribution ψ n D := Iff.rfl

end Submodule

section Coefficients

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)

variable [T2Space (GeneralLinear (n + 1) F)]
  [LocallyCompactSpace (GeneralLinear (n + 1) F)]
  [TotallyDisconnectedSpace (GeneralLinear (n + 1) F)]
  [MeasurableSpace (GeneralLinear (n + 1) F)] [BorelSpace (GeneralLinear (n + 1) F)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure (GeneralLinear (n + 1) F))
  [IsFiniteMeasureOnCompacts μ] [IsMulRightInvariant μ] [IsMulLeftInvariant μ]
variable (ρ : Representation ℂ (GeneralLinear (n + 1) F) V) (hρ : IsSmooth ρ)

/-- The two input covariance laws give bi-equivariance for the inverse additive character. -/
theorem generalizedCoefficient_isBiEquivariant
    (ℓ : glFunctionals ψ n ρ)
    (η : glInverseFunctionals ψ n (smoothContragredient ρ)) :
    IsBiEquivariantDistribution (ψ.scale (-1)) n
      (generalizedCoefficient μ ρ hρ ℓ.val η.val) := by
  intro u₁ u₂ f
  rw [Langlands.RankinSelberg.standardCharacter_scale_neg_one]
  apply generalizedCoefficient_biTranslate
  · ext v
    change ℓ.val (ρ u₁.val⁻¹ v) = (inverseStandardCharacter ψ n u₁ : ℂ) * ℓ.val v
    simpa only [Subgroup.coe_inv, map_inv, inverseStandardCharacter,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val] using ℓ.property u₁⁻¹ v
  · ext v
    exact η.property u₂ v

/-- The actual bilinear coefficient distribution, with its bi-equivariant codomain. -/
def glCoefficientDistribution :
    glFunctionals ψ n ρ →ₗ[ℂ]
      glInverseFunctionals ψ n (smoothContragredient ρ) →ₗ[ℂ]
        biEquivariantDistributions (ψ.scale (-1)) n where
  toFun ℓ :=
    ((generalizedCoefficient μ ρ hρ ℓ.val).comp
      (glInverseFunctionals ψ n (smoothContragredient ρ)).subtype).codRestrict
        (biEquivariantDistributions (ψ.scale (-1)) n)
        (fun η => generalizedCoefficient_isBiEquivariant ψ n μ ρ hρ ℓ η)
  map_add' := by
    intro ℓ₁ ℓ₂
    ext η f
    change generalizedCoefficient μ ρ hρ (ℓ₁.val + ℓ₂.val) η.val f =
      generalizedCoefficient μ ρ hρ ℓ₁.val η.val f +
        generalizedCoefficient μ ρ hρ ℓ₂.val η.val f
    simp only [map_add, LinearMap.add_apply]
  map_smul' := by
    intro c ℓ
    ext η f
    change generalizedCoefficient μ ρ hρ (c • ℓ.val) η.val f =
      c * generalizedCoefficient μ ρ hρ ℓ.val η.val f
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem glCoefficientDistribution_val
    (ℓ : glFunctionals ψ n ρ)
    (η : glInverseFunctionals ψ n (smoothContragredient ρ)) :
    (glCoefficientDistribution ψ n μ ρ hρ ℓ η).val =
      generalizedCoefficient μ ρ hρ ℓ.val η.val := rfl

@[simp] theorem glCoefficientDistribution_apply
    (ℓ : glFunctionals ψ n ρ)
    (η : glInverseFunctionals ψ n (smoothContragredient ρ))
    (f : SchwartzBruhat (GeneralLinear (n + 1) F)) :
    (glCoefficientDistribution ψ n μ ρ hρ ℓ η).val f =
      η.val (smoothFunctional μ ρ hρ ℓ.val f) := rfl

end Coefficients

end Langlands.Whittaker
