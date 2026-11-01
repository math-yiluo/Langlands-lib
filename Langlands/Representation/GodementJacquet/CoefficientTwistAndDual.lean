import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.Representation.Whittaker.Twist
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.Twist.DualProof

/-! Actual bi-smooth coefficients under a character twist and inverse transpose. -/

noncomputable section

namespace Langlands.GodementJacquet

open Whittaker HarmonicAnalysis GeneralLinear RankinSelberg

universe uG uF uV

section Twist

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The literal character multiplier on scalar group functions. -/
def coefficientTwist (χ : G →* ℂˣ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := (χ g : ℂ) * f g
  map_add' f h := by ext g; simp [mul_add]
  map_smul' c f := by ext g; simp [mul_left_comm]

omit [TopologicalSpace G] in
@[simp] theorem coefficientTwist_apply (χ : G →* ℂˣ) (f : G → ℂ) (g : G) :
    coefficientTwist χ f g = (χ g : ℂ) * f g := rfl

/-- Open-kernel twisting carries all actual bi-smooth coefficients, including
their finite linear combinations, to those of the actual twisted action. -/
theorem map_biSmoothMatrixCoefficients_twist_le
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (σ : Representation ℂ G V) :
    (biSmoothMatrixCoefficients σ).map (coefficientTwist χ) ≤
      biSmoothMatrixCoefficients (Langlands.twist χ σ) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩
  have hχinv : IsOpen ((χ⁻¹).ker : Set G) := by
    have hk : (χ⁻¹).ker = χ.ker := by ext g; simp
    simpa only [hk] using hχ
  let ℓT : SmoothDual (Langlands.twist χ σ) :=
    ⟨ℓ.val, by
      rw [dual_twist]
      exact (isSmoothVector_twist_iff χ⁻¹ σ.dual hχinv ℓ.val).mpr
        ℓ.property⟩
  let vT : smoothVectors (Langlands.twist χ σ) :=
    ⟨v.val, (isSmoothVector_twist_iff χ σ hχ v.val).mpr v.property⟩
  apply Submodule.subset_span
  refine ⟨ℓT, vT, ?_⟩
  funext g
  change ℓ.val ((χ g : ℂ) • σ g v.val) =
    (χ g : ℂ) * ℓ.val (σ g v.val)
  exact ℓ.val.map_smul _ _

/-- An actual coefficient of the twisted representation, with exactly the
character-multiplied original function. -/
def biSmoothCoefficientTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (σ : Representation ℂ G V) (f : biSmoothMatrixCoefficients σ) :
    biSmoothMatrixCoefficients (Langlands.twist χ σ) :=
  ⟨coefficientTwist χ f.val,
    map_biSmoothMatrixCoefficients_twist_le χ hχ σ
      (Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩)⟩

end Twist

section CharacterCongruence

variable {G : Type uG} [Group G] {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (N : Subgroup G) {θ θ' : N →* ℂˣ}
  (σ : Representation ℂ G V)

/-- Equality of covariance characters transports the actual model action,
not only its underlying equivariant functions. -/
def coefficientModelCharacterEquiv (e : θ = θ') (ℓ : functionals N θ σ) :
    (modelRepresentation σ ℓ).Equiv
      (modelRepresentation σ (functionalsCongr e ℓ)) := by
  cases e
  exact Representation.Equiv.refl _

end CharacterCongruence

section Models

attribute [local irreducible] biSmoothMatrixCoefficients coefficientModel modelRepresentation

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twisting an actual Whittaker-model matrix coefficient gives an actual
coefficient of the coefficient model of the twisted original representation. -/
def determinantTwistModelCoefficient
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Kˣ))
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r (Langlands.twist (χ.comp determinant) σ)
        (determinantTwistFunctionalEquiv ψ χ σ ℓ)).toSubmodule)
      (glModelRepresentation ψ r (Langlands.twist (χ.comp determinant) σ)
        (determinantTwistFunctionalEquiv ψ χ σ ℓ)) :=
  ⟨coefficientTwist (χ.comp determinant) f.val, by
    have hfmap : coefficientTwist (χ.comp (determinant (n := r + 1))) f.val ∈
        (biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
          (glModelRepresentation ψ r σ ℓ)).map
            (coefficientTwist (χ.comp (determinant (n := r + 1)))) :=
      ⟨f.val, f.property, rfl⟩
    have hf := map_biSmoothMatrixCoefficients_twist_le
      (G := GeneralLinear (r + 1) K)
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (χ.comp (determinant (n := r + 1)))
      (determinantCharacter_openKernel (n := r) χ hχ)
      (glModelRepresentation ψ r σ ℓ) hfmap
    exact (biSmoothMatrixCoefficients_equiv
      (G := GeneralLinear (r + 1) K)
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (W := (glCoefficientModel ψ r (Langlands.twist (χ.comp determinant) σ)
        (determinantTwistFunctionalEquiv ψ χ σ ℓ)).toSubmodule)
      (σ := Langlands.twist (χ.comp determinant) (glModelRepresentation ψ r σ ℓ))
      (τ := glModelRepresentation ψ r (Langlands.twist (χ.comp determinant) σ)
        (determinantTwistFunctionalEquiv ψ χ σ ℓ))
      (determinantTwistModelEquiv ψ χ σ ℓ)).le hf⟩

@[simp] theorem determinantTwistModelCoefficient_apply
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Kˣ))
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ))
    (g : GeneralLinear (r + 1) K) :
    (determinantTwistModelCoefficient ψ χ hχ σ ℓ f).val g =
      (χ (determinant g) : ℂ) * f.val g := rfl

/-- Inverse transpose gives an actual coefficient of the constructed dual
coefficient image; no original-carrier/model equivalence is assumed. -/
def iotaModelCoefficient
    (ψ : UnitaryAdditiveCharacter K)
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    biSmoothMatrixCoefficients
      (V := (coefficientModel (inverseTransposePullback σ)
        (dualFunctional ψ σ ℓ)).toSubmodule)
      (modelRepresentation (inverseTransposePullback σ) (dualFunctional ψ σ ℓ)) :=
  ⟨coefficientIota f.val, by
    have hfmap : coefficientIota f.val ∈
        (biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
          (glModelRepresentation ψ r σ ℓ)).map
            (coefficientPullback (inverseTranspose (r + 1) K).toMonoidHom) :=
      ⟨f.val, f.property, rfl⟩
    have hf : coefficientIota f.val ∈
        biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
          (inverseTransposePullback (glModelRepresentation ψ r σ ℓ)) :=
      map_biSmoothMatrixCoefficients_le
        (G := GeneralLinear (r + 1) K) (H := GeneralLinear (r + 1) K)
        (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
        (glModelRepresentation ψ r σ ℓ)
        (inverseTranspose (r + 1) K).toMonoidHom
        (continuous_inverseTranspose (r + 1) K)
        hfmap
    exact (biSmoothMatrixCoefficients_equiv
      (G := GeneralLinear (r + 1) K)
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (W := (coefficientModel (inverseTransposePullback σ)
        (dualFunctional ψ σ ℓ)).toSubmodule)
      (σ := inverseTransposePullback (glModelRepresentation ψ r σ ℓ))
      (τ := modelRepresentation (inverseTransposePullback σ) (dualFunctional ψ σ ℓ))
      (dualModelEquiv ψ σ ℓ)).le hf⟩

/-- Recast the same actual inverse-transpose coefficient image as the
standard image for the inverse additive character. -/
def iotaScaledModelCoefficient
    (ψ : UnitaryAdditiveCharacter K)
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    biSmoothMatrixCoefficients
      (V := (glCoefficientModel (ψ.scale (-1)) r (inverseTransposePullback σ)
        (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
          (dualFunctional ψ σ ℓ))).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r (inverseTransposePullback σ)
        (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
          (dualFunctional ψ σ ℓ))) :=
  ⟨coefficientIota f.val, by
    exact (biSmoothMatrixCoefficients_equiv
      (G := GeneralLinear (r + 1) K)
      (V := (coefficientModel (inverseTransposePullback σ)
        (dualFunctional ψ σ ℓ)).toSubmodule)
      (W := (glCoefficientModel (ψ.scale (-1)) r (inverseTransposePullback σ)
        (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
          (dualFunctional ψ σ ℓ))).toSubmodule)
      (coefficientModelCharacterEquiv (upperUnipotent (r + 1) K)
        (inverseTransposePullback σ) (standardCharacter_scale_neg_one ψ r).symm
        (dualFunctional ψ σ ℓ))).le (iotaModelCoefficient ψ σ ℓ f).property⟩

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- The inverse transpose of the determinant-twisted scalar coefficient has
exactly the inverse determinant character and the unchanged iota coefficient. -/
theorem coefficientIota_determinantTwist (χ : Kˣ →* ℂˣ)
    (f : GeneralLinear (r + 1) K → ℂ) :
    coefficientIota (coefficientTwist (χ.comp determinant) f) =
      coefficientTwist (χ⁻¹.comp determinant) (coefficientIota f) := by
  funext g
  change (χ (determinant (inverseTranspose (r + 1) K g)) : ℂ) *
      f (inverseTranspose (r + 1) K g) =
    (χ⁻¹ (determinant g) : ℂ) * f (inverseTranspose (r + 1) K g)
  congr 1
  have hd : determinant (inverseTranspose (r + 1) K g) = (determinant g)⁻¹ := by
    apply Units.ext
    change Matrix.det (g⁻¹ : GeneralLinear (r + 1) K).val.transpose =
      Matrix.det (g⁻¹ : GeneralLinear (r + 1) K).val
    exact Matrix.det_transpose _
  rw [hd, map_inv, MonoidHom.inv_apply]

/-- The exact transformed twisted function is an actual matrix coefficient
of a standard-character coefficient image on the constructed pullback. -/
def iotaDeterminantTwistModelCoefficient
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Kˣ))
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)) :
    biSmoothMatrixCoefficients
      (V := (glCoefficientModel (ψ.scale (-1)) r
        (inverseTransposePullback (Langlands.twist (χ.comp determinant) σ))
        (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
          (dualFunctional ψ (Langlands.twist (χ.comp determinant) σ)
            (determinantTwistFunctionalEquiv ψ χ σ ℓ)))).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r
        (inverseTransposePullback (Langlands.twist (χ.comp determinant) σ))
        (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
          (dualFunctional ψ (Langlands.twist (χ.comp determinant) σ)
            (determinantTwistFunctionalEquiv ψ χ σ ℓ)))) :=
  iotaScaledModelCoefficient ψ (Langlands.twist (χ.comp determinant) σ)
    (determinantTwistFunctionalEquiv ψ χ σ ℓ)
    (determinantTwistModelCoefficient ψ χ hχ σ ℓ f)

@[simp] theorem iotaDeterminantTwistModelCoefficient_apply
    (ψ : UnitaryAdditiveCharacter K) (χ : Kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Kˣ))
    (σ : Representation ℂ (GeneralLinear (r + 1) K) V)
    (ℓ : glFunctionals ψ r σ)
    (f : biSmoothMatrixCoefficients (V := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ))
    (g : GeneralLinear (r + 1) K) :
    (iotaDeterminantTwistModelCoefficient ψ χ hχ σ ℓ f).val g =
      (χ⁻¹ (determinant g) : ℂ) * coefficientIota f.val g :=
  congrFun (coefficientIota_determinantTwist χ f.val) g

end Models
end Langlands.GodementJacquet
