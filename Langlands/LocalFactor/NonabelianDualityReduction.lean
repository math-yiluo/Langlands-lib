import Langlands.LocalFactor.NonabelianDualityStatement
import Langlands.Representation.Twist.DualProof

/-!
# Algebraic reduction of spectral duality to fixed-Haar duality

These identities use the actual continuous exact virtual group. The fixed-Haar
functional equation remains an explicit premise of the spectral reduction.
-/

noncomputable section

universe uG uV uF

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The continuous twist takes genuine classes to the corresponding actual
twisted representation class. -/
@[simp]
theorem continuousTwist_ofRepresentation (χ : G →ₜ* ℂˣ)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G // A.IsContinuous}) :
    continuousTwist χ (ofRepresentation _ A) =
      ofRepresentation _
        ⟨FiniteRepresentation.twist χ.toMonoidHom A.val,
          FiniteRepresentation.isContinuous_twist χ A.property⟩ :=
  twist_ofRepresentation _ _ _ _ A

variable [IsTopologicalGroup G]

/-- Contragredients invert the actual continuous character twist, after descent
through the short-exact-sequence quotient. -/
theorem continuousDual_continuousTwist (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousDual (continuousTwist χ x) =
      continuousTwist χ⁻¹ (continuousDual x) := by
  have h : (continuousDual.{uG, uV} (G := G)).toLinearMap.comp
      (continuousTwist χ).toLinearMap =
      (continuousTwist χ⁻¹).toLinearMap.comp continuousDual.toLinearMap := by
    apply hom_ext (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change continuousDual (continuousTwist χ (ofRepresentation _ A)) =
        continuousTwist χ⁻¹ (continuousDual (ofRepresentation _ A))
      rw [continuousTwist_ofRepresentation, continuousDual_ofRepresentation,
        continuousDual_ofRepresentation, continuousTwist_ofRepresentation]
      apply ofRepresentation_eq_of_equiv _
      change (Langlands.twist χ.toMonoidHom A.val.representation).dual.Equiv
        (Langlands.twist (χ⁻¹).toMonoidHom A.val.representation.dual)
      rw [Langlands.dual_twist]
      exact Representation.Equiv.refl _
  exact LinearMap.congr_fun h x

/-- The character twist of the actual contragredient, as an automorphism of
the continuous exact virtual group. This is the operation in fixed-Haar
duality when the character is the actual norm. -/
def continuousTwistedDual (χ : G →ₜ* ℂˣ) :
    ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) ≃ₗ[ℤ]
      ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous) :=
  continuousDual.trans (continuousTwist χ)

@[simp]
theorem continuousTwistedDual_apply (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousTwistedDual χ x = continuousTwist χ (continuousDual x) := rfl

/-- Twisting the contragredient by any fixed character is involutive. -/
@[simp]
theorem continuousTwistedDual_apply_apply (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    continuousTwistedDual χ (continuousTwistedDual χ x) = x := by
  simp only [continuousTwistedDual_apply, continuousDual_continuousTwist,
    continuousDual_apply_apply]
  exact (continuousTwist χ).apply_symm_apply x

/-- The twisted contragredient preserves the actual integer dimension. -/
@[simp]
theorem degree_continuousTwistedDual (χ : G →ₜ* ℂˣ)
    (x : ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.IsContinuous)) :
    degree _ (continuousTwistedDual χ x) = degree _ x := by
  rw [continuousTwistedDual_apply]
  exact (degree_twist _ _ _ _ _).trans (degree_continuousDual x)

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.CommonClosureSpectral

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Negating the spectral parameter inverts the actual continuous character. -/
theorem character_neg (E : Extension F) (s : ℂ) :
    character F E (-s) = (character F E s)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change SpectralTwist.character _ _ _ (-s) * SpectralTwist.character _ _ _ s = 1
  rw [← SpectralTwist.character_add, neg_add_cancel, SpectralTwist.character_zero]

/-- At parameter one, the spectral character is the actual restricted norm. -/
theorem character_one (E : Extension F) :
    character F E 1 = CommonClosureWeilDeligne.normCharacter F E := by
  ext w
  rw [character_apply, CommonClosureWeilDeligne.normCharacter_apply]
  have hq : Complex.exp (-(Real.log (baseCardinality F) : ℂ)) =
      (baseCardinality F : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (baseCardinality_pos F)]
  simp only [neg_one_mul, hq, inv_zpow, zpow_neg]
  rfl

/-- The exact contragredient negates every complex spectral twist. -/
theorem continuousDual_virtualTwist (E : Extension F)
    (s : ℂ) (x : Virtual.{uF, uV} F E) :
    ExactGrothendieckGroup.continuousDual (virtualTwist F E s x) =
      virtualTwist F E (-s) (ExactGrothendieckGroup.continuousDual x) := by
  change ExactGrothendieckGroup.continuousDual
      (ExactGrothendieckGroup.continuousTwist (character F E s) x) =
    ExactGrothendieckGroup.continuousTwist (character F E (-s))
      (ExactGrothendieckGroup.continuousDual x)
  rw [ExactGrothendieckGroup.continuousDual_continuousTwist, character_neg]

/-- Applying the actual norm twist to the dual of a spectral twist gives the
complementary parameter, with no change of field or representation universe. -/
theorem normTwist_continuousDual_virtualTwist (E : Extension F)
    (s : ℂ) (x : Virtual.{uF, uV} F E) :
    ExactGrothendieckGroup.continuousTwist
        (CommonClosureWeilDeligne.normCharacter F E)
        (ExactGrothendieckGroup.continuousDual (virtualTwist F E s x)) =
      virtualTwist F E (1 - s) (ExactGrothendieckGroup.continuousDual x) := by
  rw [continuousDual_virtualTwist, ← character_one]
  change virtualTwist F E 1
      (virtualTwist F E (-s) (ExactGrothendieckGroup.continuousDual x)) = _
  rw [virtualTwist_add, ← sub_eq_add_neg]

end Langlands.LocalFactor.CommonClosureSpectral

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure CommonClosureSpectral VirtualRepresentation

/-- The fixed-Haar functional equation implies the complete spectral equation
by applying it to the actual spectral twist. -/
theorem spectralDuality_of_fixedHaarDuality
    (h : FixedHaarDualityStatement.{uF, uV}) :
    SpectralDualityStatement.{uF, uV} := by
  intro p hp F e ε hε E
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ μ' hμ x s
  have hx := h F e ε hε E ψ μ μ' hμ (virtualTwist F E s x)
  rw [normTwist_continuousDual_virtualTwist] at hx
  exact hx

/-- The fixed-Haar equation is the parameter-zero case of spectral duality. -/
theorem fixedHaarDuality_of_spectralDuality
    (h : SpectralDualityStatement.{uF, uV}) :
    FixedHaarDualityStatement.{uF, uV} := by
  intro p hp F e ε hε E
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ μ' hμ x
  have hx := h F e ε hε E ψ μ μ' hμ x 0
  simp only [conditionalDeligneValue, virtualTwist_zero, sub_zero] at hx
  change ε E ψ μ x * ε E (ψ.scale (-1)) μ'
    (ExactGrothendieckGroup.continuousTwist (character F E 1)
      (ExactGrothendieckGroup.continuousDual x)) = 1 at hx
  rw [character_one] at hx
  exact hx

/-- The two published clauses have the same mathematical content. -/
theorem fixedHaarDuality_iff_spectralDuality :
    FixedHaarDualityStatement.{uF, uV} ↔ SpectralDualityStatement.{uF, uV} :=
  ⟨spectralDuality_of_fixedHaarDuality, fixedHaarDuality_of_spectralDuality⟩

/-- To finish the published aggregate target it suffices to prove the unchanged
fixed-Haar clause; this reduction does not supply that clause. -/
theorem dualFunctionalEquation_of_fixedHaarDuality
    (h : FixedHaarDualityStatement.{uF, uV}) :
    DualFunctionalEquationStatement.{uF, uV} :=
  ⟨h, spectralDuality_of_fixedHaarDuality h⟩

end Langlands.LocalFactor.NonabelianSystem
