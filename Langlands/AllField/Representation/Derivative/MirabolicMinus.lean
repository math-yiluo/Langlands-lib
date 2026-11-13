import Langlands.Representation.Derivative.MirabolicMinus
import Langlands.AllField.Group.GL.NormalizedCharacter
import Langlands.AllField.Representation.Derivative.MirabolicCharacter
/-!
# Mirabolic minus localization functors

The unnormalized Bernstein–Zelevinsky functors `Ψ⁻ : P_(n+1) → GL_n` and
`Φ⁻ : P_(n+2) → P_(n+1)` act on the actual character-localized quotients by the
actual radicals. Their determinant-normalized versions twist the descended action by
the inverse half power of the residue-normalized determinant character. No Haar
automorphism modulus is identified with that character here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinusUnnormalized_action
open Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative
open Langlands.AllField.Derivative

open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis

universe uR uG uH uV uF

section Pullback

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R]
variable [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

end Pullback

variable {F : Type uF} [Field F]

/-! ## Unnormalized Psi-minus -/

/-! ## Unnormalized Phi-minus -/

/-- Unnormalized `Φ⁻`: localize at `θ_ψ` on `V_(n+2)`, then restrict the descended
successor action along `P_(n+1) ≃ₜ* successorSubgroup n`. -/
def phiMinusUnnormalized (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F) := by
  letI := T.topology
  exact Jacquet.Localization.smoothFunctor (radical (n + 1) F) (T.mirabolicTheta ψ n)
      (successorSubgroup n F) successorSubgroup_le_normalizer
      (theta_isInvariant ψ n) ⋙
    continuousPullbackFunctor (successorContinuousEquiv (n := n) (F := F)).toMonoidHom
      (successorContinuousEquiv (n := n) (F := F)).continuous

/-- The canonical quotient map onto the actual `Φ⁻` carrier. -/
abbrev phiMinusQuotient (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F)) →
      A →ₗ[ℂ] Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F)
        (T.mirabolicTheta ψ n) := by
  letI := T.topology
  exact fun A => Jacquet.Localization.mk A.representation (radical (n + 1) F)
    (T.mirabolicTheta ψ n)

theorem phiMinusQuotient_surjective (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F),
      Function.Surjective (phiMinusQuotient T ψ n A) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.mk_surjective A.representation (radical (n + 1) F) _

/-- Radical elements act on `Φ⁻` quotient classes through `θ_ψ`. -/
theorem phiMinusQuotient_radical (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F))
      (u : radical (n + 1) F) (v : A),
      phiMinusQuotient T ψ n A (A.representation (u : mirabolic (n + 1) F) v) =
        (T.mirabolicTheta ψ n u : ℂ) • phiMinusQuotient T ψ n A v := by
  let := T.topology
  intro A u v
  exact Jacquet.Localization.mk_apply_subgroup A.representation _ _ u v

/-- `h • q(v) = q(successor h • v)` for unnormalized `Φ⁻`. -/
theorem phiMinusUnnormalized_action (T : LocalFieldData F)
    (ψ : @UnitaryAdditiveCharacter F _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F))
      (h : mirabolic n F) (v : A),
      ((phiMinusUnnormalized T ψ n).obj A).representation h (phiMinusQuotient T ψ n A v) =
        phiMinusQuotient T ψ n A (A.representation (successor h) v) := by
  intros
  rfl

/-! ## Determinant normalization -/

end Langlands.AllField.Derivative.Mirabolic
