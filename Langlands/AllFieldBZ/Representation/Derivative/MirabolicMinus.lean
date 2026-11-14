import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicCharacter
import Langlands.Representation.Derivative.MirabolicMinus

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicMinus`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicMinus` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter ker_psiMinusQuotient phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
universe uR uG uH uV uF

section Pullback
variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R]
variable [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

end Pullback
variable {F : LocalFieldPackage.{uF}}

/-! ## Unnormalized Psi-minus -/

/-- Unnormalized `Ψ⁻`: localize at the trivial character of `V_(n+1)`, then restrict
the descended Levi action along `GL_n ≃ₜ* leviSubgroup n`. -/
def psiMinusUnnormalized (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact Jacquet.Localization.smoothFunctor (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
      leviSubgroup_le_normalizer
      (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer) ⋙
    continuousPullbackFunctor (leviContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
      (leviContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- The canonical quotient map onto the actual `Ψ⁻` carrier. -/
abbrev psiMinusQuotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      A →ₗ[ℂ] Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1 := by
  letI := T.topology
  exact fun A => Jacquet.Localization.mk A.representation (radical n F.Carrier) 1

theorem psiMinusQuotient_surjective (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Surjective (psiMinusQuotient T n A) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.mk_surjective A.representation (radical n F.Carrier) 1

theorem ker_psiMinusQuotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      LinearMap.ker (psiMinusQuotient T n A) =
        Jacquet.Localization.relations A.representation (radical n F.Carrier) 1 := by
  let := T.topology
  intro A
  exact Jacquet.Localization.ker_mk A.representation (radical n F.Carrier) 1

/-- Radical elements act trivially on `Ψ⁻` quotient classes. -/
theorem psiMinusQuotient_radical (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (u : radical n F.Carrier) (v : A),
      psiMinusQuotient T n A (A.representation (u : mirabolic n F.Carrier) v) =
        psiMinusQuotient T n A v := by
  let := T.topology
  intro A u v
  rw [Jacquet.Localization.mk_apply_subgroup]
  simp

/-! ## Unnormalized Phi-minus -/

/-- Unnormalized `Φ⁻`: localize at `θ_ψ` on `V_(n+2)`, then restrict the descended
successor action along `P_(n+1) ≃ₜ* successorSubgroup n`. -/
def phiMinusUnnormalized (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact Jacquet.Localization.smoothFunctor (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n)
      (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer
      (theta_isInvariant ψ n) ⋙
    continuousPullbackFunctor (successorContinuousEquiv (n := n) (F := F.Carrier)).toMonoidHom
      (successorContinuousEquiv (n := n) (F := F.Carrier)).continuous

/-- The canonical quotient map onto the actual `Φ⁻` carrier. -/
abbrev phiMinusQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      A →ₗ[ℂ] Jacquet.Localization.Coinvariants A.representation (radical (n + 1) F.Carrier)
        (T.mirabolicTheta ψ n) := by
  letI := T.topology
  exact fun A => Jacquet.Localization.mk A.representation (radical (n + 1) F.Carrier)
    (T.mirabolicTheta ψ n)

theorem phiMinusQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier),
      Function.Surjective (phiMinusQuotient T ψ n A) := by
  let := T.topology
  intro A
  exact Jacquet.Localization.mk_surjective A.representation (radical (n + 1) F.Carrier) _

/-- Radical elements act on `Φ⁻` quotient classes through `θ_ψ`. -/
theorem phiMinusQuotient_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (u : radical (n + 1) F.Carrier) (v : A),
      phiMinusQuotient T ψ n A (A.representation (u : mirabolic (n + 1) F.Carrier) v) =
        (T.mirabolicTheta ψ n u : ℂ) • phiMinusQuotient T ψ n A v := by
  let := T.topology
  intro A u v
  exact Jacquet.Localization.mk_apply_subgroup A.representation _ _ u v

/-! ## Determinant normalization -/

/-- The explicit `Ψ⁻` normalization character `|det|^(-1/2)` on `GL_n`. -/
abbrev psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℂˣ :=
  realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ))

/-- The explicit `Φ⁻` normalization character `|det|^(-1/2)` on `P_(n+1)`. -/
abbrev phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    mirabolic n F.Carrier →* ℂˣ :=
  realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
    (-(1 / 2 : ℝ))

theorem isOpen_ker_psiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((psiMinusCharacter T n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact isOpen_ker_realPowerCharacter _ (T.isOpen_ker_determinantNorm n) _

theorem isOpen_ker_phiMinusCharacter (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen ((phiMinusCharacter T n).ker : Set (mirabolic n F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  apply isOpen_ker_realPowerCharacter
  exact (T.isOpen_ker_determinantNorm (n + 1)).preimage continuous_subtype_val

/-- Determinant-normalized `Ψ⁻`: unnormalized `Ψ⁻` twisted by `|det|^(-1/2)`. -/
def psiMinus (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact psiMinusUnnormalized T n ⋙
    SmoothRep.twistFunctor (psiMinusCharacter T n) (isOpen_ker_psiMinusCharacter T n)

/-- Determinant-normalized `Φ⁻`: unnormalized `Φ⁻` twisted by `|det|^(-1/2)`. -/
def phiMinus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact phiMinusUnnormalized T ψ n ⋙
    SmoothRep.twistFunctor (phiMinusCharacter T n) (isOpen_ker_phiMinusCharacter T n)

/-- `g • q(v) = |det g|^(-1/2) q(levi g • v)` for normalized `Ψ⁻`. -/
theorem psiMinus_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : GeneralLinear n F.Carrier)
      (v : A),
      ((psiMinus T n).obj A).representation g (psiMinusQuotient T n A v) =
        (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
          psiMinusQuotient T n A (A.representation (levi g) v) := by
  intros
  rfl

/-- The normalized action is the character value times the unnormalized action. -/
theorem psiMinus_action_eq_smul (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : GeneralLinear n F.Carrier)
      (w : (psiMinusUnnormalized T n).obj A),
      ((psiMinus T n).obj A).representation g w =
        (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
          ((psiMinusUnnormalized T n).obj A).representation g w := by
  intros
  rfl

/-- The normalized functor keeps the quotient-induced linear maps. -/
theorem psiMinus_map_quotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((psiMinus T n).map f) (psiMinusQuotient T n A v) =
        psiMinusQuotient T n B (SmoothRep.hom f v) := by
  intros
  rfl

/-- `h • q(v) = |det h|^(-1/2) q(successor h • v)` for normalized `Φ⁻`. -/
theorem phiMinus_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (h : mirabolic n F.Carrier) (v : A),
      ((phiMinus T ψ n).obj A).representation h (phiMinusQuotient T ψ n A v) =
        (realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
            (-(1 / 2 : ℝ)) h : ℂ) •
          phiMinusQuotient T ψ n A (A.representation (successor h) v) := by
  intros
  rfl

/-- The normalized functor keeps the quotient-induced linear maps. -/
theorem phiMinus_map_quotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((phiMinus T ψ n).map f) (phiMinusQuotient T ψ n A v) =
        phiMinusQuotient T ψ n B (SmoothRep.hom f v) := by
  intros
  rfl

end Langlands.AllFieldBZ.Derivative.Mirabolic
