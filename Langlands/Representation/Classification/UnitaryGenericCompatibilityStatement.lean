import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Unitary.Twist
import Langlands.Representation.Parabolic.NormalizedCompatibilityStatement
import Langlands.Representation.Parabolic.NormalizedInductionStatement

/-!
# Hermitian, twist, ordinary dual and scalar compatibility of inducing parameters

These are proposition definitions on actual smooth representations. In particular,
a conjugate-linear equivalence to the smooth dual expresses Hermitian duality;
it is not an ordinary linear self-contragredience assertion.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An invariant positive form on an admissible smooth representation induces
an equivariant conjugate-linear bijection onto its actual smooth dual. -/
def UnitaryAdmissibleHermitianClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ (δ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      IsAdmissible δ.representation →
      ∀ b : InvariantPositiveForm δ.representation,
        ∃ E : δ ≃ₗ⋆[ℂ] SmoothDual δ.representation,
          (∀ g v, E (δ.representation g v) =
            smoothContragredient δ.representation g (E v)) ∧
          ∀ v w, smoothDualPairing δ.representation (E v) w = b.inner v w

/-- For a unitary square-integrable block, the Hermitian partner of `ν^s δ`
is `ν^(-s) δ`. The pairing is the original positive form, not a form claimed
invariant on `ν^s δ` itself. -/
def UnitaryBlockRealTwistHermitianClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ (δ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible δ.representation →
      T.IsSquareIntegrable δ.representation →
      ∀ (b : InvariantPositiveForm δ.representation) (s : ℝ),
        ∃ E : δ ≃ₗ⋆[ℂ] SmoothDual (T.segmentFactor δ s).representation,
          (∀ g v, E ((T.segmentFactor δ (-s)).representation g v) =
            smoothContragredient (T.segmentFactor δ s).representation g (E v)) ∧
          ∀ v w, smoothDualPairing (T.segmentFactor δ s).representation (E v) w =
            b.inner v w

/-- Ordinary smooth duality sends `(s, δ)` to `(-s, δ^∨)`. -/
def RealTwistOrdinaryDualClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ (δ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ),
      Nonempty (Representation.Equiv
        (smoothContragredient (T.segmentFactor δ s).representation)
        (realPowerTwist (T.determinantNorm n) (-s)
          (smoothContragredient δ.representation)))

/-- The ordinary dual is again an irreducible unitary square-integrable block.
This does not identify a block linearly with its own ordinary dual. -/
def UnitaryBlockOrdinaryDualClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ δ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      Representation.IsIrreducible δ.representation →
      IsUnitarizable δ.representation → T.IsSquareIntegrable δ.representation →
      Representation.IsIrreducible (smoothContragredient δ.representation) ∧
      IsUnitarizable (smoothContragredient δ.representation) ∧
      T.IsSquareIntegrable (smoothContragredient δ.representation)

/-- Normalized induction from the same upper block parabolic commutes with
ordinary duality, changing every exponent's sign and dualizing every block. -/
def TwistedProductOrdinaryDualClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    ∀ (δ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (s : Fin B.length → ℝ),
      (∀ i, IsAdmissible (δ i).representation) →
      let δv := fun i => SmoothRep.of (smoothContragredient (δ i).representation)
        (isSmooth_smoothContragredient (δ i).representation)
      Nonempty (Representation.Equiv
        (smoothContragredient (T.twistedProductInduced B δ s).representation)
        (T.twistedProductInduced B δv (fun i => -s i)).representation)

/-- A common smooth determinant character twists every block of the actual
upper normalized product; the exponents remain unchanged. -/
def TwistedProductCharacterTwistClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
    ∀ (χ : Induction.SmoothCharacter ℂ F.Carrierˣ),
      let χr := fun r => χ.toMonoidHom.comp
        (determinant : GeneralLinear r F.Carrier →* F.Carrierˣ)
      let hχr : ∀ r, IsOpen ((χr r).ker : Set (GeneralLinear r F.Carrier)) :=
        fun r => χ.isOpen_ker.preimage (T.generalLinearDeterminant r).continuous
      ∀ (δ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
        (s : Fin B.length → ℝ),
        Nonempty (Representation.Equiv
          (twist (χr n) (T.twistedProductInduced B δ s).representation)
          (T.twistedProductInduced B
            (fun i => (δ i).twist (χr (B.size i)) (hχr (B.size i))) s).representation)

/-- Unit-modulus smooth determinant characters preserve and reflect all three
conditions on a unitary square-integrable inducing block. -/
def UnitaryBlockCharacterTwistClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (χ : Induction.SmoothCharacter ℂ F.Carrierˣ),
      (∀ z, ‖(χ.toMonoidHom z : ℂ)‖ = 1) →
      ∀ δ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
        let ρχ := twist (χ.toMonoidHom.comp determinant) δ.representation
        (Representation.IsIrreducible ρχ ∧ IsUnitarizable ρχ ∧ T.IsSquareIntegrable ρχ) ↔
        (Representation.IsIrreducible δ.representation ∧
          IsUnitarizable δ.representation ∧ T.IsSquareIntegrable δ.representation)

/-- The scalar character of the normalized product has the full rank-weighted
real exponent, and its pointwise value is explicitly the product formula. -/
def TwistedProductCentralCharacterClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ B : BlockShape n,
    ∀ (δ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (s : Fin B.length → ℝ) (ω : Fin B.length → F.Carrierˣ →* ℂˣ),
      (∀ i, HasScalarCharacter (δ i).representation GeneralLinear.scalar (ω i)) →
      let a : ℝ := ∑ i, (B.size i : ℝ) * s i
      let Ω : F.Carrierˣ →* ℂˣ := (∏ i, ω i) * realPowerCharacter T.normalizedAbsUnits a
      HasScalarCharacter (T.twistedProductInduced B δ s).representation
          GeneralLinear.scalar Ω ∧
        (∀ z : F.Carrierˣ, (Ω z : ℂ) =
          (∏ i, (ω i z : ℂ)) * ((T.normalizedAbs z ^ a : ℝ) : ℂ)) ∧
        ∀ z : F.Carrierˣ, (Ω z : ℂ) =
          ∏ i, (ω i z : ℂ) *
            (T.determinantPowerCharacter (B.size i) (s i) (GeneralLinear.scalar z) : ℂ)

/-- A determinant twist multiplies the scalar character by `χ^n`; ordinary
smooth duality inverts it. No unitary restriction is imposed on `χ`. -/
def ScalarCharacterTwistDualClause : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (ω : F.Carrierˣ →* ℂˣ) (χ : Induction.SmoothCharacter ℂ F.Carrierˣ),
      HasScalarCharacter π.representation GeneralLinear.scalar ω →
      HasScalarCharacter (twist (χ.toMonoidHom.comp determinant) π.representation)
          GeneralLinear.scalar (ω * χ.toMonoidHom ^ n) ∧
        HasScalarCharacter (smoothContragredient π.representation)
          GeneralLinear.scalar ω⁻¹

/-- The focused compatibility installment for one actual finite p-adic field.
No existence, uniqueness or generic classification conclusion is assumed. -/
def UnitaryGenericCompatibilityStatement : Prop :=
  UnitaryAdmissibleHermitianClause.{uF, uV} F T ∧
  UnitaryBlockRealTwistHermitianClause.{uF, uV} F T ∧
  RealTwistOrdinaryDualClause.{uF, uV} F T ∧
  UnitaryBlockOrdinaryDualClause.{uF, uV} F T ∧
  TwistedProductOrdinaryDualClause.{uF, uV} F T ∧
  TwistedProductCharacterTwistClause.{uF, uV} F T ∧
  UnitaryBlockCharacterTwistClause.{uF, uV} F T ∧
  TwistedProductCentralCharacterClause.{uF, uV} F T ∧
  ScalarCharacterTwistDualClause.{uF, uV} F T

/-- Compatibility over every prime, finite p-adic extension, and compatible
topological realization; field and block-carrier universes are independent. -/
def AllPadicUnitaryGenericCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    UnitaryGenericCompatibilityStatement.{uF, uV} F T

end Langlands.Classification
