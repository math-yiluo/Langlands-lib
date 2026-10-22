import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.LocalField.Definitions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units

/-!
# Constituent compatibility statements for the classification branch

These are proposition definitions, not proofs. They concern actual intertwiners
and actual general linear groups. They neither construct parabolic induction
nor assert its classification.
-/

namespace Langlands.Classification

universe uG uV uF

section Algebraic

variable (G : Type uG) [Group G]

/-- Common character twisting preserves the actual irreducible quotient,
subrepresentation, head and socle relations. -/
def TwistConstituentCompatibilityFor : Prop :=
  ∀ (V W : Type uV) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (π : Representation ℂ G W) (χ : G →* ℂˣ),
    (IsIrreducibleQuotient (twist χ ρ) (twist χ π) ↔
      IsIrreducibleQuotient ρ π) ∧
    (IsIrreducibleSubrepresentation (twist χ ρ) (twist χ π) ↔
      IsIrreducibleSubrepresentation ρ π) ∧
    (IsIrreducibleHead (twist χ ρ) (twist χ π) ↔
      IsIrreducibleHead ρ π) ∧
    (IsIrreducibleSocle (twist χ ρ) (twist χ π) ↔
      IsIrreducibleSocle ρ π)

/-- Uniqueness of an actual simple head or socle implies uniqueness up to
an actual representation isomorphism. No quotient of arbitrary labels is used. -/
def ConstituentIsomorphismUniquenessFor : Prop :=
  ∀ (V W W' : Type uV) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G V) (π : Representation ℂ G W)
    (π' : Representation ℂ G W'),
    (IsIrreducibleHead ρ π → IsIrreducibleHead ρ π' →
      Nonempty (π.Equiv π')) ∧
    (IsIrreducibleSocle ρ π → IsIrreducibleSocle ρ π' →
      Nonempty (π.Equiv π'))

end Algebraic

section GeneralLinear

variable (F : Type uF) [Field F] (n : ℕ)

/-- Scalar matrices act by the specified character. For `n > 0` this is the
central-character formula for the actual general linear group. -/
abbrev HasGLCentralCharacter {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F) V)
    (ω : Fˣ →* ℂˣ) : Prop :=
  HasScalarCharacter ρ (Matrix.GeneralLinearGroup.scalar (Fin n)) ω

/-- Prescribed central characters pass to actual irreducible quotients and
subrepresentations. A determinant twist changes the central character by
`χ^n`, with no omitted rank factor. -/
def GLConstituentCentralCharacterFor : Prop :=
  ∀ (V W : Type uV) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F) V)
    (π : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F) W)
    (ω χ : Fˣ →* ℂˣ),
    (HasGLCentralCharacter F n ρ ω → IsIrreducibleQuotient ρ π →
      HasGLCentralCharacter F n π ω) ∧
    (HasGLCentralCharacter F n ρ ω → IsIrreducibleSubrepresentation ρ π →
      HasGLCentralCharacter F n π ω) ∧
    (HasGLCentralCharacter F n ρ ω →
      HasGLCentralCharacter F n
        (twist (χ.comp Matrix.GeneralLinearGroup.det) ρ) (ω * χ ^ n))

end GeneralLinear

/-- The algebraic compatibility family specialized to every positive rank and
every finite extension of every `ℚ_p`. Module carriers remain arbitrary. -/
def AllPadicGLAlgebraicConstituentCompatibility : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ), 0 < n →
    TwistConstituentCompatibilityFor.{uF, uV}
      (Matrix.GeneralLinearGroup (Fin n) F.Carrier) ∧
    ConstituentIsomorphismUniquenessFor.{uF, uV}
      (Matrix.GeneralLinearGroup (Fin n) F.Carrier) ∧
    GLConstituentCentralCharacterFor.{uV, uF} F.Carrier n

/-- On actual admissible smooth representations of every positive-rank
`GL_n(F)`, smooth contragredience exchanges an irreducible head with an
irreducible socle. The dual is the smooth part of the full algebraic dual. -/
def AllPadicGLContragredientConstituentCompatibility : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ), 0 < n →
    ∀ (V W : Type uV) [AddCommGroup V] [Module ℂ V]
      [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F.Carrier) V)
      (π : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F.Carrier) W),
      IsSmooth ρ → IsAdmissible ρ → IsSmooth π → IsAdmissible π →
      (IsIrreducibleHead ρ π ↔
        IsIrreducibleSocle (smoothContragredient ρ) (smoothContragredient π)) ∧
      (IsIrreducibleSocle ρ π ↔
        IsIrreducibleHead (smoothContragredient ρ) (smoothContragredient π)) ∧
      (∀ (ω : F.Carrierˣ →* ℂˣ),
        HasGLCentralCharacter F.Carrier n ρ ω →
        HasGLCentralCharacter F.Carrier n (smoothContragredient ρ) ω⁻¹)

/-- A coherent prerequisite for twist, dual, and central-character
compatibilities of the special and multisegment constituents. This family
does not assert the existence of any special or Langlands constituent. -/
def AllPadicGLConstituentCompatibility : Prop :=
  AllPadicGLAlgebraicConstituentCompatibility.{uV, uF} ∧
    AllPadicGLContragredientConstituentCompatibility.{uV, uF}

end Langlands.Classification
