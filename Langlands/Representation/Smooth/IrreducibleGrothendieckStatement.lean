import Langlands.Representation.Smooth.IrreducibleRealization

/-!
# Bijectivity of the irreducible exact finite-length realization: statement

The proposition that the canonical integer-linear map from the free lattice on
genuine isomorphism classes of actual irreducible smooth representations to the
exact Grothendieck group of finite-length smooth representations is bijective,
with its actual `GL_n` and product-Levi specializations. Bijectivity is not
proved or assumed here, and no inverse or multiplicity function is chosen.
-/

noncomputable section

universe uR uG uV uF

namespace Langlands.SmoothRep

variable (k : Type uR) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]

/-- The canonical realization `realizeIrreducibles k G` of integral combinations of
genuine irreducible smooth classes in the exact finite-length Grothendieck group,
the quotient by all actual short exact sequences, is bijective. No admissibility
is assumed and the carrier universe `uV` is independent. -/
def IrreducibleGrothendieckStatement : Prop :=
  Function.Bijective (realizeIrreducibles.{uR, uG, uV} k G)

end Langlands.SmoothRep

namespace Langlands.GeneralLinear

variable (n : ℕ) (F : Type uF) [Field F] [TopologicalSpace F]

/-- Bijectivity of the irreducible realization for complex smooth representations
of the actual `GL_n(F)` with carriers in `Type (max uF uV)`, for every rank. -/
def IrreducibleGrothendieckStatement : Prop :=
  Function.Bijective (realizeIrreducibles.{uV, uF} n F)

/-- The `GL_n(F)` proposition is the generic one at `ℂ` and `GeneralLinear n F`. -/
theorem irreducibleGrothendieckStatement_iff :
    IrreducibleGrothendieckStatement.{uV, uF} n F ↔
      SmoothRep.IrreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (GeneralLinear n F) :=
  Iff.rfl

/-- Direct specialization from the generic proposition; its truth is not asserted. -/
theorem IrreducibleGrothendieckStatement.of_smoothRep
    (h : SmoothRep.IrreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (GeneralLinear n F)) :
    IrreducibleGrothendieckStatement.{uV, uF} n F :=
  h

namespace BlockShape

variable {n} (B : BlockShape n)

/-- Bijectivity of the irreducible realization for complex smooth representations
of the actual product Levi `B.Levi F` with carriers in `Type (max uF uV)`. Its
irreducible objects are arbitrary; no tensor factorization is assumed. -/
def IrreducibleGrothendieckStatement : Prop :=
  Function.Bijective (B.realizeIrreducibles.{uV, uF} F)

/-- The product-Levi proposition is the generic one at `ℂ` and `B.Levi F`. -/
theorem irreducibleGrothendieckStatement_iff :
    B.IrreducibleGrothendieckStatement.{uV, uF} F ↔
      SmoothRep.IrreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (B.Levi F) :=
  Iff.rfl

/-- Direct specialization from the generic proposition; its truth is not asserted. -/
theorem IrreducibleGrothendieckStatement.of_smoothRep
    (h : SmoothRep.IrreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ (B.Levi F)) :
    B.IrreducibleGrothendieckStatement.{uV, uF} F :=
  h

end BlockShape
end Langlands.GeneralLinear
