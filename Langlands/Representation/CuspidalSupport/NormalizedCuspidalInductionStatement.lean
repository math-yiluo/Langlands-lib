import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Induction.Definitions
import Langlands.Group.GL.BlockModulus

/-! BZ77 cuspidal embedding, finite length, association, and Hom bounds. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- Every irreducible smooth representation embeds in normalized induction
from an irreducible cuspidal representation of an actual standard Levi.
Admissibility is a conclusion, not an input. -/
def CuspidalEmbeddingTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ ω : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
    ω.IsIrreducible → ω.IsAdmissible ∧
    ∃ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation ∧
      ∃ j : ω.representation.IntertwiningMap
          (Induction.smoothInduced (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B)
              (σ.representation.comp (B.leviProjection F.Carrier)))),
        Function.Injective j

/-- Irreducible cuspidal induction has finite group-module length and an
actual composition series with at most the factorial of the block count
many factors. -/
def CuspidalInductionLengthTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B : BlockShape n) (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    let π := Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.representation.comp (B.leviProjection F.Carrier)))
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.asModule ∧
      HasCompositionLengthAtMost (Rep.of π) (Nat.factorial B.length)

/-- Association of irreducible cuspidal inducing data is equivalent to
nonzero Hom, equality of composition factors with multiplicities, and an
actual common irreducible subquotient. The two inducing carrier universes
are independent. -/
def CuspidalInductionAssociationTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B C : BlockShape n)
    (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    τ.IsIrreducible → IsLeviCuspidal C τ.representation →
    let σP := twist (T.parabolicHalfModulus B)
      (σ.representation.comp (B.leviProjection F.Carrier))
    let τP := twist (T.parabolicHalfModulus C)
      (τ.representation.comp (C.leviProjection F.Carrier))
    let π := Induction.smoothInduced (B.parabolic F.Carrier) σP
    let π' := Induction.smoothInduced (C.parabolic F.Carrier) τP
    let A := SmoothRep.of π (Induction.smoothInduced_smooth _ σP)
    let A' := SmoothRep.of π' (Induction.smoothInduced_smooth _ τP)
    let associated := RepresentationsAssociated B C σ.representation τ.representation
    (associated ↔ ∃ f : π.IntertwiningMap π', f ≠ 0) ∧
    (associated ↔ HaveSameJordanHolderFactors (Rep.of π) (Rep.of π')) ∧
    (associated ↔
      ∃ (S : Subrepresentation A.representation)
        (Q : Subrepresentation (SmoothRep.subrepresentation A S).representation)
        (S' : Subrepresentation A'.representation)
        (Q' : Subrepresentation (SmoothRep.subrepresentation A' S').representation),
        (SmoothRep.subquotient A S Q).IsIrreducible ∧
        Nonempty ((SmoothRep.subquotient A S Q).representation.Equiv
          (SmoothRep.subquotient A' S' Q').representation))

/-- The actual intertwiner space is finite dimensional and its dimension is
bounded by the number of minimal Weyl permutations associating the data. -/
def CuspidalInductionHomBoundTheorem : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B C : BlockShape n)
    (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    τ.IsIrreducible → IsLeviCuspidal C τ.representation →
    let π := Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.representation.comp (B.leviProjection F.Carrier)))
    let π' := Induction.smoothInduced (C.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus C)
        (τ.representation.comp (C.leviProjection F.Carrier)))
    FiniteDimensional ℂ (π.IntertwiningMap π') ∧
      Module.finrank ℂ (π.IntertwiningMap π') ≤
        Nat.card (AssociatingPermutations B C σ.representation τ.representation)

/-- The GL_n specialization of BZ77 2.5 and 2.8-2.9 over every actual finite
p-adic extension and every compatible topological realization. -/
def PadicCuspidalInductionTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
      CuspidalEmbeddingTheorem.{uF, uV} F T n ∧
      CuspidalInductionLengthTheorem.{uF, uV} F T n ∧
      CuspidalInductionAssociationTheorem.{uF, uV, uW} F T n ∧
      CuspidalInductionHomBoundTheorem.{uF, uV, uW} F T n

end Langlands.CuspidalSupport
