import Langlands.JacquetLanglands.Relation
import Langlands.Representation.Twist.Definitions
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Statements of the local Jacquet–Langlands correspondence

Proposition-valued statements: the Jacquet–Langlands relation is the graph of a bijection
between isomorphism classes of irreducible essentially square-integrable representations of
`GL_n(F)` and of irreducible admissible representations of `Dˣ` (Deligne–Kazhdan–Vignéras and
Rogawski in characteristic zero, Badulescu in positive characteristic), and it is compatible
with central characters and with twists by `χ ∘ det` and `χ ∘ Nrd`. Nothing here is proved
except the passage from the bundled form to isomorphism classes.
-/

noncomputable section

namespace Langlands.JacquetLanglands

universe u uV uW

open Langlands.Classification

section Statements

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
  [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ)

/-- The Jacquet–Langlands relation is the graph of a bijection between isomorphism classes of
irreducible essentially square-integrable smooth representations of `GL_n(F)` (carriers in
`Type uV`) and isomorphism classes of irreducible admissible smooth representations of `Dˣ`
(carriers in `Type uW`): existence on both sides and uniqueness up to isomorphism on both
sides. -/
def IsJacquetLanglandsBijection : Prop :=
  (∀ A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F), A.representation.IsIrreducible →
      IsEssentiallySquareIntegrable A.representation →
      ∃ B : SmoothRep.{0, u, uW} ℂ Dˣ, IsJacquetLanglandsSmoothPair F D n A B) ∧
    (∀ B : SmoothRep.{0, u, uW} ℂ Dˣ, B.representation.IsIrreducible →
      IsAdmissible B.representation →
      ∃ A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F), IsJacquetLanglandsSmoothPair F D n A B) ∧
    (∀ (A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)) (B₁ B₂ : SmoothRep.{0, u, uW} ℂ Dˣ),
      IsJacquetLanglandsSmoothPair F D n A B₁ → IsJacquetLanglandsSmoothPair F D n A B₂ →
      Nonempty (B₁ ≅ B₂)) ∧
    (∀ (A₁ A₂ : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)) (B : SmoothRep.{0, u, uW} ℂ Dˣ),
      IsJacquetLanglandsSmoothPair F D n A₁ B → IsJacquetLanglandsSmoothPair F D n A₂ B →
      Nonempty (A₁ ≅ A₂))

/-- Compatibility with central characters: related representations have central characters,
and these agree on `Fˣ`, embedded as the scalar matrices in `GL_n(F)` and as the centre of
`Dˣ`. -/
def JacquetLanglandsCentralCharacterCompatibility : Prop :=
  ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear n F) V) (ρ' : Representation ℂ Dˣ W),
    IsJacquetLanglandsPair F D n ρ ρ' →
      ∃ ω : Fˣ →* ℂˣ, HasScalarCharacter ρ GeneralLinear.scalar ω ∧
        HasScalarCharacter ρ' (Units.map (algebraMap F D : F →* D)) ω

/-- Compatibility with twists: for a smooth character `χ` of `Fˣ` (open kernel), twisting by
`χ ∘ det` on `GL_n(F)` and by `χ ∘ Nrd` on `Dˣ` preserves the relation. The reduced norm is the
Library's `BinaryElementary.Reduced.coefficientNorm F D`. -/
def JacquetLanglandsTwistCompatibility : Prop :=
  ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear n F) V) (ρ' : Representation ℂ Dˣ W)
    (χ : Fˣ →* ℂˣ), IsOpen (χ.ker : Set Fˣ) →
    IsJacquetLanglandsPair F D n ρ ρ' →
      IsJacquetLanglandsPair F D n (twist (χ.comp GeneralLinear.determinant) ρ)
        (twist (χ.comp (BinaryElementary.Reduced.coefficientNorm F D)) ρ')

end Statements

/-- The local Jacquet–Langlands correspondence in characteristic zero (Deligne–Kazhdan–Vignéras,
Rogawski): for every nonarchimedean local field `F` of characteristic zero and every central
division algebra `D` of dimension `n^2` over `F`, the relation is a bijection on isomorphism
classes, compatible with central characters and twists. -/
def JacquetLanglandsCharZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
      IsJacquetLanglandsBijection.{u, uV, uW} F D n ∧
        JacquetLanglandsCentralCharacterCompatibility.{u, uV, uW} F D n ∧
        JacquetLanglandsTwistCompatibility.{u, uV, uW} F D n

/-- The local Jacquet–Langlands correspondence in positive characteristic (Badulescu 2002):
the same conclusion for every nonarchimedean local field `F` of characteristic `p > 0`. -/
def JacquetLanglandsPositiveCharStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
    [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
      IsJacquetLanglandsBijection.{u, uV, uW} F D n ∧
        JacquetLanglandsCentralCharacterCompatibility.{u, uV, uW} F D n ∧
        JacquetLanglandsTwistCompatibility.{u, uV, uW} F D n

section Classes

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {D : Type u} [DivisionRing D] [Algebra F D] [FiniteDimensional F D] [Algebra.IsCentral F D]
  [TopologicalSpace D] [IsModuleTopology F D] {n : ℕ}

/-- Under the bijection statement, the class of an irreducible essentially square-integrable
representation of `GL_n(F)` is related to exactly one class of representations of `Dˣ`. -/
theorem IsJacquetLanglandsBijection.existsUnique_right
    (h : IsJacquetLanglandsBijection.{u, uV, uW} F D n)
    (A : SmoothRep.{0, u, uV} ℂ (GeneralLinear n F)) (hA : A.representation.IsIrreducible)
    (hA' : IsEssentiallySquareIntegrable A.representation) :
    ∃! π' : SmoothRep.IsoClass.{0, u, uW} ℂ Dˣ,
      IsJacquetLanglandsClassPair F D n (SmoothRep.isoClass A) π' := by
  obtain ⟨B, hB⟩ := h.1 A hA hA'
  refine ⟨SmoothRep.isoClass B, (isJacquetLanglandsClassPair_isoClass A B).2 hB, ?_⟩
  intro π' hπ'
  induction π' using Quotient.inductionOn with
  | h B₂ =>
    have hB₂ := (isJacquetLanglandsClassPair_isoClass A B₂).1 hπ'
    exact (SmoothRep.isoClass_eq_iff B₂ B).2 ⟨(h.2.2.1 A B B₂ hB hB₂).some.symm⟩

/-- Under the bijection statement, the class of an irreducible admissible representation of
`Dˣ` is related to exactly one class of representations of `GL_n(F)`. -/
theorem IsJacquetLanglandsBijection.existsUnique_left
    (h : IsJacquetLanglandsBijection.{u, uV, uW} F D n)
    (B : SmoothRep.{0, u, uW} ℂ Dˣ) (hB : B.representation.IsIrreducible)
    (hB' : IsAdmissible B.representation) :
    ∃! π : SmoothRep.IsoClass.{0, u, uV} ℂ (GeneralLinear n F),
      IsJacquetLanglandsClassPair F D n π (SmoothRep.isoClass B) := by
  obtain ⟨A, hA⟩ := h.2.1 B hB hB'
  refine ⟨SmoothRep.isoClass A, (isJacquetLanglandsClassPair_isoClass A B).2 hA, ?_⟩
  intro π hπ
  induction π using Quotient.inductionOn with
  | h A₂ =>
    have hA₂ := (isJacquetLanglandsClassPair_isoClass A₂ B).1 hπ
    exact (SmoothRep.isoClass_eq_iff A₂ A).2 ⟨(h.2.2.2 A A₂ B hA hA₂).some.symm⟩

end Classes

end Langlands.JacquetLanglands
