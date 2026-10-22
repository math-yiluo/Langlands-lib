import Langlands.Representation.Classification.LanglandsData

/-!
# The regular-chamber Langlands quotient statements for GL_n

These proposition definitions specialize Silberger's quotient theorem to
ordered tempered GL blocks with strictly decreasing real determinant exponents.
All induction, quotient maps and block isomorphisms are actual constructions.
-/

namespace Langlands

open CategoryTheory

universe uF uV

/-- Every regular-positive tempered standard module has an irreducible head,
with uniqueness of the kernel of every irreducible quotient map. -/
def GLRegularLanglandsHeadExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ d : T.TemperedLanglandsDatum.{max uF uV, uF} n,
        ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
          d.IsLanglandsHead π

/-- Isomorphic irreducible quotients of regular-positive tempered standard
modules recover the ordered ranks, real exponents and tempered block classes. -/
def GLRegularLanglandsDataUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (d e : T.TemperedLanglandsDatum.{max uF uV, uF} n)
        (π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
        d.IsLanglandsQuotient π → e.IsLanglandsQuotient τ →
        Nonempty (π ≅ τ) →
          ∃ (a : Fin d.shape.length ≃o Fin e.shape.length)
            (h : ∀ i, d.shape.size i = e.shape.size (a i)),
            ∀ i, d.exponent i = e.exponent (a i) ∧
              Nonempty ((h i ▸ d.blocks i) ≅ e.blocks (a i))

/-- Every irreducible admissible representation of positive-rank GL_n is
the irreducible head of a regular-positive tempered standard module. -/
def GLRegularLanglandsExhaustionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        Representation.IsIrreducible π.representation →
        IsAdmissible π.representation →
          ∃ d : T.TemperedLanglandsDatum.{max uF uV, uF} n,
            d.IsLanglandsHead π

/-- The three clauses of the regular-chamber Langlands quotient theorem in
actual ordered tempered-block form. They are statements, not proofs. -/
def GLRegularLanglandsQuotientStatement : Prop :=
  GLRegularLanglandsHeadExistenceStatement.{uF, uV} ∧
  GLRegularLanglandsDataUniquenessStatement.{uF, uV} ∧
  GLRegularLanglandsExhaustionStatement.{uF, uV}

end Langlands
