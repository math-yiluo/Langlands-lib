import Langlands.Representation.Exponents.WeylBranchMultiplicityExtraction
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.MultiplicityIndependenceProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-!
# Strict multiplicity excess lies in another graded piece

If an actual composition series of a finitely filtered representation counts
more factors equivalent to `τ` than one distinguished graded quotient does,
then `τ` is an actual subquotient of a different graded quotient. The
multiplicities are actual Jordan–Hölder multiplicities.
-/

noncomputable section

namespace Langlands.WeylBranchPieces

open CategoryTheory

universe uG uV uW uX uC vC

variable {G : Type uG} [Group G]

/-- Every graded quotient of an actual object filtration is an actual
subquotient of the filtered representation. -/
theorem isSubquotient_gradedRepresentation {A : Rep.{uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A n) (j : Fin n) :
    IsSubquotient A.ρ (s.gradedRepresentation j).ρ :=
  isSubquotient_graded s (Discrete.mk PUnit.unit) j

/-- A representation counted a positive number of times among the graded
quotients of an actual object filtration is an actual subquotient. -/
theorem isSubquotient_of_factorMultiplicity_pos {A : Rep.{uV} ℂ G}
    {τ : Rep.{uW} ℂ G} {n : ℕ} (s : ObjectRepFiltration A n)
    (h : 0 < s.factorMultiplicity τ) : IsSubquotient A.ρ τ.ρ := by
  unfold ObjectRepFiltration.factorMultiplicity at h
  obtain ⟨⟨j, ⟨φ⟩⟩⟩ := (Nat.card_pos_iff.mp h).1
  exact (isSubquotient_gradedRepresentation s j).of_equiv_right φ

/-- Strict excess of the ambient multiplicity over that of one graded
quotient: if `A` has Jordan–Hölder multiplicity `M` of `τ`, and the `j₀`th
graded quotient of a finite filtration of `A` is equivalent to a
representation `X` of multiplicity `m₀ < M`, then `τ` is an actual
subquotient of some other graded quotient. -/
theorem exists_ne_isSubquotient_gradedRepresentation_of_lt
    {A : Rep.{uV} ℂ G} {τ : Rep.{uW} ℂ G} {M : ℕ}
    (hM : HasJordanHolderMultiplicity A τ M) {n : ℕ}
    (s : ObjectRepFiltration A n) (j₀ : Fin n) {X : Rep.{uX} ℂ G}
    (φ : (s.gradedRepresentation j₀).ρ.Equiv X.ρ) {m₀ : ℕ}
    (h₀ : HasJordanHolderMultiplicity X τ m₀) (hlt : m₀ < M) :
    ∃ j : Fin n, j ≠ j₀ ∧ IsSubquotient (s.gradedRepresentation j).ρ τ.ρ :=
  exists_isSubquotient_graded_of_multiplicity_excess s j₀ φ h₀ hM hlt

variable {C : Type uC} [Category.{vC} C]

/-- The objectwise filtration underlying a natural finite filtration. -/
def objectFiltration {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    (s : RepFunctorFiltration F n) (Y : C) : ObjectRepFiltration (F.obj Y) n :=
  ObjectRepFiltration.ofSubrepresentations (fun k => (s.step k).obj Y)
    (s.monotone Y) (s.zero Y) (s.top Y)

/-- Strict excess for a representation glued from finitely many pieces: if
`τ` has multiplicity `M` in `F.obj Y`, and piece `i₀` at `Y` has multiplicity
`m₀ < M`, then `τ` is an actual subquotient of another piece at `Y`. -/
theorem IsGluedFrom.exists_ne_isSubquotient_piece_of_lt
    {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ} {pieces : Fin n → C ⥤ Rep.{uV} ℂ G}
    (h : IsGluedFrom F pieces) (Y : C) {τ : Rep.{uW} ℂ G} {M : ℕ}
    (hM : HasJordanHolderMultiplicity (F.obj Y) τ M) (i₀ : Fin n) {m₀ : ℕ}
    (h₀ : HasJordanHolderMultiplicity ((pieces i₀).obj Y) τ m₀) (hlt : m₀ < M) :
    ∃ i : Fin n, i ≠ i₀ ∧ IsSubquotient ((pieces i).obj Y).ρ τ.ρ :=
  Langlands.WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess
    h Y i₀ h₀ hM hlt

end Langlands.WeylBranchPieces
