import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Filtration.Definitions
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# The actual derivative Leibniz filtration in all ranks

The natural finite-filtration assertion of Bernstein–Zelevinsky 1977, 4.14(c),
with a concrete feasible index set and the published rank-zero tensor extension.
The assertion is a proposition definition; this module does not prove it.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

universe uF uV

/-- Exactly the derivative-order pairs that are within both source ranks. -/
def leibnizIndices (a b d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal d).filter (fun x => x.1 ≤ a ∧ x.2 ≤ b)

@[simp]
theorem mem_leibnizIndices {a b d : ℕ} {x : ℕ × ℕ} :
    x ∈ leibnizIndices a b d ↔ x.1 ≤ a ∧ x.2 ≤ b ∧ x.1 + x.2 = d := by
  simp only [leibnizIndices, Finset.mem_filter, Finset.mem_antidiagonal]
  tauto

theorem leibnizIndices_left_le {a b d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ leibnizIndices a b d) : x.1 ≤ a :=
  (mem_leibnizIndices.mp hx).1

theorem leibnizIndices_right_le {a b d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ leibnizIndices a b d) : x.2 ≤ b :=
  (mem_leibnizIndices.mp hx).2.1

theorem leibnizIndices_sum {a b d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ leibnizIndices a b d) : x.1 + x.2 = d :=
  (mem_leibnizIndices.mp hx).2.2

theorem leibnizIndices_rank {a b d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ leibnizIndices a b d) :
    (a - x.1) + (b - x.2) = (a + b) - d := by
  have := leibnizIndices_left_le hx
  have := leibnizIndices_right_le hx
  have := leibnizIndices_sum hx
  omega

/-- The finite subtype retains different indices even when their pieces coincide. -/
abbrev LeibnizIndex (a b d : ℕ) := {x : ℕ × ℕ // x ∈ leibnizIndices a b d}

@[simp]
theorem leibnizIndices_zero (a b : ℕ) : leibnizIndices a b 0 = {(0, 0)} := by
  ext x
  simp only [mem_leibnizIndices, Finset.mem_singleton]
  rcases x with ⟨i, j⟩
  simp only [Prod.mk.injEq]
  omega

@[simp]
theorem leibnizIndices_top (a b : ℕ) : leibnizIndices a b (a + b) = {(a, b)} := by
  ext x
  simp only [mem_leibnizIndices, Finset.mem_singleton]
  rcases x with ⟨i, j⟩
  simp only [Prod.mk.injEq]
  omega

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The literal derivative of the actual binary normalized product, viewed in `Rep`. -/
def leibnizSource (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) := by
  letI := T.topology
  exact T.binaryNormalizedProductFunctor a b ⋙
    generalLinearDerivative T ψ (a + b) d hd ⋙ SmoothRep.toRep

theorem leibnizSource_obj (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      (leibnizSource T ψ a b d hd).obj (A, B) =
        SmoothRep.toRep.obj
          ((generalLinearDerivative T ψ (a + b) d hd).obj
            ((T.binaryNormalizedProductFunctor a b).obj (A, B))) := by
  intros
  rfl

/-- A feasible grade: derivative of each factor, binary product, smooth rank cast,
then the forgetful functor to `Rep`. -/
def leibnizPiece (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) := by
  letI := T.topology
  exact (generalLinearDerivative T ψ a x.val.1 (leibnizIndices_left_le x.property)).prod
      (generalLinearDerivative T ψ b x.val.2 (leibnizIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor (a - x.val.1) (b - x.val.2) ⋙
    generalLinearRankCast T (leibnizIndices_rank x.property) ⋙ SmoothRep.toRep

theorem leibnizPiece_obj (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (x : LeibnizIndex a b d) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      (leibnizPiece T ψ a b d x).obj (A, B) =
        SmoothRep.toRep.obj
          ((generalLinearRankCast T (leibnizIndices_rank x.property)).obj
            ((T.binaryNormalizedProductFunctor (a - x.val.1) (b - x.val.2)).obj
              ((generalLinearDerivative T ψ a x.val.1
                  (leibnizIndices_left_le x.property)).obj A,
                (generalLinearDerivative T ψ b x.val.2
                  (leibnizIndices_right_le x.property)).obj B))) := by
  intros
  rfl

variable (F) in
/-- BZ77 4.14(c) as an actual natural filtration, with every feasible index exactly
once and arbitrary ordering, including all rank-zero and top-order boundaries. -/
def GeneralLinearDerivativeLeibnizFiltrationStatement (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b),
    ∃ e : LeibnizIndex a b d ≃ Fin (leibnizIndices a b d).card,
      IsGluedFrom (leibnizSource.{uF, uV} T ψ a b d hd)
        (fun i => leibnizPiece T ψ a b d (e.symm i))

/-- Extract a genuine filtration; absorb the gluing permutation into its enumeration.
This is a consequence of a supplied Leibniz assertion, not a proof of that assertion. -/
theorem GeneralLinearDerivativeLeibnizFiltrationStatement.filtration
    (T : F.TopologicalData)
    (h : GeneralLinearDerivativeLeibnizFiltrationStatement.{uF, uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    ∃ e : LeibnizIndex a b d ≃ Fin (leibnizIndices a b d).card,
      ∃ s : RepFunctorFiltration (leibnizSource.{uF, uV} T ψ a b d hd)
          (leibnizIndices a b d).card,
        ∀ i, Nonempty (s.graded i ≅ leibnizPiece T ψ a b d (e.symm i)) := by
  let _ := T.topology
  obtain ⟨e, σ, s, hs⟩ := h ψ a b d hd
  exact ⟨e.trans σ.symm, s, hs⟩

end Langlands.Derivative
