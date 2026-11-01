import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Filtration.Definitions
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# The actual right mixed-product derivative filtration

BZ77 4.14(b), with a concrete family of feasible orders, actual natural
successive quotients, and the arbitrary-carrier rank-zero tensor extension.
The main assertion is a proposition definition and is not proved here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

/-- Precisely the within-rank derivative pairs for a right mixed product. -/
def rightMixedDerivativeIndices (k r d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal d).filter (fun x => 1 ≤ x.1 ∧ x.1 ≤ r + 1 ∧ x.2 ≤ k)

@[simp]
theorem mem_rightMixedDerivativeIndices {k r d : ℕ} {x : ℕ × ℕ} :
    x ∈ rightMixedDerivativeIndices k r d ↔
      1 ≤ x.1 ∧ x.1 ≤ r + 1 ∧ x.2 ≤ k ∧ x.1 + x.2 = d := by
  simp only [rightMixedDerivativeIndices, Finset.mem_filter, Finset.mem_antidiagonal]
  tauto

theorem rightMixedDerivativeIndices_left_pos {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) : 0 < x.1 :=
  (mem_rightMixedDerivativeIndices.mp hx).1

theorem rightMixedDerivativeIndices_left_le {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) : x.1 ≤ r + 1 :=
  (mem_rightMixedDerivativeIndices.mp hx).2.1

theorem rightMixedDerivativeIndices_left_bound {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) : 0 < x.1 ∧ x.1 ≤ r + 1 :=
  ⟨rightMixedDerivativeIndices_left_pos hx, rightMixedDerivativeIndices_left_le hx⟩

theorem rightMixedDerivativeIndices_right_le {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) : x.2 ≤ k :=
  (mem_rightMixedDerivativeIndices.mp hx).2.2.1

theorem rightMixedDerivativeIndices_sum {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) : x.1 + x.2 = d :=
  (mem_rightMixedDerivativeIndices.mp hx).2.2.2

theorem rightMixedDerivativeIndices_rank {k r d : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rightMixedDerivativeIndices k r d) :
    (r + 1 - x.1) + (k - x.2) = (k + r) + 1 - d := by
  have := rightMixedDerivativeIndices_left_le hx
  have := rightMixedDerivativeIndices_right_le hx
  have := rightMixedDerivativeIndices_sum hx
  omega

/-- The finite subtype keeps different orders even for zero or isomorphic grades. -/
abbrev RightMixedDerivativeIndex (k r d : ℕ) :=
  {x : ℕ × ℕ // x ∈ rightMixedDerivativeIndices k r d}

/-- With a `GL₀` factor the entire derivative falls on the mirabolic factor. -/
theorem rightMixedDerivativeIndices_zero_gl (r d : ℕ) (hd : 0 < d ∧ d ≤ r + 1) :
    rightMixedDerivativeIndices 0 r d = {(d, 0)} := by
  ext x
  simp only [mem_rightMixedDerivativeIndices, Finset.mem_singleton]
  rcases x with ⟨j, t⟩
  simp only [Prod.mk.injEq]
  omega

/-- For `P₁` the only mirabolic derivative order is one. -/
theorem rightMixedDerivativeIndices_zero_mirabolic (k d : ℕ)
    (hd : 0 < d ∧ d ≤ k + 1) :
    rightMixedDerivativeIndices k 0 d = {(1, d - 1)} := by
  ext x
  simp only [mem_rightMixedDerivativeIndices, Finset.mem_singleton]
  rcases x with ⟨j, t⟩
  simp only [Prod.mk.injEq]
  omega

/-- The top order has the pair of top derivatives, with both carriers retained. -/
@[simp]
theorem rightMixedDerivativeIndices_top (k r : ℕ) :
    rightMixedDerivativeIndices k r ((k + r) + 1) = {(r + 1, k)} := by
  ext x
  simp only [mem_rightMixedDerivativeIndices, Finset.mem_singleton]
  rcases x with ⟨j, t⟩
  simp only [Prod.mk.injEq]
  omega

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The literal derivative of the published right mixed product, viewed in `Rep`. -/
def rightMixedDerivativeSource (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((k + r) + 1 - d) F.Carrier) := by
  letI := T.topology
  exact T.rightMixedProductFunctor k r ⋙
    mirabolicDerivativeOfOrder T ψ (k + r) d hd ⋙ SmoothRep.toRep

theorem rightMixedDerivativeSource_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1) :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)),
      (rightMixedDerivativeSource T ψ k r d hd).obj (B, A) =
        SmoothRep.toRep.obj
          ((mirabolicDerivativeOfOrder T ψ (k + r) d hd).obj
            ((T.rightMixedProductFunctor k r).obj (B, A))) := by
  intros
  rfl

/-- A feasible grade in the order `B^(j) × A^(t)`, with smooth rank transport. -/
def rightMixedDerivativePiece (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (x : RightMixedDerivativeIndex k r d) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ⥤
      Rep.{max uF uV} ℂ (GeneralLinear ((k + r) + 1 - d) F.Carrier) := by
  letI := T.topology
  exact (mirabolicDerivativeOfOrder T ψ r x.val.1
        (rightMixedDerivativeIndices_left_bound x.property)).prod
      (generalLinearDerivative T ψ k x.val.2
        (rightMixedDerivativeIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor (r + 1 - x.val.1) (k - x.val.2) ⋙
    generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property) ⋙ SmoothRep.toRep

theorem rightMixedDerivativePiece_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (x : RightMixedDerivativeIndex k r d) :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)),
      (rightMixedDerivativePiece T ψ k r d x).obj (B, A) =
        SmoothRep.toRep.obj
          ((generalLinearRankCast T (rightMixedDerivativeIndices_rank x.property)).obj
            ((T.binaryNormalizedProductFunctor (r + 1 - x.val.1) (k - x.val.2)).obj
              ((mirabolicDerivativeOfOrder T ψ r x.val.1
                  (rightMixedDerivativeIndices_left_bound x.property)).obj B,
                (generalLinearDerivative T ψ k x.val.2
                  (rightMixedDerivativeIndices_right_le x.property)).obj A))) := by
  intros
  rfl

variable (F) in
/-- BZ77 4.14(b) with an actual finite natural filtration and every feasible
order pair exactly once, including all rank-zero and top-order boundaries. -/
def RightMixedProductDerivativeFiltrationStatement (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1),
    ∃ e : Fin (rightMixedDerivativeIndices k r d).card ≃ RightMixedDerivativeIndex k r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ k r d hd)
        (fun i => rightMixedDerivativePiece T ψ k r d (e i))

set_option maxHeartbeats 1000000 in
/-- Extract the actual filtration, its complete grade enumeration, and natural
graded isomorphisms from a supplied assertion. This does not prove the assertion. -/
theorem RightMixedProductDerivativeFiltrationStatement.filtration
    (T : F.TopologicalData)
    (h : RightMixedProductDerivativeFiltrationStatement.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + r) + 1) :
    letI := T.topology
    ∃ s : RepFunctorFiltration (rightMixedDerivativeSource.{uF, uV} T ψ k r d hd)
        (rightMixedDerivativeIndices k r d).card,
      ∃ e : Fin (rightMixedDerivativeIndices k r d).card ≃ RightMixedDerivativeIndex k r d,
        ∀ i, Nonempty (s.graded i ≅ rightMixedDerivativePiece T ψ k r d (e i)) := by
  let _ := T.topology
  obtain ⟨e, σ, s, hs⟩ := h ψ k r d hd
  exact ⟨s, σ.trans e, hs⟩

end Langlands.Derivative
