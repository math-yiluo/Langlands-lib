import Langlands.Representation.MatrixCoefficient.CentralL2
import Langlands.Representation.Unitary.Completion
import Mathlib.RepresentationTheory.Irreducible

/-!
# A closed coefficient component in the actual central L2 completion

This internal proposition states an application of coefficient restriction,
form pullback, completion and admissible smooth-vector recovery. It supplies
neither a completed embedding nor an irreducibility proof.
-/

namespace Langlands

universe uG uV

/-- An irreducible square-integrable unitarizable representation occurs as a
closed irreducible coefficient component in the actual central L2 completion,
with its original algebraic carrier recovered as the smooth vectors. -/
def SquareIntegrableCoefficientHilbertComponentStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ G V)
      [MeasurableSpace (G ⧸ Subgroup.center G)]
      [BorelSpace (G ⧸ Subgroup.center G)]
      (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
      [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
      Representation.IsIrreducible ρ →
      ∀ hsq : IsSquareIntegrableModCenter ρ μ,
        IsUnitarizable ρ →
        ∃ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ),
          ℓ.val ≠ 0 ∧
          let σ := Induction.centralL2Representation c.character c.norm_eq_one μ
          let B := Induction.centralL2Form c.character c.norm_eq_one μ
          ∃ (j : ρ.IntertwiningMap σ) (b : InvariantPositiveForm ρ)
            (e : b.HilbertCompletion →ₗᵢ[ℂ] B.HilbertCompletion)
            (R : Subrepresentation B.completedRepresentation),
            (∀ v, (j v).1 = c.coefficientIntertwiner hsq.1.1 ℓ.val v) ∧
            (∀ v w, b.inner v w = B.inner (j v) (j w)) ∧
            (∀ v, e (b.toHilbert v) = B.toHilbert (j v)) ∧
            (∀ g x, e (b.completedRepresentation g x) =
              B.completedRepresentation g (e x)) ∧
            Set.range e = (R : Set B.HilbertCompletion) ∧
            IsClosed (R : Set B.HilbertCompletion) ∧
            (∀ y : B.HilbertCompletion,
              Continuous (fun g : G => B.completedRepresentation g y)) ∧
            (Nontrivial R.toSubmodule ∧
              ∀ S : Subrepresentation R.toRepresentation,
                IsClosed (S : Set R.toSubmodule) → S = ⊥ ∨ S = ⊤) ∧
            (∀ y : B.HilbertCompletion,
              (y ∈ R ∧ y ∈ smoothVectors B.completedRepresentation) ↔
                ∃ v : V, e (b.toHilbert v) = y)

end Langlands
