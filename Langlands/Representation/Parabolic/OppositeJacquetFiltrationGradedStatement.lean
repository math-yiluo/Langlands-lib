import Langlands.Representation.Parabolic.OppositeJacquetFiltration

/-! Same-index graded comparisons for the fixed normalized opposite Jacquet
image filtrations. These proposition definitions do not supply proofs. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Each actual graded quotient of the refined opposite image filtration is
equivalent to the normalized refined opposite quotient of the original grade. -/
def NormalizedRefinedOppositeJacquetFiltrationGradedClause : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V),
    IsSmooth ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration (Rep.of ρ) l) (i : Fin l),
        Nonempty
          (((T.normalizedRefinedOppositeJacquetFiltration B S ρ s).gradedRepresentation i).ρ.Equiv
            (T.normalizedRefinedOppositeJacquet B S (s.gradedRepresentation i).ρ))

/-- The analogous comparison for the actual composed opposite quotient of an
ambient general-linear representation, retaining the full normalization. -/
def NormalizedComposedOppositeJacquetFiltrationGradedClause : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    IsSmooth ρ →
      ∀ (l : ℕ) (s : ObjectRepFiltration (Rep.of ρ) l) (i : Fin l),
        Nonempty
          (((T.normalizedComposedOppositeJacquetFiltration B S ρ s).gradedRepresentation i).ρ.Equiv
            (T.normalizedComposedOppositeJacquet B S (s.gradedRepresentation i).ρ))

/-- Both same-index comparisons for every p-adic field, block shape and
refinement, with independent field and representation-carrier universes. -/
def NormalizedOppositeJacquetFiltrationGradedStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    NormalizedRefinedOppositeJacquetFiltrationGradedClause.{uF, uV} F T B S ∧
    NormalizedComposedOppositeJacquetFiltrationGradedClause.{uF, uV} F T B S

end Langlands.Parabolic
