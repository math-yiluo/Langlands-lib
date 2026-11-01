import Langlands.Geometry.Analytic.Affinoid

/-! # Isometric amalgamation of complete ultrametric fields -/

universe u

namespace Langlands.Analytic

/-- Two complete ultrametric normed extensions of a common complete field,
with compatible coefficient structures, admit commuting isometric embeddings
into one complete ultrametric normed field in the same universe. -/
def CompleteFieldAmalgamationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (E F G : Type u)
    [NormedField E] [IsUltrametricDist E] [CompleteSpace E] [NormedAlgebra K E]
    [NormedField F] [IsUltrametricDist F] [CompleteSpace F] [NormedAlgebra K F]
    [NormedField G] [IsUltrametricDist G] [CompleteSpace G] [NormedAlgebra K G]
    (i : BoundedAlgHom K E F) (j : BoundedAlgHom K E G),
    Isometry i → Isometry j →
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (_ : NormedAlgebra K L)
      (f : BoundedAlgHom K F L) (g : BoundedAlgHom K G L),
      f.comp i = g.comp j ∧ Isometry f ∧ Isometry g

end Langlands.Analytic
