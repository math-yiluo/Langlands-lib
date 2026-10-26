import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement

/-! The full determinant modulus under ordered refinement coordinates. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF

/-- The full-modulus conjunct of the ordered refinement normalization statement,
closed over exactly its field, block and coordinate hypotheses. -/
def RefinementCoordinatesModulusTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B D : BlockShape n) (S : BlockRefinement D)
    (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ i k x, D.index i ((S i).index k x) =
      B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x)),
    RefinementCoordinatesNormalization.ModulusClause F T B D S e hs

end Langlands.Parabolic
