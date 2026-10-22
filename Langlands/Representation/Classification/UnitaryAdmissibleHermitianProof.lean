import Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Unitary.HermitianDual

/-!
# Proof of the admissible Hermitian identification clause

For an admissible smooth representation of `GL_n(F)` with an invariant positive
form `b`, the map `v ↦ b(v, -)` is the required conjugate-linear equivalence
onto the actual smooth dual.
-/

namespace Langlands.Classification

universe uF uV

/-- Every invariant positive form on an admissible smooth representation of
`GL_n(F)` identifies it, conjugate-linearly and equivariantly, with its smooth
dual through `v ↦ b(v, -)`. -/
theorem unitaryAdmissibleHermitianClause {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    UnitaryAdmissibleHermitianClause.{uF, uV} F T := by
  intro n _
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro δ hδ b
  exact ⟨b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T n) hδ,
    fun g v => b.toSmoothDual_apply_action hδ.1 g v, fun _ _ => rfl⟩

end Langlands.Classification
