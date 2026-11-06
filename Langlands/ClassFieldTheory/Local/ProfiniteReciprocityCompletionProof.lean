import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityNormBridges
import Langlands.ClassFieldTheory.Local.CompletionComparison
import Langlands.ClassFieldTheory.Local.NormExistenceProof
import Langlands.ClassFieldTheory.Local.NormSubgroupsSeparatePointsProof

/-!
# The profinite reciprocity completion

Arithmetic norm existence and norm separation discharge the structural
descent and injectivity criteria for the original multiplicative completion.
-/

namespace Langlands.LocalClassField

universe u

/-- Every reciprocity candidate satisfying the published geometric relation
is injective and gives the unique actual multiplicative completion comparison. -/
theorem profiniteReciprocityCompletion : ProfiniteReciprocityCompletion.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : CompactSpace (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
    inferInstanceAs (CompactSpace (localAbelianGaloisGroup F))
  let : T2Space (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
    inferInstanceAs (T2Space (localAbelianGaloisGroup F))
  let : TotallyDisconnectedSpace
      (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (localAbelianGaloisGroup F))
  intro r hr
  refine ⟨injective_of_normSubgroupsSeparatePoints F T
    normSubgroupsSeparatePoints r hr.1, ?_⟩
  exact ContinuousProfinite.existsUnique_equiv_of_finite_quotient_descent r hr.1.1
    (finiteQuotientDescent_of_normSubgroupExistence F T
      Langlands.ClassFieldTheory.Local.normSubgroupExistence r hr.1)

end Langlands.LocalClassField
