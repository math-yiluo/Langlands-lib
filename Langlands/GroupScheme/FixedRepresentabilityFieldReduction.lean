import Langlands.GroupScheme.FixedRepresentabilityStatement
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Field reductions for closed fixed-subgroup representability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- The identity extension of the field supplies the faithfully flat extension
and projective coordinate module required by the general fixed-locus target. -/
def fieldCoordinateProjectiveWitness (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) :
    {B : CommAlgCat.{u} (CommRingCat.of k) //
      Module.FaithfullyFlat (CommRingCat.of k) B ∧
        Module.Projective B
          (B ⊗[CommRingCat.of k] ((algΓ (CommRingCat.of k)).obj H.X).unop)} :=
  ⟨CommAlgCat.of (CommRingCat.of k) k, inferInstance, inferInstance⟩

/-- The coordinate-projectivity condition imposes no restriction over a field. -/
theorem hasFpqcProjectiveCoordinateModule_field (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) :
    HasFpqcProjectiveCoordinateModule H :=
  ⟨(fieldCoordinateProjectiveWitness k H).val,
    (fieldCoordinateProjectiveWitness k H).property⟩

/-- Every group scheme over a field has flat structure morphism. -/
theorem flat_field (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) : Flat H.X.hom :=
  inferInstance

/-- The general representability target implies the field target with its exact
scope, using flatness, projectivity of vector spaces, and field separatedness. -/
theorem fieldFixedSubgroupRepresentability_of_general
    (h : FixedSubgroupRepresentabilityStatement.{u}) :
    FieldFixedSubgroupRepresentabilityStatement.{u} := by
  intro k _ H G hH a
  exact h (CommRingCat.of k) H G hH (flat_field k H)
    (hasFpqcProjectiveCoordinateModule_field k H) (fieldSeparated k G) a

/-- The field centralizer target follows by applying the field fixed-subgroup
target to the actual conjugation action. -/
theorem fieldCentralizerRepresentability_of_fixed
    (h : FieldFixedSubgroupRepresentabilityStatement.{u}) :
    FieldCentralizerRepresentabilityStatement.{u} := by
  intro k _ H G hH j
  have hj := h k H.toGrp G hH (AutomorphicAction.conjugation j)
  rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer] at hj

end Langlands.GroupScheme
