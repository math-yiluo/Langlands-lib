import Langlands.AbelianScheme.FieldEqualDimensionClosedImmersionStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.Picard.SectionCutDimensionProof

/-! # A full-dimensional closed abelian subscheme fills its target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AbelianScheme

private lemma stalkKrullDim_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  simpa only [topologicalKrullDim, coheight_orderIso] using
    (coheight_le_krullDim ((irreducibleSetEquivPoints (α := X)).symm x))

/-- A full-dimensional closed immersion between actual abelian schemes over
a field is an isomorphism of underlying schemes. -/
theorem fieldEqualDimensionClosedImmersion :
    FieldEqualDimensionClosedImmersionStatement.{u} := by
  intro K _ A B g hA hB f hi
  have : IsClosedImmersion (hom f) := hi
  have : GeometricallyIntegral B.X.hom :=
    smoothGeometricIntegrality K B.X.left B.X.hom inferInstance inferInstance
  have : IsIntegral B.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  have : CompactSpace A.X.left :=
    QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : CompactSpace B.X.left :=
    QuasiCompact.compactSpace_of_compactSpace B.X.hom
  obtain ⟨x, _, hx⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set A.X.left)).exists_closed_singleton
      Set.univ_nonempty
  have hdimA : (g : WithBot ℕ∞) ≤ topologicalKrullDim A.X.left := by
    rw [← Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension
      K A.X.left A.X.hom g hA x hx]
    exact stalkKrullDim_le_topologicalKrullDim A.X.left x
  have hdimB : topologicalKrullDim B.X.left ≤ (g : WithBot ℕ∞) :=
    Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim
      K B.X.left B.X.hom g hB inferInstance
  have hdimImage : topologicalKrullDim A.X.left ≤
      topologicalKrullDim (Set.range (hom f)) :=
    ((hom f).isClosedEmbedding.isInducing.codRestrict
      (fun x => (show hom f x ∈ Set.range (hom f) from ⟨x, rfl⟩))).topologicalKrullDim_le
  have hrange : Set.range (hom f) = Set.univ := by
    by_contra hne
    have hdrop := Langlands.AlgebraicGeometry.Picard.topologicalKrullDim_add_one_le_of_isClosed
      (Set.range (hom f)) (hom f).isClosedEmbedding.isClosed_range hne
    have hlt : topologicalKrullDim (Set.range (hom f)) < (g : WithBot ℕ∞) :=
      ENat.WithBot.add_one_le_natCast_iff.mp (hdrop.trans hdimB)
    exact (not_lt_of_ge (hdimA.trans hdimImage)) hlt
  have : Surjective (hom f) := ⟨Set.range_eq_univ.mp hrange⟩
  exact isIso_of_isClosedImmersion_of_surjective (hom f)

end Langlands.AbelianScheme
