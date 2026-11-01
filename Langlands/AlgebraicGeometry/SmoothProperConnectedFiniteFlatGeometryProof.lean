import Langlands.AlgebraicGeometry.SmoothProperConnectedFiniteFlatGeometryStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.FiniteIrreducibleEndomorphismSurjectiveProof

/-! # Integral geometry and constant positive native rank -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry

/-- The geometric and native-rank preparation holds over any field. -/
theorem smoothProperConnectedFiniteFlatGeometry :
    SmoothProperConnectedFiniteFlatGeometryStatement.{u} := by
  intro K _ X g hs hp hc f hf hflat
  let : SmoothOfRelativeDimension g X.hom := hs
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : IsProper X.hom := hp
  let : GeometricallyConnected X.hom := hc
  let : IsFinite f.left := hf
  let : Flat f.left := hflat
  have hgi : GeometricallyIntegral X.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K X.left X.hom
      inferInstance hc
  let : GeometricallyIntegral X.hom := hgi
  have hi : IsIntegral X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  let : IsIntegral X.left := hi
  have hn : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian X.left := hn
  have hcompact : CompactSpace X.left :=
    (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  let : CompactSpace X.left := hcompact
  let : IsNoetherian X.left := ⟨⟩
  have hdim : topologicalKrullDim X.left = (g : WithBot ℕ∞) := by
    apply le_antisymm
    · exact fieldSmoothTopologicalKrullDim K X.left X.hom g hs hcompact
    · obtain ⟨x, _, hx⟩ :=
        (isClosed_univ : IsClosed (Set.univ : Set X.left)).exists_closed_singleton
          Set.univ_nonempty
      rw [← fieldSmoothClosedPointStalkDimension K X.left X.hom g hs x hx,
        ringKrullDim_stalk_eq_coheight]
      rw [topologicalKrullDim]
      rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X.left)).symm x]
      exact coheight_le_krullDim _
  have hsurj : Surjective f.left :=
    finiteIrreducibleEndomorphismSurjective X.left f.left hf
  let : Surjective f.left := hsurj
  refine ⟨hi, hdim, hsurj, ?_, ?_⟩
  · exact f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace
  · intro x
    exact Nat.lt_of_succ_le ((f.left.one_le_finrank_iff_surjective.mpr hsurj) x)

end Langlands.AlgebraicGeometry
