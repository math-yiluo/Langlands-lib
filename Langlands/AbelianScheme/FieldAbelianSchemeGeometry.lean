import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof

/-! # Basic geometry of an abelian scheme over a field -/

universe u

open CategoryTheory AlgebraicGeometry Order

namespace Langlands.AbelianScheme

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- An abelian scheme over a field is integral. -/
theorem field_isIntegral : IsIntegral A.X.left :=
  have : GeometricallyIntegral A.X.hom :=
    smoothGeometricIntegrality K A.X.left A.X.hom inferInstance inferInstance
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

/-- An abelian scheme over a field is Noetherian. -/
theorem field_isNoetherian : IsNoetherian A.X.left :=
  have : IsLocallyNoetherian A.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : CompactSpace A.X.left :=
    (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance
  ⟨⟩

/-- An abelian scheme over a field is separated. -/
theorem field_isSeparated : A.X.left.IsSeparated :=
  ⟨by
    rw [← Limits.terminal.comp_from A.X.hom]
    infer_instance⟩

variable {A}

/-- At a closed point of an abelian scheme of relative dimension `g` over a field,
the stalk has Krull dimension `g`. -/
theorem field_closedPoint_stalk_dimension {g : ℕ} (hg : A.HasRelativeDimension g)
    (x : A.X.left) (hx : IsClosed ({x} : Set A.X.left)) :
    ringKrullDim (A.X.left.presheaf.stalk x) = (g : WithBot ℕ∞) :=
  Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension K A.X.left A.X.hom g hg
    x hx

/-- An abelian scheme of relative dimension `g` over a field has topological Krull
dimension `g`. -/
theorem field_topologicalKrullDim {g : ℕ} (hg : A.HasRelativeDimension g) :
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) := by
  have : IsIntegral A.X.left := field_isIntegral A
  have hcompact : CompactSpace A.X.left :=
    (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance
  apply le_antisymm
  · exact Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K A.X.left A.X.hom g hg
      hcompact
  · obtain ⟨x, _, hx⟩ :=
      (isClosed_univ : IsClosed (Set.univ : Set A.X.left)).exists_closed_singleton
        Set.univ_nonempty
    rw [← field_closedPoint_stalk_dimension hg x hx, ringKrullDim_stalk_eq_coheight,
      topologicalKrullDim, ← coheight_orderIso (irreducibleSetEquivPoints (α := A.X.left)).symm x]
    exact coheight_le_krullDim _

end Langlands.AbelianScheme
