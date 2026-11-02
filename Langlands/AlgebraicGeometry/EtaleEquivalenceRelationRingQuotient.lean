import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine quotients from faithfully flat pushouts of coordinate rings

The ring certificate used at the end of the Serre criterion proof consists of a ring,
a faithfully flat map to the coordinate ring of the object scheme, and a pushout square
with the two coordinate maps of the relation. Étaleness of the resulting quotient map
follows by fpqc descent from the first projection of the relation.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- Coordinate-ring data for an affine quotient of an affine étale equivalence relation.
The two maps from the coordinate ring of `E.U` to that of `E.R` form the pushout of the
faithfully flat map `inclusion` with itself. -/
structure FaithfullyFlatRingQuotient (E : EtaleEquivalenceRelation.{u}) where
  baseRing : CommRingCat.{u}
  inclusion : baseRing ⟶ Γ(E.U, ⊤)
  faithfullyFlat : inclusion.hom.FaithfullyFlat
  isPushout : IsPushout inclusion inclusion E.t.appTop E.s.appTop

namespace FaithfullyFlatRingQuotient

variable {E : EtaleEquivalenceRelation.{u}} (Q : E.FaithfullyFlatRingQuotient)
variable [IsAffine E.U]

/-- The morphism from the object scheme to the spectrum of the proposed quotient ring. -/
noncomputable def quotientMap : E.U ⟶ Spec Q.baseRing :=
  E.U.isoSpec.hom ≫ Spec.map Q.inclusion

instance quotientMap_flat : Flat Q.quotientMap := by
  have : Flat (Spec.map Q.inclusion) :=
    ((flat_and_surjective_SpecMap_iff Q.inclusion).mpr Q.faithfullyFlat).1
  dsimp [quotientMap]
  infer_instance

instance quotientMap_surjective : Surjective Q.quotientMap := by
  have : Surjective (Spec.map Q.inclusion) :=
    ((flat_and_surjective_SpecMap_iff Q.inclusion).mpr Q.faithfullyFlat).2
  dsimp [quotientMap]
  infer_instance

/-- The relation is the kernel pair of the morphism to the proposed quotient spectrum. -/
theorem isPullback_quotientMap [IsAffine E.R] :
    IsPullback E.t E.s Q.quotientMap Q.quotientMap := by
  have hpb :
      IsPullback (Spec.map E.t.appTop) (Spec.map E.s.appTop)
        (Spec.map Q.inclusion) (Spec.map Q.inclusion) :=
    isPullback_SpecMap_of_isPushout Q.inclusion Q.inclusion
      E.t.appTop E.s.appTop Q.isPushout
  refine hpb.of_iso E.R.isoSpec.symm E.U.isoSpec.symm E.U.isoSpec.symm
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa [Iso.symm_hom] using Scheme.isoSpec_inv_naturality E.t
  · simpa [Iso.symm_hom] using Scheme.isoSpec_inv_naturality E.s
  · simp [quotientMap]
  · simp [quotientMap]

/-- The quotient morphism is étale by descent from the first projection of the relation. -/
instance quotientMap_etale [IsAffine E.R] : Etale Q.quotientMap := by
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) Q.isPullback_quotientMap
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact E.etale_t

include Q in
/-- A faithfully flat coordinate-ring pushout gives an affine quotient in the published
sense. The quotient map is in fact étale. -/
theorem hasAffineQuotient [IsAffine E.R] : E.HasAffineQuotient :=
  ⟨Spec Q.baseRing, Q.quotientMap, inferInstance, Q.isPullback_quotientMap,
    inferInstance, inferInstance, inferInstance⟩

end FaithfullyFlatRingQuotient

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
