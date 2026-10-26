import Langlands.Cohomology.AcyclicResolution.Statement

/-!
# The resolution comparison commutes with derived natural transformations

Proof of `Langlands.Cohomology.ResolutionComparisonTransformationStatement`: for a natural
transformation `α : F ⟶ G` of additive functors, the comparison maps `Hⁿ(F K) ⟶ Rⁿ F A` and
`Hⁿ(G K) ⟶ Rⁿ G A` induced by an augmentation-compatible map `φ : K ⟶ I` to an injective
resolution intertwine `Hⁿ(α_K)` and `(NatTrans.rightDerived α n).app A`. Mathlib's
`InjectiveResolution.rightDerived_app_eq` computes the derived transformation on `I`; the
remaining step is the naturality of `NatTrans.mapHomologicalComplex α _` at `φ`. Neither the
quasi-isomorphism hypothesis nor the augmentation compatibility is used.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u v u' v'

/-- The resolution comparison commutes with the right-derived natural transformation. -/
theorem resolutionComparisonTransformationStatement :
    ResolutionComparisonTransformationStatement.{u, v, u', v'} := by
  intro C _ _ _ D _ _ F G _ _ α A K ε _ I φ _ n
  rw [InjectiveResolution.rightDerived_app_eq α I n, Iso.inv_hom_id_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rw [← (NatTrans.mapHomologicalComplex α _).naturality φ]

end Langlands.Cohomology
