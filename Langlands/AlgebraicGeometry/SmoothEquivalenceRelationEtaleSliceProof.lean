import Langlands.AlgebraicGeometry.SmoothEquivalenceRelationEtaleSliceStatement
import Langlands.AlgebraicGeometry.RelationEtaleSliceOfOrbits
import Langlands.AlgebraicGeometry.GoodPointEtaleSliceProof
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointExistence

/-! # Etale slices of smooth equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- The local good-point construction, saturation, and globalization give
the slicing conclusion once each orbit supplies a good point. -/
theorem exists_etale_surjective_slice_of_goodPoint_orbits
    {U R : Scheme.{u}} (t s : R ⟶ U) (hr : IsEquivRel t s) [Smooth s]
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U)
    (horbit : ∀ x : U, ∃ r : R, s r = x ∧
      SmoothRelationGoodPoint.IsGoodPoint t s e (t r)) :
    ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
      Etale (pullback.snd g t ≫ s) ∧ Surjective (pullback.snd g t ≫ s) := by
  apply exists_etale_surjective_slice_of_orbit_slices t s hr
    (SmoothRelationGoodPoint.IsGoodPoint t s e) horbit
  intro y hy
  obtain ⟨V, g, _, hfp, a, hay, he⟩ :=
    exists_etale_slice_of_isGoodPoint t s hr e het hes y hy
  have := hfp
  exact ⟨V, g, inferInstance, he, ⟨a, hay⟩⟩

/-- Every smooth equivalence relation of schemes has an etale surjective slice. -/
theorem smoothEquivalenceRelationEtaleSlice :
    SmoothEquivalenceRelationEtaleSliceStatement.{u} := by
  intro U R t s hr _ht hs
  have : Smooth s := hs
  obtain ⟨e, het, hes⟩ := hr.refl U (𝟙 U)
  exact exists_etale_surjective_slice_of_goodPoint_orbits t s hr e het hes
    (SmoothRelationGoodPoint.exists_isGoodPoint t s hr.mono hs e het hes)

end Langlands.AlgebraicGeometry
