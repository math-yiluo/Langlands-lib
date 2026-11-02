import Langlands.AlgebraicGeometry.SchemeDifferentialSlice
import Langlands.AlgebraicGeometry.SmoothRelationGoodPointChart
import Langlands.AlgebraicGeometry.RelationSliceEtalePropagationProof

/-! # Etale slices through good points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation SmoothRelationGoodPoint

/-- A good point of a smooth equivalence relation lies on a preimmersed,
locally finitely presented slice whose full relation pullback is etale. -/
theorem exists_etale_slice_of_isGoodPoint
    {U R : Scheme.{u}} (t s : R ⟶ U) (hr : IsEquivRel t s) [Smooth s]
    (e : U ⟶ R) (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U)
    (x : U) (hgood : IsGoodPoint t s e x) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ U),
      IsPreimmersion g ∧ LocallyOfFinitePresentation g ∧
      ∃ a : Z, g a = x ∧ Etale (pullback.snd g t ≫ s) := by
  obtain ⟨V, hV, _, W, hW, heW, hWt, hWs⟩ :=
    exists_common_affine_slice_charts t s e het hes x
  let q := hW.primeIdealOf ⟨e x, heW⟩
  let := (s.appLE V W hWs).hom.toAlgebra
  let p := q.asIdeal.comap (s.appLE V W hWs).hom
  have hpq : p ≤ q.asIdeal.comap (t.appLE V W hWt).hom := by
    rw [comap_appLE_eq_comap_appLE het hes x hW heW hWs hWt]
  have hC := residueSpan_eq_top_of_isGoodPoint het hes x hV hW heW hWs hWt
    rfl q.asIdeal rfl hgood
  obtain ⟨Z, g, hgpre, hgfp, a, hax, hfe⟩ :=
    exists_identity_slice_of_residue_span t s e het x V hV W hW hWt hWs p q
      (hW.fromSpec_primeIdealOf ⟨e x, heW⟩) hpq hC
  have : IsPreimmersion g := hgpre
  have : LocallyOfFinitePresentation g := hgfp
  let σ : Z ⟶ pullback g t :=
    pullback.lift (𝟙 Z) (g ≫ e)
      (by simp only [Category.id_comp, Category.assoc, het, Category.comp_id])
  have hσ : σ ≫ pullback.fst g t = 𝟙 Z := by
    simp only [σ, pullback.lift_fst]
  obtain ⟨O, haO, he⟩ :=
    RelationSlice.exists_open_etale_of_section hr g σ hσ a hfe
  refine ⟨O, O.ι ≫ g, inferInstance, inferInstance, ⟨a, haO⟩, ?_, he⟩
  exact hax

end Langlands.AlgebraicGeometry
