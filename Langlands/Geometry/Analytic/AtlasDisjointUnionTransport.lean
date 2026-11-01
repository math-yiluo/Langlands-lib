import Langlands.Geometry.Analytic.AtlasDisjointUnionMaps

/-! # Componentwise transport of disjoint unions of supplied atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasDisjointUnion

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I J L : Type z}
  (A : I → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hA : ∀ i, (A i).atlas.HasNonemptyCharts)
  (B : J → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hB : ∀ j, (B j).atlas.HasNonemptyCharts)

/-- Reindex components and apply their actual complete chosen bounded arrows. -/
def map (r : I → J) (f : ∀ i, A i ⟶ B (r i)) :
    presentation A hA ⟶ presentation B hB :=
  desc A hA (fun i => f i ≫ inclusion B hB (r i))

@[simp]
theorem map_baseMap (r : I → J) (f : ∀ i, A i ⟶ B (r i))
    (i : I) (x : (A i).space) :
    (map A hA B hB r f).baseMap ⟨i, x⟩ = ⟨r i, (f i).baseMap x⟩ := rfl

@[simp]
theorem map_indexMap (r : I → J) (f : ∀ i, A i ⟶ B (r i))
    (i : I) (c : (A i).atlas.Index) :
    (map A hA B hB r f).indexMap ⟨i, c⟩ = ⟨r i, (f i).indexMap c⟩ := rfl

@[simp]
theorem map_pullback (r : I → J) (f : ∀ i, A i ⟶ B (r i))
    (i : I) (c : (A i).atlas.Index) :
    (map A hA B hB r f).pullback ⟨i, c⟩ = (f i).pullback c := by
  exact BoundedAlgHom.comp_id _

/-- The equation includes the original chosen charts and bounded pullbacks. -/
@[simp]
theorem inclusion_map (r : I → J) (f : ∀ i, A i ⟶ B (r i)) (i : I) :
    inclusion A hA i ≫ map A hA B hB r f = f i ≫ inclusion B hB (r i) :=
  inclusion_desc A hA _ i

@[simp]
theorem map_id :
    map A hA A hA _root_.id (fun i => 𝟙 (A i)) = 𝟙 (presentation A hA) := by
  apply hom_ext A hA
  intro i
  simp only [inclusion_map, Category.id_comp, Category.comp_id]
  rfl

variable (C : L → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hC : ∀ k, (C k).atlas.HasNonemptyCharts)

/-- Reindexing and the full component maps compose in the same order. -/
theorem map_comp (r : I → J) (s : J → L)
    (f : ∀ i, A i ⟶ B (r i)) (g : ∀ j, B j ⟶ C (s j)) :
    map A hA B hB r f ≫ map B hB C hC s g =
      map A hA C hC (s ∘ r) (fun i => f i ≫ g (r i)) := by
  apply hom_ext A hA
  intro i
  rw [← Category.assoc, inclusion_map, Category.assoc, inclusion_map,
    inclusion_map, Category.assoc]
  rfl

end Langlands.Analytic.AtlasDisjointUnion
