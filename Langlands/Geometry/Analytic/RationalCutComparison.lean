import Langlands.Geometry.Analytic.RationalCutAtlas
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.StrongQuasiIsoComposition

/-! # Full strong comparison with the actual rational-cut atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra.Domain.Inclusion

/-- A bounded inclusion into an embedded full domain represents its actual
relative locus against every presented affinoid test. -/
theorem represents_of_injective {A : PresentedAffinoidAlgebra K}
    {U V : Domain K A} (f : U ⟶ V)
    (hinj : Function.Injective V.spectrumMap) :
    Represents K f.restriction (V.spectrumMap ⁻¹' U.locus) := by
  have hrep : Represents K (f.restriction.comp V.baseMap) U.locus := by
    rw [f.comp_baseMap]
    exact U.represents
  exact V.represents.of_comp_of_injective hrep hinj

end PresentedAffinoidAlgebra.Domain.Inclusion

namespace RationalCutAtlas

variable {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (t : a.Index)
  (ht : ∀ i, Set.range (a.chart i) ⊆ Set.range (a.chart t))

/-- Original atlas restrictions are actual arrows over the common base. -/
def originalInclusion (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    a.restrictionDomain i t (ht i) ⟶ a.restrictionDomain j t (ht j) where
  restriction := a.restriction i j h
  comp_baseMap := (a.restriction_comp i j t h (ht j) (ht i)).symm

/-- A contained original chart maps to a cut via the full common-base
representations, retaining its original algebra. -/
def fromOriginalInclusion (i : a.Index) (s : Index a t)
    (h : Set.range (a.chart i) ⊆ Set.range (chart a t ht s)) :
    a.restrictionDomain i t (ht i) ⟶ s.domain a t ht :=
  Domain.inclusionOfSubset _ _ (by
    rw [Index.domain_locus_eq_preimage]
    change a.chart t ⁻¹' Set.range (a.chart i) ⊆ a.chart t ⁻¹' s.val
    exact Set.preimage_mono ((range_chart a t ht s) ▸ h))

/-- A cut contained in an original chart maps to that chart using its
actual full domain representation over the same base. -/
def toOriginalInclusion (s : Index a t) (i : a.Index)
    (h : Set.range (chart a t ht s) ⊆ Set.range (a.chart i)) :
    s.domain a t ht ⟶ a.restrictionDomain i t (ht i) :=
  Domain.inclusionOfSubset _ _ (by
    rw [Index.domain_locus_eq_preimage]
    change a.chart t ⁻¹' s.val ⊆ a.chart t ⁻¹' Set.range (a.chart i)
    exact Set.preimage_mono ((range_chart a t ht s) ▸ h))

/-- Full domain uniqueness proves bounded-map naturality in both charts. -/
theorem fromOriginalInclusion_naturality (i i' : a.Index) (s s' : Index a t)
    (hi : Set.range (a.chart i) ⊆ Set.range (a.chart i'))
    (hs : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht s'))
    (h : Set.range (a.chart i) ⊆ Set.range (chart a t ht s))
    (h' : Set.range (a.chart i') ⊆ Set.range (chart a t ht s')) :
    (a.restriction i i' hi).comp (fromOriginalInclusion a t ht i' s' h').restriction =
      (fromOriginalInclusion a t ht i s h).restriction.comp (restriction a t ht s s' hs) :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (a.restrictionDomain i t (ht i))
      (s'.domain a t ht)) inferInstance
      (originalInclusion a t ht i i' hi ≫ fromOriginalInclusion a t ht i' s' h')
      (fromOriginalInclusion a t ht i s h ≫ inclusion a t ht s s' hs))

/-- The reverse comparison also commutes with all bounded restrictions. -/
theorem toOriginalInclusion_naturality (s s' : Index a t) (i i' : a.Index)
    (hs : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht s'))
    (hi : Set.range (a.chart i) ⊆ Set.range (a.chart i'))
    (h : Set.range (chart a t ht s) ⊆ Set.range (a.chart i))
    (h' : Set.range (chart a t ht s') ⊆ Set.range (a.chart i')) :
    (restriction a t ht s s' hs).comp (toOriginalInclusion a t ht s' i' h').restriction =
      (toOriginalInclusion a t ht s i h).restriction.comp (a.restriction i i' hi) :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (s.domain a t ht)
      (a.restrictionDomain i' t (ht i'))) inferInstance
      (inclusion a t ht s s' hs ≫ toOriginalInclusion a t ht s' i' h')
      (toOriginalInclusion a t ht s i h ≫ originalInclusion a t ht i i' hi))

/-- At an original locus the forward comparison is exactly the inverse
of the constructed bounded algebra equivalence. -/
theorem fromOriginalInclusion_original (i : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (chart a t ht (Index.ofOriginal a t i))) :
    (fromOriginalInclusion a t ht i (Index.ofOriginal a t i) h).restriction =
      (originalAlgebraEquiv a t ht i).symm.toBoundedAlgHom := by
  apply Domain.boundedHom_eq_of_over_base ((Index.ofOriginal a t i).domain a t ht)
    (a.restrictionDomain i t (ht i))
  · exact (fromOriginalInclusion a t ht i (Index.ofOriginal a t i) h).comp_baseMap
  · exact Domain.boundedEquivOfLocusEq_symm_comp_baseMap _ _ (original_domain_locus a t ht i)

/-- The reverse map at the same original locus is the forward bounded equivalence. -/
theorem toOriginalInclusion_original (i : a.Index)
    (h : Set.range (chart a t ht (Index.ofOriginal a t i)) ⊆ Set.range (a.chart i)) :
    (toOriginalInclusion a t ht (Index.ofOriginal a t i) i h).restriction =
      (originalAlgebraEquiv a t ht i).toBoundedAlgHom := by
  apply Domain.boundedHom_eq_of_over_base (a.restrictionDomain i t (ht i))
    ((Index.ofOriginal a t i).domain a t ht)
  · exact (toOriginalInclusion a t ht (Index.ofOriginal a t i) i h).comp_baseMap
  · exact originalAlgebraEquiv_comp_restriction a t ht i

/-- The actual bounded equivalences commute with every old restriction,
including its entire algebraic information. The index universes are arbitrary. -/
theorem originalAlgebraEquiv_naturality (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (h' : Set.range (chart a t ht (Index.ofOriginal a t i)) ⊆
      Set.range (chart a t ht (Index.ofOriginal a t j))) :
    (restriction a t ht (Index.ofOriginal a t i) (Index.ofOriginal a t j) h').comp
        (originalAlgebraEquiv a t ht j).toBoundedAlgHom =
      (originalAlgebraEquiv a t ht i).toBoundedAlgHom.comp (a.restriction i j h) := by
  apply Domain.boundedHom_eq_of_over_base (a.restrictionDomain j t (ht j))
    ((Index.ofOriginal a t i).domain a t ht)
  · change ((restriction a t ht (Index.ofOriginal a t i) (Index.ofOriginal a t j) h').comp
      (originalAlgebraEquiv a t ht j).toBoundedAlgHom).comp (a.restriction j t (ht j)) = _
    calc
      _ = (restriction a t ht (Index.ofOriginal a t i) (Index.ofOriginal a t j) h').comp
          ((originalAlgebraEquiv a t ht j).toBoundedAlgHom.comp
            (a.restriction j t (ht j))) := rfl
      _ = (restriction a t ht (Index.ofOriginal a t i) (Index.ofOriginal a t j) h').comp
          ((Index.ofOriginal a t j).domain a t ht).baseMap :=
        congrArg
          (fun q => (restriction a t ht (Index.ofOriginal a t i) (Index.ofOriginal a t j) h').comp q)
          (originalAlgebraEquiv_comp_restriction a t ht j)
      _ = _ := restriction_comp_baseMap a t ht _ _ h'
  · change ((originalAlgebraEquiv a t ht i).toBoundedAlgHom.comp
      (a.restriction i j h)).comp (a.restriction j t (ht j)) = _
    exact (congrArg (fun q => (originalAlgebraEquiv a t ht i).toBoundedAlgHom.comp q)
      (a.restriction_comp i j t h (ht j) (ht i)).symm).trans
        (originalAlgebraEquiv_comp_restriction a t ht i)

/-- Lift the original indices to a common universe; its algebras, points,
charts and restrictions remain the actual original ones. -/
def originalPresentation : AffinoidAtlasPresentation.{u, v, max v w} K where
  space := TopCat.of X
  atlas := a.reindex (Equiv.ulift : ULift.{v} a.Index ≃ a.Index)

/-- Lift the rational-cut indices to the same common universe, preserving
all of the constructed atlas data. -/
def presentation : AffinoidAtlasPresentation.{u, v, max v w} K where
  space := TopCat.of X
  atlas := (atlas a t ht).reindex (Equiv.ulift : ULift.{w} (Index a t) ≃ Index a t)

/-- All admissible old-to-cut pairs use the actual common-base inclusion. -/
def fromOriginal : StrongHom (originalPresentation a) (presentation a t ht) where
  baseMap := ContinuousMap.id X
  target_exists i := ⟨⟨Index.ofOriginal a t i.down⟩, by
    change _root_.id '' Set.range (a.chart i.down) ⊆
      Set.range ((atlas a t ht).chart (Index.ofOriginal a t i.down))
    rw [Set.image_id, atlas_ofOriginal_range]⟩
  pullback i s h := (fromOriginalInclusion a t ht i.down s.down (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm i s h x := by
    exact (congrArg (a.chart t)
      ((fromOriginalInclusion a t ht i.down s.down (fun x hx => h ⟨x, hx, rfl⟩)).spectrumMap_over_base x)).trans
        (a.restriction_chart i.down t (ht i.down) x)
  restriction_comm i i' s s' hi hs h h' :=
    fromOriginalInclusion_naturality a t ht i.down i'.down s.down s'.down hi hs
      (fun x hx => h ⟨x, hx, rfl⟩) (fun x hx => h' ⟨x, hx, rfl⟩)

/-- The reverse full strong map has the same underlying identity. -/
def toOriginal : StrongHom (presentation a t ht) (originalPresentation a) where
  baseMap := ContinuousMap.id X
  target_exists _ := ⟨⟨t⟩, fun x _ => greatest_chart_surjective a t ht x⟩
  pullback s i h := (toOriginalInclusion a t ht s.down i.down (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm s i h x := by
    exact (a.restriction_chart i.down t (ht i.down) _).symm.trans
      (congrArg (a.chart t)
        ((toOriginalInclusion a t ht s.down i.down (fun x hx => h ⟨x, hx, rfl⟩)).spectrumMap_over_base x))
  restriction_comm s s' i i' hs hi h h' :=
    toOriginalInclusion_naturality a t ht s.down s'.down i.down i'.down hs hi
      (fun x hx => h ⟨x, hx, rfl⟩) (fun x hx => h' ⟨x, hx, rfl⟩)

@[simp]
theorem fromOriginal_baseMap : (fromOriginal a t ht).baseMap = ContinuousMap.id X := rfl

@[simp]
theorem toOriginal_baseMap : (toOriginal a t ht).baseMap = ContinuousMap.id X := rfl

/-- The full strong comparison at a retained original chart uses the
same inverse bounded equivalence as the common-base construction. -/
theorem fromOriginal_pullback_original (i : a.Index)
    (h : (fromOriginal a t ht).baseMap ''
      Set.range ((originalPresentation a).atlas.chart (ULift.up i)) ⊆
      Set.range ((presentation a t ht).atlas.chart (ULift.up (Index.ofOriginal a t i)))) :
    (fromOriginal a t ht).pullback (ULift.up i) (ULift.up (Index.ofOriginal a t i)) h =
      (originalAlgebraEquiv a t ht i).symm.toBoundedAlgHom :=
  fromOriginalInclusion_original a t ht i (fun x hx => h ⟨x, hx, rfl⟩)

/-- Its reverse retained-chart pullback is exactly the forward equivalence. -/
theorem toOriginal_pullback_original (i : a.Index)
    (h : (toOriginal a t ht).baseMap ''
      Set.range ((presentation a t ht).atlas.chart (ULift.up (Index.ofOriginal a t i))) ⊆
      Set.range ((originalPresentation a).atlas.chart (ULift.up i))) :
    (toOriginal a t ht).pullback (ULift.up (Index.ofOriginal a t i)) (ULift.up i) h =
      (originalAlgebraEquiv a t ht i).toBoundedAlgHom :=
  toOriginalInclusion_original a t ht i (fun x hx => h ⟨x, hx, rfl⟩)

/-- Every old-to-cut local map represents the exact relative chart image
against all positive-polyradius affinoid tests. -/
theorem isQuasiIso_fromOriginal : (fromOriginal a t ht).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i s h
  change ULift.{v} a.Index at i
  change ULift.{w} (Index a t) at s
  change Represents K (fromOriginalInclusion a t ht i.down s.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
    (chart a t ht s.down ⁻¹' (_root_.id '' Set.range (a.chart i.down)))
  rw [Set.image_id]
  have hrep := (fromOriginalInclusion a t ht i.down s.down (fun x hx => h ⟨x, hx, rfl⟩)).represents_of_injective
    (isEmbedding_cutDomain_spectrumMap a t ht _ _).injective
  exact hrep

/-- Every cut-to-old local map is likewise a full affinoid-domain representation. -/
theorem isQuasiIso_toOriginal : (toOriginal a t ht).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro s i h
  change ULift.{w} (Index a t) at s
  change ULift.{v} a.Index at i
  change Represents K (toOriginalInclusion a t ht s.down i.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
    (a.chart i.down ⁻¹' (_root_.id '' Set.range (chart a t ht s.down)))
  rw [Set.image_id]
  have hrep := (toOriginalInclusion a t ht s.down i.down (fun x hx => h ⟨x, hx, rfl⟩)).represents_of_injective
    (a.isEmbedding_restriction i.down t (ht i.down)).injective
  have hlocus : (a.restrictionDomain i.down t (ht i.down)).spectrumMap ⁻¹'
      (s.down.domain a t ht).locus = a.chart i.down ⁻¹' Set.range (chart a t ht s.down) := by
    rw [Index.domain_locus_eq_preimage, range_chart]
    ext x
    change a.chart t (BanachSpectrum.comap (a.restriction i.down t (ht i.down)).toBoundedRingHom x) ∈
      s.down.val ↔ a.chart i.down x ∈ s.down.val
    exact (congrArg (fun y : X => y ∈ s.down.val)
      (a.restriction_chart i.down t (ht i.down) x)).to_iff
  rw [hlocus] at hrep
  exact hrep

end RationalCutAtlas
end Langlands.Analytic
