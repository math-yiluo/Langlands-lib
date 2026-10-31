import Langlands.Geometry.Analytic.StrongAtlasMaps
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Singleton atlases on actual presented affinoid spectra -/

noncomputable section

universe u

namespace Langlands.Analytic

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidSpace

/-- The whole actual spectrum is its one atlas chart, including when empty.
Every restriction and every domain factorization is the actual identity. -/
def singletonAtlas (A : PresentedAffinoidSpace K) :
    IndexedAffinoidAtlas.{u, u, 0} K (BanachSpectrum A.unop) where
  Index := PUnit.{1}
  algebra _ := A.unop
  chart _ := _root_.id
  isEmbedding_chart _ := Topology.IsEmbedding.id
  chartDomain_injective _ _ _ := Subsingleton.elim _ _
  locallyHausdorff _ := ⟨Set.univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := by
    convert AtlasTopology.isNet_singleton_univ (X := BanachSpectrum A.unop) using 1
    ext U
    simp
  restriction _ _ _ := BoundedAlgHom.id K A.unop
  restriction_chart _ _ _ _ := rfl
  restriction_universal _ _ _ _R φ _ := by
    refine ⟨φ, BoundedAlgHom.comp_id φ, ?_⟩
    intro ψ hψ
    simpa only [BoundedAlgHom.comp_id] using hψ
  restriction_id _ _ := rfl
  restriction_comp _ _ _ _ _ _ := rfl

/-- The actual spectrum and its constructed singleton atlas. -/
def atlasPresentation (A : PresentedAffinoidSpace K) :
    AffinoidAtlasPresentation.{u, u, 0} K where
  space := (affinoidSpectrumFunctor K).obj A
  atlas := A.singletonAtlas

/-- The unique index is a greatest chart even when the spectrum is empty. -/
theorem atlasPresentation_top_contains (A : PresentedAffinoidSpace K)
    (i : A.atlasPresentation.atlas.Index) :
    Set.range (A.atlasPresentation.atlas.chart i) ⊆
      Set.range (A.atlasPresentation.atlas.chart PUnit.unit) := Subset.rfl

/-- A genuine bounded algebra map gives a chosen singleton-atlas map,
with its original contravariant pullback. -/
def atlasMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    A.atlasPresentation ⟶ B.atlasPresentation where
  baseMap := BanachSpectrum.comapContinuous f.unop.toBoundedRingHom
  indexMap _ := PUnit.unit
  index_mono _ _ _ := Subset.rfl
  pullback _ := f.unop
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

@[simp]
theorem atlasMap_pullback {A B : PresentedAffinoidSpace K} (f : A ⟶ B)
    (i : A.atlasPresentation.atlas.Index) :
    (atlasMap f).pullback i = f.unop := rfl

/-- Read the actual bounded algebra map from the unique chart pullback. -/
def fromAtlasMap {A B : PresentedAffinoidSpace K}
    (f : A.atlasPresentation ⟶ B.atlasPresentation) : A ⟶ B :=
  Quiver.Hom.op (show B.unop ⟶ A.unop from f.pullback PUnit.unit)

@[simp]
theorem fromAtlasMap_atlasMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    fromAtlasMap (atlasMap f) = f := rfl

/-- Every chosen map between these singleton atlases is recovered in full
from its actual bounded pullback, including the continuous map. -/
@[simp]
theorem atlasMap_fromAtlasMap {A B : PresentedAffinoidSpace K}
    (f : A.atlasPresentation ⟶ B.atlasPresentation) :
    atlasMap (fromAtlasMap f) = f := by
  refine AffinoidAtlasPresentation.Hom.ext ?_ (funext fun i => Subsingleton.elim (α := PUnit.{1}) _ _) ?_
  · exact ContinuousMap.ext (fun x => f.chart_comm PUnit.unit x)
  · apply heq_of_eq
    funext i
    cases i
    rfl

/-- A bijection of the actual bounded algebra maps and chosen atlas maps. -/
def atlasHomEquiv (A B : PresentedAffinoidSpace K) :
    (A ⟶ B) ≃ (A.atlasPresentation ⟶ B.atlasPresentation) where
  toFun := atlasMap
  invFun := fromAtlasMap
  left_inv := fromAtlasMap_atlasMap
  right_inv := atlasMap_fromAtlasMap

/-- Singleton atlases realize the actual opposite bounded-algebra category. -/
def atlasFunctor : PresentedAffinoidSpace K ⥤ AffinoidAtlasPresentation.{u, u, 0} K where
  obj := atlasPresentation
  map := atlasMap
  map_id A := by
    refine AffinoidAtlasPresentation.Hom.ext ?_ rfl (heq_of_eq (funext fun _ => rfl))
    exact ContinuousMap.ext (fun x => BanachSpectrum.ext (fun _ => rfl))
  map_comp f g := by
    refine AffinoidAtlasPresentation.Hom.ext ?_ rfl (heq_of_eq (funext fun _ => rfl))
    exact ContinuousMap.ext (fun x => BanachSpectrum.ext (fun _ => rfl))

/-- Explicit inverse on morphisms; no pointwise criterion for algebra maps is used. -/
def atlasFullyFaithful : (atlasFunctor (K := K)).FullyFaithful where
  preimage := fromAtlasMap
  map_preimage := atlasMap_fromAtlasMap
  preimage_map := fromAtlasMap_atlasMap

instance : (atlasFunctor (K := K)).Full where
  map_surjective {A B} := (atlasHomEquiv A B).surjective

instance : (atlasFunctor (K := K)).Faithful where
  map_injective {A B} := (atlasHomEquiv A B).injective

/-- The atlas realization retains the original spectrum diagram exactly. -/
theorem atlasFunctor_spaceFunctor :
    atlasFunctor (K := K) ⋙ AffinoidAtlasPresentation.spaceFunctor =
      affinoidSpectrumFunctor K := rfl

/-- Construct all-admissible-pair strong maps on the actual singleton atlases. -/
def strongAtlasMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    AffinoidAtlasPresentation.StrongHom A.atlasPresentation B.atlasPresentation :=
  AffinoidAtlasPresentation.StrongHom.ofTopChart (atlasMap f) PUnit.unit
    B.atlasPresentation_top_contains

/-- The strong map retains the original bounded map on the actual quotients. -/
theorem strongAtlasMap_pullback {A B : PresentedAffinoidSpace K} (f : A ⟶ B)
    (i : A.atlasPresentation.atlas.Index)
    (h : (strongAtlasMap f).baseMap '' Set.range (A.atlasPresentation.atlas.chart i) ⊆
      Set.range (B.atlasPresentation.atlas.chart PUnit.unit)) :
    (strongAtlasMap f).pullback i PUnit.unit h = f.unop :=
  AffinoidAtlasPresentation.StrongHom.ofTopChart_pullback_selected (atlasMap f)
    PUnit.unit B.atlasPresentation_top_contains i

/-- Strong singleton-atlas data are recovered from an actual algebra map. -/
theorem strongAtlasMap_fromChosen {A B : PresentedAffinoidSpace K}
    (f : AffinoidAtlasPresentation.StrongHom A.atlasPresentation B.atlasPresentation) :
    strongAtlasMap (fromAtlasMap
      (f.toChosen PUnit.unit B.atlasPresentation_top_contains)) = f := by
  unfold strongAtlasMap
  rw [atlasMap_fromAtlasMap]
  exact f.ofTopChart_toChosen PUnit.unit B.atlasPresentation_top_contains

/-- Every full strong map between singleton presentations corresponds to
exactly one actual bounded algebra map, including on nonreduced algebras. -/
def strongAtlasHomEquiv (A B : PresentedAffinoidSpace K) :
    (A ⟶ B) ≃
      AffinoidAtlasPresentation.StrongHom A.atlasPresentation B.atlasPresentation where
  toFun := strongAtlasMap
  invFun f := fromAtlasMap (f.toChosen PUnit.unit B.atlasPresentation_top_contains)
  left_inv f := by
    apply Quiver.Hom.unop_inj
    exact strongAtlasMap_pullback f PUnit.unit
      ((strongAtlasMap f).image_chart_top PUnit.unit B.atlasPresentation_top_contains
        PUnit.unit)
  right_inv := strongAtlasMap_fromChosen

end PresentedAffinoidSpace

end Langlands.Analytic
