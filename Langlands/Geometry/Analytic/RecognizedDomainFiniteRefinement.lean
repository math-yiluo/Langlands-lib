import Langlands.Geometry.Analytic.RecognizedAffinoidAtlas
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure

/-! # Actual finite original local-domain refinements inside recognized charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace RecognizedSubset

variable (V : a.RecognizedSubset)

/-- The actual ambient map of a full domain in the constructed chart. -/
def domainAmbientMap (D : Domain K V.algebra) : C(BanachSpectrum D.algebra, X) :=
  V.chart.comp D.spectrumMap

/-- The literal ambient subset of that domain. -/
def domainLocus (D : Domain K V.algebra) : Set X := V.chart '' D.locus

theorem range_domainAmbientMap (D : Domain K V.algebra) :
    Set.range (V.domainAmbientMap D) = V.domainLocus D := by
  change Set.range (V.chart ∘ D.spectrumMap) = V.chart '' D.locus
  rw [Set.range_comp]
  exact congrArg (fun S : Set (BanachSpectrum V.algebra) => V.chart '' S)
    D.represents.2.1

theorem isEmbedding_domainAmbientMap (D : Domain K V.algebra) :
    Topology.IsEmbedding (V.domainAmbientMap D) :=
  V.isEmbedding_chart.comp (Domain.spectrumEmbedding K V.algebra D).isEmbedding

/-- Intersect the unchanged domain with a witnessed original component.
The algebra is the actual affinoid pushout quotient. -/
def domainComponentIntersection (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) : Domain K V.algebra :=
  D.inter (V.property.componentDomain i)

/-- The same quotient algebra, now a full domain over the unchanged original
component algebra, using the second actual quotient leg. -/
def domainLocalPiece (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) : LocalDomain a :=
  ⟨V.property.cover.index i,
    (V.property.componentDomain i).relative (V.domainComponentIntersection D i)
      (D.interRight (V.property.componentDomain i))⟩

/-- The same quotient algebra over the unchanged domain algebra, using the
first actual quotient leg. These pieces cover its whole spectrum. -/
def domainFiniteCover (D : Domain K V.algebra) :
    Domain.FiniteCover (Domain.whole K D.algebra) where
  size := V.property.cover.size
  obj i := D.relative (V.domainComponentIntersection D i)
    (D.interLeft (V.property.componentDomain i))
  map i := ⟨(D.interLeft (V.property.componentDomain i)).restriction, rfl⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := V.componentCover.covers (D.spectrumMap x) (Set.mem_univ _)
    let j : Fin V.property.cover.size := i
    change D.spectrumMap x ∈ (V.property.componentDomain j).locus at hi
    refine ⟨j, ?_⟩
    exact (D.relative_locus_eq_preimage (V.domainComponentIntersection D j)
      (D.interLeft (V.property.componentDomain j))).symm ▸
        ⟨D.represents.hasImageIn x, hi⟩

@[simp]
theorem domainFiniteCover_obj_algebra (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) :
    ((V.domainFiniteCover D).obj i).algebra = (V.domainLocalPiece D i).algebra := rfl

@[simp]
theorem domainLocalPiece_baseMap (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) :
    (V.domainLocalPiece D i).domain.baseMap =
      AffinoidPushout.rightMap D.baseMap (V.property.componentDomain i).baseMap := rfl

@[simp]
theorem domainFiniteCover_restriction (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) :
    ((V.domainFiniteCover D).map i).restriction =
      AffinoidPushout.leftMap D.baseMap (V.property.componentDomain i).baseMap := rfl

/-- The two retained full bounded maps commute over the entire recognized
algebra, including information invisible on spectrum points. -/
theorem domainLocalPiece_baseMap_comp (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) :
    (V.domainLocalPiece D i).domain.baseMap.comp
        (V.property.componentDomain i).baseMap =
      ((V.domainFiniteCover D).map i).restriction.comp D.baseMap :=
  (AffinoidPushout.condition D.baseMap (V.property.componentDomain i).baseMap).symm

/-- Each local piece is precisely the literal intersection with its original
component; no global ambient Hausdorff assumption is needed. -/
theorem domainLocalPiece_locus (D : Domain K V.algebra)
    (i : Fin V.property.cover.size) :
    (V.domainLocalPiece D i).locus =
      V.domainLocus D ∩ Set.range (a.chart (V.property.cover.index i)) := by
  change a.chart (V.property.cover.index i) ''
    ((V.property.componentDomain i).relative (V.domainComponentIntersection D i)
      (D.interRight (V.property.componentDomain i))).locus = _
  calc
    _ = V.chart '' ((V.property.componentDomain i).spectrumMap ''
        ((V.property.componentDomain i).relative (V.domainComponentIntersection D i)
          (D.interRight (V.property.componentDomain i))).locus) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(V.property.componentDomain i).spectrumMap y, ⟨y, hy, rfl⟩,
          V.property.componentDomain_over_ambient i y⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, (V.property.componentDomain_over_ambient i y).symm⟩
    _ = V.chart '' (V.domainComponentIntersection D i).locus :=
      congrArg (fun S : Set (BanachSpectrum V.algebra) => V.chart '' S)
        ((V.property.componentDomain i).image_relative_locus
          (V.domainComponentIntersection D i) (D.interRight (V.property.componentDomain i)))
    _ = _ := by
      change V.chart '' (D.locus ∩ (V.property.componentDomain i).locus) = _
      ext x
      constructor
      · rintro ⟨y, ⟨hyD, hyC⟩, rfl⟩
        exact ⟨⟨y, hyD, rfl⟩, hyC⟩
      · rintro ⟨⟨y, hyD, rfl⟩, hyC⟩
        exact ⟨y, ⟨hyD, hyC⟩, rfl⟩

/-- The unchanged quotient spectra identify both actual ambient maps. -/
theorem domainLocalPiece_over_ambient (D : Domain K V.algebra)
    (i : Fin V.property.cover.size)
    (x : BanachSpectrum (V.domainLocalPiece D i).algebra) :
    (V.domainLocalPiece D i).ambientMap x =
      V.domainAmbientMap D (((V.domainFiniteCover D).obj i).spectrumMap x) := by
  change a.chart (V.property.cover.index i)
    (BanachSpectrum.comap (V.domainLocalPiece D i).domain.baseMap.toBoundedRingHom x) = _
  rw [← V.property.componentDomain_over_ambient i]
  apply congrArg V.chart
  exact BanachSpectrum.ext fun b =>
    congrArg (fun q : BoundedAlgHom K V.algebra (V.domainLocalPiece D i).algebra => x (q b))
      (V.domainLocalPiece_baseMap_comp D i)

/-- Every full domain in a recognized chart is covered by finitely many
actual original local domains with the displayed quotient algebras. -/
theorem domainLocalPiece_covers (D : Domain K V.algebra) :
    (⋃ i, (V.domainLocalPiece D i).locus) = V.domainLocus D := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ((V.domainLocalPiece_locus D i).subset hi).1
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := V.componentCover.covers y (Set.mem_univ _)
    apply Set.mem_iUnion.mpr
    refine ⟨i, (V.domainLocalPiece_locus D i).symm ▸ ?_⟩
    exact ⟨⟨y, hy, rfl⟩, hi⟩

end RecognizedSubset

variable (a)

/-- A full domain in a chart recognized from the enlarged atlas has actual
pieces over the original atlas, with the same intersection quotient algebras. -/
def fullRecognitionDomainPiece (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) : LocalDomain a :=
  a.saturatedDomainToLocal (V.domainLocalPiece D i).index (V.domainLocalPiece D i).domain

@[simp]
theorem fullRecognitionDomainPiece_algebra (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) :
    (a.fullRecognitionDomainPiece V D i).algebra = ((V.domainFiniteCover D).obj i).algebra :=
  rfl

/-- Extension to the original chart composes the two actual bounded maps;
it leaves the affinoid pushout quotient unchanged. -/
theorem fullRecognitionDomainPiece_baseMap (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) :
    (a.fullRecognitionDomainPiece V D i).domain.baseMap =
      (V.domainLocalPiece D i).domain.baseMap.comp
        (a.saturatedRepresentative (V.domainLocalPiece D i).index).domain.baseMap :=
  rfl

theorem fullRecognitionDomainPiece_locus (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) :
    (a.fullRecognitionDomainPiece V D i).locus = (V.domainLocalPiece D i).locus :=
  a.saturatedDomainToLocal_locus (V.domainLocalPiece D i).index
    (V.domainLocalPiece D i).domain

theorem fullRecognitionDomainPiece_over_ambient (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size)
    (x : BanachSpectrum (a.fullRecognitionDomainPiece V D i).algebra) :
    (a.fullRecognitionDomainPiece V D i).ambientMap x =
      V.domainAmbientMap D (((V.domainFiniteCover D).obj i).spectrumMap x) :=
  V.domainLocalPiece_over_ambient D i x

/-- Every domain in a chart of the full recognition atlas is a finite
union of actual original local domains, with their displayed presentations. -/
theorem fullRecognitionDomainPiece_covers (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) :
    (⋃ i, (a.fullRecognitionDomainPiece V D i).locus) = V.domainLocus D := by
  simp_rw [a.fullRecognitionDomainPiece_locus V D]
  exact V.domainLocalPiece_covers D

end Langlands.Analytic.IndexedAffinoidAtlas
