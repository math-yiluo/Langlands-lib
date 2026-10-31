import Langlands.Geometry.Analytic.StrongAtlasComposition
import Langlands.Geometry.Analytic.AffinoidSpectrumAtlas
import Mathlib.CategoryTheory.Equivalence

/-! # Actual bounded affinoid comparison for greatest-chart presentations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.TopChartPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : TopChartPresentation.{u, v, w} K}

/-- The actual presented affinoid algebra of the greatest chart, oppositely. -/
def affinoid (A : TopChartPresentation.{u, v, w} K) : PresentedAffinoidSpace K :=
  Opposite.op (A.presentation.atlas.algebra A.topChart)

/-- Retain the bounded map at the greatest source and target charts. -/
def topPullback (f : A ⟶ B) :
    BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
      (A.presentation.atlas.algebra A.topChart) :=
  f.pullback A.topChart B.topChart (f.image_chart_top B.topChart B.top_contains A.topChart)

@[simp]
theorem topPullback_id (A : TopChartPresentation.{u, v, w} K) :
    topPullback (𝟙 A) = BoundedAlgHom.id K (A.presentation.atlas.algebra A.topChart) :=
  A.presentation.atlas.restriction_id A.topChart _

@[simp]
theorem topPullback_comp (f : A ⟶ B) (g : B ⟶ C) :
    topPullback (f ≫ g) = (topPullback f).comp (topPullback g) :=
  f.compOfTopCharts_pullback g B.topChart B.top_contains C.topChart C.top_contains
    A.topChart B.topChart C.topChart
    (f.image_chart_top B.topChart B.top_contains A.topChart)
    (g.image_chart_top C.topChart C.top_contains B.topChart)
    ((f ≫ g).image_chart_top C.topChart C.top_contains A.topChart)

/-- Top-chart bounded maps determine the full strong map algebraically. -/
theorem topPullback_injective : Function.Injective (topPullback (A := A) (B := B)) := by
  intro f g h
  have hb : f.baseMap = g.baseMap := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, rfl⟩ := A.topChart_surjective x
    exact (f.chart_comm A.topChart B.topChart _ y).symm.trans
      ((congrArg (fun φ => B.presentation.atlas.chart B.topChart
        (BanachSpectrum.comap φ.toBoundedRingHom y)) h).trans
          (g.chart_comm A.topChart B.topChart _ y))
  apply AffinoidAtlasPresentation.StrongHom.toChosen_injective B.topChart B.top_contains
  dsimp only
  refine AffinoidAtlasPresentation.Hom.ext hb rfl ?_
  apply heq_of_eq
  funext i
  exact (f.restriction_comp_pullback i A.topChart B.topChart (A.top_contains i)
    (f.image_chart_top B.topChart B.top_contains i)
    (f.image_chart_top B.topChart B.top_contains A.topChart)).symm.trans
      ((congrArg (fun φ => (A.presentation.atlas.restriction i A.topChart
        (A.top_contains i)).comp φ) h).trans
          (g.restriction_comp_pullback i A.topChart B.topChart (A.top_contains i)
            (g.image_chart_top B.topChart B.top_contains i)
            (g.image_chart_top B.topChart B.top_contains A.topChart)))

/-- Smaller charts have exactly the actual restriction coordinates in the top chart. -/
theorem topSpectrumHomeomorph_symm_chart (A : TopChartPresentation.{u, v, w} K)
    (i : A.presentation.atlas.Index) (x : BanachSpectrum (A.presentation.atlas.algebra i)) :
    A.topSpectrumHomeomorph.symm (A.presentation.atlas.chart i x) =
      BanachSpectrum.comap
        (A.presentation.atlas.restriction i A.topChart (A.top_contains i)).toBoundedRingHom x := by
  apply A.topSpectrumHomeomorph.injective
  rw [A.topSpectrumHomeomorph.apply_symm_apply]
  exact (A.presentation.atlas.restriction_chart i A.topChart (A.top_contains i) x).symm

/-- Construct chosen local pullbacks from an arbitrary actual top-algebra map. -/
def chosenOfPullback (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
    (A.presentation.atlas.algebra A.topChart)) : A.presentation ⟶ B.presentation where
  baseMap := (show C(_, _) from ⟨B.topSpectrumHomeomorph, B.topSpectrumHomeomorph.continuous⟩).comp
    ((BanachSpectrum.comapContinuous φ.toBoundedRingHom).comp
      (show C(_, _) from ⟨A.topSpectrumHomeomorph.symm, A.topSpectrumHomeomorph.symm.continuous⟩))
  indexMap _ := B.topChart
  index_mono _ _ _ := Subset.rfl
  pullback i := (A.presentation.atlas.restriction i A.topChart (A.top_contains i)).comp φ
  chart_comm i x := by
    change B.presentation.atlas.chart B.topChart
      (BanachSpectrum.comap φ.toBoundedRingHom
        (BanachSpectrum.comap
          (A.presentation.atlas.restriction i A.topChart (A.top_contains i)).toBoundedRingHom x)) =
      B.topSpectrumHomeomorph (BanachSpectrum.comap φ.toBoundedRingHom
        (A.topSpectrumHomeomorph.symm (A.presentation.atlas.chart i x)))
    rw [topSpectrumHomeomorph_symm_chart]
    rfl
  restriction_comm i i' hi := by
    rw [B.presentation.atlas.restriction_id, BoundedAlgHom.comp_id,
      ← BoundedAlgHom.comp_assoc, ← A.presentation.atlas.restriction_comp]

/-- All admissible bounded maps are constructed by actual domain factorization. -/
def ofTopPullback (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
    (A.presentation.atlas.algebra A.topChart)) : A ⟶ B :=
  AffinoidAtlasPresentation.StrongHom.ofTopChart (chosenOfPullback φ)
    B.topChart B.top_contains

/-- The inverse retains each actual source restriction followed by the given map. -/
theorem ofTopPullback_pullback_top
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
      (A.presentation.atlas.algebra A.topChart)) (i : A.presentation.atlas.Index)
    (h : (ofTopPullback φ).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart B.topChart)) :
    (ofTopPullback φ).pullback i B.topChart h =
      (A.presentation.atlas.restriction i A.topChart (A.top_contains i)).comp φ :=
  AffinoidAtlasPresentation.StrongHom.ofTopChart_pullback_selected
    (chosenOfPullback (A := A) (B := B) φ) B.topChart B.top_contains i

/-- At any admissible target the inverse is the actual bounded domain factorization. -/
theorem ofTopPullback_comp_restriction
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
      (A.presentation.atlas.algebra A.topChart))
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : (ofTopPullback φ).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart j)) :
    ((ofTopPullback φ).pullback i j h).comp
        (B.presentation.atlas.restriction j B.topChart (B.top_contains j)) =
      (A.presentation.atlas.restriction i A.topChart (A.top_contains i)).comp φ :=
  ((ofTopPullback φ).pullback_comp_restriction i j B.topChart (B.top_contains j) h
    ((ofTopPullback φ).image_chart_top B.topChart B.top_contains i)).symm.trans
      (ofTopPullback_pullback_top φ i _)

@[simp]
theorem topPullback_ofTopPullback
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
      (A.presentation.atlas.algebra A.topChart)) :
    topPullback (ofTopPullback φ) = φ := by
  have h := AffinoidAtlasPresentation.StrongHom.ofTopChart_pullback_selected
    (chosenOfPullback (A := A) (B := B) φ) B.topChart B.top_contains A.topChart
  change topPullback (ofTopPullback φ) =
    (A.presentation.atlas.restriction A.topChart A.topChart _).comp φ at h
  simpa only [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp] using h

@[simp]
theorem ofTopPullback_topPullback (f : A ⟶ B) : ofTopPullback (topPullback f) = f := by
  apply topPullback_injective
  exact topPullback_ofTopPullback _

/-- The actual bounded maps and all strong maps are in explicit bijection. -/
def topPullbackEquiv (A B : TopChartPresentation.{u, v, w} K) :
    (A ⟶ B) ≃ BoundedAlgHom K (B.presentation.atlas.algebra B.topChart)
      (A.presentation.atlas.algebra A.topChart) where
  toFun := topPullback
  invFun := ofTopPullback
  left_inv := ofTopPullback_topPullback
  right_inv := topPullback_ofTopPullback

/-- Recover the actual affinoid space and every bounded contravariant map. -/
def affinoidFunctor : TopChartPresentation.{u, v, w} K ⥤ PresentedAffinoidSpace K where
  obj := affinoid
  map f := Quiver.Hom.op (show (affinoid _).unop ⟶ (affinoid _).unop from topPullback f)
  map_id A := by
    apply Quiver.Hom.unop_inj
    exact topPullback_id A
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    exact topPullback_comp f g

/-- The inverse on actual morphisms uses constructed bounded factorizations. -/
def affinoidFullyFaithful : (affinoidFunctor.{u, v, w} (K := K)).FullyFaithful where
  preimage f := ofTopPullback f.unop
  map_preimage f := by
    apply Quiver.Hom.unop_inj
    exact topPullback_ofTopPullback f.unop
  preimage_map := ofTopPullback_topPullback

instance : (affinoidFunctor.{u, v, w} (K := K)).Full :=
  affinoidFullyFaithful.full

instance : (affinoidFunctor.{u, v, w} (K := K)).Faithful :=
  affinoidFullyFaithful.faithful

/-- The top spectrum homeomorphism intertwines the actual strong point map. -/
theorem topSpectrumHomeomorph_naturality (f : A ⟶ B)
    (x : BanachSpectrum (A.presentation.atlas.algebra A.topChart)) :
    B.topSpectrumHomeomorph (BanachSpectrum.comap (topPullback f).toBoundedRingHom x) =
      f.baseMap (A.topSpectrumHomeomorph x) :=
  f.chart_comm A.topChart B.topChart _ x

/-- Canonical actual singleton atlas, now in the strong-map category. -/
abbrev ofAffinoid (A : PresentedAffinoidSpace K) : TopChartPresentation.{u, u, 0} K where
  presentation := A.atlasPresentation
  topChart := PUnit.unit
  top_contains := A.atlasPresentation_top_contains

/-- The actual bounded morphism realizes a full strong singleton map. -/
def ofAffinoidMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    ofAffinoid A ⟶ ofAffinoid B :=
  PresentedAffinoidSpace.strongAtlasMap f

@[simp]
theorem topPullback_ofAffinoidMap {A B : PresentedAffinoidSpace K} (f : A ⟶ B) :
    topPullback (ofAffinoidMap f) = f.unop :=
  PresentedAffinoidSpace.strongAtlasMap_pullback f PUnit.unit _

/-- Singleton realization with full strong morphisms and the proved composition. -/
def singletonFunctor : PresentedAffinoidSpace K ⥤ TopChartPresentation.{u, u, 0} K where
  obj := ofAffinoid
  map := ofAffinoidMap
  map_id A := by
    apply topPullback_injective
    rw [topPullback_ofAffinoidMap, topPullback_id]
    rfl
  map_comp f g := by
    apply topPullback_injective
    rw [topPullback_ofAffinoidMap, topPullback_comp,
      topPullback_ofAffinoidMap, topPullback_ofAffinoidMap]
    rfl

/-- Singleton realization preserves exactly the actual spectrum functor. -/
theorem singletonFunctor_spaceFunctor :
    singletonFunctor (K := K) ⋙ spaceFunctor = affinoidSpectrumFunctor K := rfl

/-- Both directions are constructed strong maps with identity top-algebra maps. -/
def singletonComparisonIso (A : TopChartPresentation.{u, u, 0} K) :
    ofAffinoid A.affinoid ≅ A :=
  (affinoidFullyFaithful.{u, u, 0} (K := K)).preimageIso
    (X := ofAffinoid A.affinoid) (Y := A) (Iso.refl A.affinoid)

@[simp]
theorem topPullback_singletonComparisonIso_hom (A : TopChartPresentation.{u, u, 0} K) :
    topPullback A.singletonComparisonIso.hom =
      BoundedAlgHom.id K (A.presentation.atlas.algebra A.topChart) :=
  topPullback_ofTopPullback (A := ofAffinoid A.affinoid) (B := A) _

@[simp]
theorem topPullback_singletonComparisonIso_inv (A : TopChartPresentation.{u, u, 0} K) :
    topPullback A.singletonComparisonIso.inv =
      BoundedAlgHom.id K (A.presentation.atlas.algebra A.topChart) :=
  topPullback_ofTopPullback (A := A) (B := ofAffinoid A.affinoid) _

/-- The identity bounded comparisons are natural for every full strong morphism. -/
def singletonComparison :
    affinoidFunctor.{u, u, 0} (K := K) ⋙ singletonFunctor ≅
      𝟭 (TopChartPresentation.{u, u, 0} K) :=
  NatIso.ofComponents singletonComparisonIso (by
    intro A B f
    apply topPullback_injective
    change topPullback (ofAffinoidMap (affinoidFunctor.map f) ≫
      B.singletonComparisonIso.hom) =
        topPullback (A.singletonComparisonIso.hom ≫ f)
    exact (topPullback_comp _ _).trans
      ((congrArg₂ (fun φ ψ => φ.comp ψ)
        (topPullback_ofAffinoidMap (affinoidFunctor.map f))
        (topPullback_singletonComparisonIso_hom B)).trans
          ((BoundedAlgHom.comp_id _).trans
            ((BoundedAlgHom.id_comp _).symm.trans
              ((congrArg (fun φ => φ.comp (topPullback f))
                (topPullback_singletonComparisonIso_hom A).symm).trans
                  (topPullback_comp _ _).symm)))))

/-- Reading the greatest algebra after singleton realization gives the identity. -/
def affinoidSingletonComparison :
    singletonFunctor (K := K) ⋙ affinoidFunctor ≅ 𝟭 (PresentedAffinoidSpace K) :=
  NatIso.ofComponents (fun A => Iso.refl A) (by
    intro A B f
    apply Quiver.Hom.unop_inj
    change (topPullback (ofAffinoidMap f)).comp (BoundedAlgHom.id K B.unop) =
      (BoundedAlgHom.id K A.unop).comp f.unop
    exact (congrArg (fun φ => φ.comp (BoundedAlgHom.id K B.unop))
      (topPullback_ofAffinoidMap f)).trans
        ((BoundedAlgHom.comp_id _).trans (BoundedAlgHom.id_comp _).symm))

/-- Explicit actual affinoid equivalence in the singleton-compatible universes. -/
def affinoidEquivalence : TopChartPresentation.{u, u, 0} K ≌ PresentedAffinoidSpace K :=
  CategoryTheory.Equivalence.mk affinoidFunctor singletonFunctor singletonComparison.symm
    affinoidSingletonComparison

/-- The affinoid comparison also identifies the actual topological diagrams.
Space universe equals the algebra universe; the index universe is arbitrary. -/
def spaceComparison :
    affinoidFunctor.{u, u, w} (K := K) ⋙ affinoidSpectrumFunctor K ≅ spaceFunctor :=
  NatIso.ofComponents (fun A => TopCat.isoOfHomeo A.topSpectrumHomeomorph) (by
    intro A B f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact topSpectrumHomeomorph_naturality f)

end Langlands.Analytic.TopChartPresentation
