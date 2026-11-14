import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourcePointDimension
import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointManifold

/-! # Actual algebraic dimension pieces of an arbitrary smooth space -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces

variable {K : Type u} [Field K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : SmoothOverBase X)

/-- The full ordinary-point locus of dimension `n`, including empty loci. -/
def subset (n : ℕ) : Set (Points X.presheaf) := pointDimension hX ⁻¹' {n}

theorem subset_isOpen (n : ℕ) :
    IsOpen[pointTopology X.presheaf] (subset hX n) :=
  pointDimension_isLocallyConstant hX {n}

theorem subset_isClosed (n : ℕ) :
    IsClosed[pointTopology X.presheaf] (subset hX n) := by
  let := pointTopology X.presheaf
  rw [← isOpen_compl_iff]
  exact pointDimension_isLocallyConstant hX {n}ᶜ

/-- The genuine algebraic open subspace of dimension `n`. -/
def space (n : ℕ) : AlgebraicSpace (Spec (CommRingCat.of K)) :=
  PointOpenSubspace.space X (subset hX n) (subset_isOpen hX n)

/-- The actual morphism from the dimension piece into the original space. -/
def inclusion (n : ℕ) : space hX n ⟶ X :=
  PointOpenSubspace.inclusion X (subset hX n) (subset_isOpen hX n)

theorem inclusion_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (hom (inclusion hX n)) :=
  PointOpenSubspace.isOpenImmersion_subfunctor X _ (subset_isOpen hX n)

theorem range_inclusion (n : ℕ) :
    Set.range (Points.map (hom (inclusion hX n))) = subset hX n :=
  PointOpenSubspace.range_points X.presheaf _

theorem cover (p : Points X.presheaf) :
    ∃ n : ℕ, p ∈ Set.range (Points.map (hom (inclusion hX n))) := by
  refine ⟨pointDimension hX p, ?_⟩
  rw [range_inclusion]
  rfl

theorem disjoint {n m : ℕ} (h : n ≠ m) :
    Disjoint (Set.range (Points.map (hom (inclusion hX n))))
      (Set.range (Points.map (hom (inclusion hX m)))) := by
  rw [range_inclusion, range_inclusion]
  apply Set.disjoint_left.mpr
  intro p hn hm
  exact h (hn.symm.trans hm)

/-- The actual open restriction of the chosen smooth scheme atlas. -/
abbrev restrictedAtlas (n : ℕ) : Over (Spec (CommRingCat.of K)) :=
  PointOpenSubspace.chartScheme X (subset hX n) (subset_isOpen hX n) (atlasMap hX)

def restrictedAtlasInclusion (n : ℕ) : restrictedAtlas hX n ⟶ atlas hX :=
  PointOpenSubspace.chartInclusion X (subset hX n) (subset_isOpen hX n) (atlasMap hX)

instance restrictedAtlasInclusion_isOpenImmersion (n : ℕ) :
    _root_.AlgebraicGeometry.IsOpenImmersion (restrictedAtlasInclusion hX n).left :=
  PointOpenSubspace.chartInclusion_isOpenImmersion X _ (subset_isOpen hX n) (atlasMap hX)

theorem restrictedAtlas_factors (n : ℕ) :
    Subfunctor.range ((schemeYoneda _).map (restrictedAtlasInclusion hX n) ≫ atlasMap hX) ≤
      PointOpenSubspace.subfunctor X.presheaf (subset hX n) := by
  rw [Subfunctor.range_comp, Subfunctor.image_le_iff, restrictedAtlasInclusion,
    PointOpenSubspace.range_chartInclusion X _ (subset_isOpen hX n) (atlasMap hX)]

/-- The actual restricted atlas map, obtained by represented-open factorization. -/
def restrictedAtlasMap (n : ℕ) :
    (schemeYoneda _).obj (restrictedAtlas hX n) ⟶ (space hX n).presheaf :=
  Subfunctor.lift _ (restrictedAtlas_factors hX n)

theorem restrictedAtlas_comm (n : ℕ) :
    restrictedAtlasMap hX n ≫ hom (inclusion hX n) =
      (schemeYoneda _).map (restrictedAtlasInclusion hX n) ≫ atlasMap hX :=
  Subfunctor.lift_ι _ (restrictedAtlas_factors hX n)

/-- The restricted atlas is the actual base change of the original atlas. -/
theorem restrictedAtlas_isPullback (n : ℕ) :
    IsPullback (restrictedAtlasMap hX n)
      ((schemeYoneda _).map (restrictedAtlasInclusion hX n))
      (hom (inclusion hX n)) (atlasMap hX) := by
  let j := restrictedAtlasInclusion hX n
  let : Mono j := Over.mono_of_mono_left j
  exact OpenSubfunctorLifting.isPullback_subfunctor_of_range
    (PointOpenSubspace.subfunctor X.presheaf (subset hX n))
    (restrictedAtlasMap hX n) ((schemeYoneda _).map j) (atlasMap hX)
    (restrictedAtlas_comm hX n)
    (PointOpenSubspace.range_chartInclusion X _ (subset_isOpen hX n) (atlasMap hX))

theorem restrictedAtlasMap_isEtale (n : ℕ) : IsEtale (restrictedAtlasMap hX n) := by
  let := MorphismProperty.relative_isStableUnderBaseChange
    (F := schemeYoneda (Spec (CommRingCat.of K)))
    (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget _))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget _)).relative
      (schemeYoneda _))
    (restrictedAtlas_isPullback hX n).flip (atlasMap_isEtale hX)

theorem restrictedAtlasMap_isSurjective (n : ℕ) :
    IsSurjective (restrictedAtlasMap hX n) := by
  let := MorphismProperty.relative_isStableUnderBaseChange
    (F := schemeYoneda (Spec (CommRingCat.of K)))
    (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget _))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget _)).relative
      (schemeYoneda _))
    (restrictedAtlas_isPullback hX n).flip (atlasMap_isSurjective hX)

theorem restrictedAtlas_smooth (n : ℕ) : Smooth (restrictedAtlas hX n).hom := by
  let := atlas_smooth hX
  change Smooth (_ ≫ (atlas hX).hom)
  infer_instance

instance restrictedAtlas_isLocallyNoetherian (n : ℕ) :
    IsLocallyNoetherian (restrictedAtlas hX n).left := by
  let := restrictedAtlas_smooth hX n
  exact LocallyOfFiniteType.isLocallyNoetherian (restrictedAtlas hX n).hom

/-- The local structural dimension of the actual restricted atlas is `n`. -/
theorem restrictedAtlas_localDimension (n : ℕ) (x : (restrictedAtlas hX n).left) :
    relativeTopologicalKrullDimAt (restrictedAtlas hX n).hom x = (n : WithBot ℕ∞) := by
  have hx : Points.map (hom (inclusion hX n))
      (chartPointMap (restrictedAtlasMap hX n) x) ∈ subset hX n := by
    rw [← range_inclusion]
    exact ⟨_, rfl⟩
  have ha : IsEtale (restrictedAtlasMap hX n ≫ hom (inclusion hX n)) :=
    (restrictedAtlasMap_isEtale hX n).comp
      (PointOpenSubspace.isEtale_of_isOpenImmersion (inclusion_isOpenImmersion hX n))
  have he := pointDimension_chart hX
    (restrictedAtlasMap hX n ≫ hom (inclusion hX n)) ha x
  change pointDimension hX
    (Points.map (hom (inclusion hX n)) (chartPointMap (restrictedAtlasMap hX n) x)) = n at hx
  simp only [chartPointMap, Function.comp_apply] at hx
  simpa only [chartPointMap, Function.comp_apply, Points.map_comp, hx] using he.symm

/-- This holds for every natural index, even when the restricted atlas is empty. -/
theorem restrictedAtlas_smoothOfRelativeDimension (n : ℕ) :
    SmoothOfRelativeDimension n (restrictedAtlas hX n).hom :=
  smoothOfRelativeDimension_of_localDimension _ (restrictedAtlas_smooth hX n) n
    (restrictedAtlas_localDimension hX n)

theorem space_hasAtlasProperty (n : ℕ) :
    HasAtlasProperty (@SmoothOfRelativeDimension.{u} n) (space hX n) :=
  ⟨restrictedAtlas hX n, restrictedAtlasMap hX n, restrictedAtlasMap_isEtale hX n,
    restrictedAtlasMap_isSurjective hX n, restrictedAtlas_smoothOfRelativeDimension hX n⟩

theorem space_smoothOverBase (n : ℕ) : SmoothOverBase (space hX n) :=
  ⟨restrictedAtlas hX n, restrictedAtlasMap hX n, restrictedAtlasMap_isEtale hX n,
    restrictedAtlasMap_isSurjective hX n, restrictedAtlas_smooth hX n⟩

theorem space_isQuasiSeparated (hqs : IsQuasiSeparated X) (n : ℕ) :
    IsQuasiSeparated (space hX n) :=
  OpenSubspaceGeometry.isQuasiSeparated_openSubspace hqs
    (PointOpenSubspace.subfunctor X.presheaf (subset hX n))
    (inclusion_isOpenImmersion hX n)

theorem space_isLocallySeparated (hls : IsLocallySeparated X) (n : ℕ) :
    IsLocallySeparated (space hX n) := by
  let := MorphismProperty.relative_isStableUnderBaseChange
    (F := schemeYoneda (Spec (CommRingCat.of K)))
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u})
      (Over.forget _))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsImmersion.{u})
      (Over.forget _)).relative (schemeYoneda _))
    (OpenSubfunctorImages.diag_isPullback_of_mono
      (PointOpenSubspace.subfunctor X.presheaf (subset hX n)).ι) hls

section Normed

variable {K : Type u} [NontriviallyNormedField K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : SmoothOverBase X)

/-- With the separately supplied separation hypotheses, every piece belongs to
the existing pure-dimensional analytic interface. -/
theorem space_isSmoothPureDimensional (hqs : IsQuasiSeparated X)
    (hls : IsLocallySeparated X) (n : ℕ) :
    IsSmoothPureDimensional K n (space hX n) :=
  ⟨⟨⟨space_isQuasiSeparated hX hqs n,
      (space_smoothOverBase hX n).locallyOfFiniteType⟩,
    space_isLocallySeparated hX hls n⟩, space_hasAtlasProperty hX n⟩

end Normed

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionPieces
