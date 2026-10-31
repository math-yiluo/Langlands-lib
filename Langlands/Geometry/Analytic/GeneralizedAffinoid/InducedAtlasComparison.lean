import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedEquivariantAtlas

/-! # Natural equivariant bounded atlas comparison for actual affinoid induction -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The actual family-to-quotient homeomorphism with bounded identity pullbacks. -/
def atlasComparisonHom (X : NormContinuousSpace K H) :
    (family H X.unop).atlasPresentation ⟶ atlasPresentation H hH X where
  baseMap := ⟨spectrumHomeomorph H X.unop hH,
    (spectrumHomeomorph H X.unop hH).continuous⟩
  indexMap := id
  index_mono c d h := by
    have he := DisjointAffinoidAtlas.chart_eq_of_subset (family H X.unop).algebra c d h
    subst d
    exact Set.Subset.rfl
  pullback _ := BoundedAlgHom.id K X.unop.obj.V
  chart_comm _ _ := rfl
  restriction_comm c d h := by
    have he := DisjointAffinoidAtlas.chart_eq_of_subset (family H X.unop).algebra c d h
    subst d
    rfl

/-- The inverse quotient-to-family map retains the same original chart algebras. -/
def atlasComparisonInv (X : NormContinuousSpace K H) :
    atlasPresentation H hH X ⟶ (family H X.unop).atlasPresentation where
  baseMap := ⟨(spectrumHomeomorph H X.unop hH).symm,
    (spectrumHomeomorph H X.unop hH).symm.continuous⟩
  indexMap := id
  index_mono c d h := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c d h
    subst d
    exact Set.Subset.rfl
  pullback _ := BoundedAlgHom.id K X.unop.obj.V
  chart_comm c x := (spectrumHomeomorph H X.unop hH).symm_apply_apply
    (DisjointAffinoidAtlas.chart (family H X.unop).algebra c x) |>.symm
  restriction_comm c d h := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c d h
    subst d
    rfl

@[simp]
theorem atlasComparisonHom_indexMap (X : NormContinuousSpace K H) :
    (atlasComparisonHom H hH X).indexMap = id := rfl

@[simp]
theorem atlasComparisonInv_indexMap (X : NormContinuousSpace K H) :
    (atlasComparisonInv H hH X).indexMap = id := rfl

@[simp]
theorem atlasComparisonHom_pullback (X : NormContinuousSpace K H)
    (c : (family H X.unop).atlas.Index) :
    (atlasComparisonHom H hH X).pullback c = BoundedAlgHom.id K X.unop.obj.V := rfl

@[simp]
theorem atlasComparisonInv_pullback (X : NormContinuousSpace K H)
    (c : (atlas H X.unop hH).Index) :
    (atlasComparisonInv H hH X).pullback c = BoundedAlgHom.id K X.unop.obj.V := rfl

@[simp]
theorem atlasComparisonHom_inv (X : NormContinuousSpace K H) :
    atlasComparisonHom H hH X ≫ atlasComparisonInv H hH X =
      𝟙 (family H X.unop).atlasPresentation :=
  AffinoidAtlasPresentation.Hom.ext
    (ContinuousMap.ext (spectrumHomeomorph H X.unop hH).symm_apply_apply)
    rfl (heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl))

@[simp]
theorem atlasComparisonInv_hom (X : NormContinuousSpace K H) :
    atlasComparisonInv H hH X ≫ atlasComparisonHom H hH X =
      𝟙 (atlasPresentation H hH X) :=
  AffinoidAtlasPresentation.Hom.ext
    (ContinuousMap.ext (spectrumHomeomorph H X.unop hH).apply_symm_apply)
    rfl (heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl))

/-- An isomorphism of actual chosen atlas presentations, including bounded data. -/
def atlasComparisonIso (X : NormContinuousSpace K H) :
    (family H X.unop).atlasPresentation ≅ atlasPresentation H hH X where
  hom := atlasComparisonHom H hH X
  inv := atlasComparisonInv H hH X
  hom_inv_id := atlasComparisonHom_inv H hH X
  inv_hom_id := atlasComparisonInv_hom H hH X

/-- The comparison intertwines the entire bounded atlas action maps. -/
theorem atlasComparisonHom_equivariant (X : NormContinuousSpace K H) (g : G) :
    (actionMap H X.unop g).atlasMap ≫ atlasComparisonHom H hH X =
      atlasComparisonHom H hH X ≫ atlasActionMap H hH X g := by
  apply AffinoidAtlasPresentation.Hom.ext
    (f := (actionMap H X.unop g).atlasMap ≫ atlasComparisonHom H hH X)
    (g := atlasComparisonHom H hH X ≫ atlasActionMap H hH X g)
    (ContinuousMap.ext fun p => (actionMap_realization H X.unop hH g p).symm)
    rfl
  exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)

/-- Equivariant atlas presentations of the family and balanced quotient agree. -/
def equivariantAtlasComparisonIso (X : NormContinuousSpace K H) :
    ((AffinoidFamily.atlasFunctor (K := K)).mapAction G).obj (action H X.unop) ≅
      atlasAction H hH X :=
  Action.mkIso (atlasComparisonIso H hH X) (atlasComparisonHom_equivariant H hH X)

/-- Naturality holds as equality of complete bounded chosen atlas morphisms. -/
theorem atlasComparisonHom_naturality {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    (familyMap H f).atlasMap ≫ atlasComparisonHom H hH Y =
      atlasComparisonHom H hH X ≫ atlasMap H hH f := by
  apply AffinoidAtlasPresentation.Hom.ext
    (f := (familyMap H f).atlasMap ≫ atlasComparisonHom H hH Y)
    (g := atlasComparisonHom H hH X ≫ atlasMap H hH f)
    (ContinuousMap.ext fun p => spectrumHomeomorph_naturality H hH f p)
    rfl
  exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)

/-- Bounded coset-family realization and the original quotient-atlas induction
are naturally isomorphic as functors into full-group atlas actions. -/
def equivariantAtlasComparison :
    functor H ⋙ (AffinoidFamily.atlasFunctor (K := K)).mapAction G ≅
      equivariantAtlasFunctor H hH :=
  NatIso.ofComponents (equivariantAtlasComparisonIso H hH)
    (fun f => Action.Hom.ext (atlasComparisonHom_naturality H hH f))

/-- The forward continuous map is exactly the existing topological comparison. -/
@[simp]
theorem equivariantAtlasComparison_hom_baseMap (X : NormContinuousSpace K H) :
    ((equivariantAtlasComparison H hH).hom.app X).hom.baseMap =
      ((spectrumComparison H hH).hom.app X).hom.hom.hom := rfl

/-- The inverse continuous map is exactly the inverse topological comparison. -/
@[simp]
theorem equivariantAtlasComparison_inv_baseMap (X : NormContinuousSpace K H) :
    ((equivariantAtlasComparison H hH).inv.app X).hom.baseMap =
      ((spectrumComparison H hH).inv.app X).hom.hom.hom := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
