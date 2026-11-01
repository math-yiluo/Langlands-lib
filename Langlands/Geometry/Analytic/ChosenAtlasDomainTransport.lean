import Langlands.Geometry.Analytic.OriginalDomainTopology
import Langlands.Geometry.Analytic.AtlasTopology.Homeomorph
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Original-domain transport by actual chosen atlas isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- The actual base homeomorphism of an isomorphism of chosen atlas maps. -/
def isoHomeomorph (e : A ≅ B) : A.space ≃ₜ B.space :=
  TopCat.homeoOfIso (spaceFunctor.mapIso e)

@[simp]
theorem isoHomeomorph_apply (e : A ≅ B) (x : A.space) :
    isoHomeomorph e x = e.hom.baseMap x := rfl

@[simp]
theorem isoHomeomorph_symm_apply (e : A ≅ B) (y : B.space) :
    (isoHomeomorph e).symm y = e.inv.baseMap y := rfl

@[simp]
theorem isoHomeomorph_symm (e : A ≅ B) :
    isoHomeomorph e.symm = (isoHomeomorph e).symm := rfl

theorem iso_hom_inv_indexMap (e : A ≅ B) (i : A.atlas.Index) :
    e.inv.indexMap (e.hom.indexMap i) = i :=
  congrArg (fun f : A ⟶ A => f.indexMap i) e.hom_inv_id

theorem iso_inv_hom_indexMap (e : A ≅ B) (j : B.atlas.Index) :
    e.hom.indexMap (e.inv.indexMap j) = j :=
  congrArg (fun f : B ⟶ B => f.indexMap j) e.inv_hom_id

/-- The full chosen inverse laws yield an equivalence of chart indices. -/
def isoIndexEquiv (e : A ≅ B) : A.atlas.Index ≃ B.atlas.Index where
  toFun := e.hom.indexMap
  invFun := e.inv.indexMap
  left_inv := iso_hom_inv_indexMap e
  right_inv := iso_inv_hom_indexMap e

/-- A chosen atlas isomorphism sends a whole source chart onto its chosen target. -/
theorem isoHomeomorph_image_chart (e : A ≅ B) (i : A.atlas.Index) :
    isoHomeomorph e '' Set.range (A.atlas.chart i) =
      Set.range (B.atlas.chart (e.hom.indexMap i)) := by
  apply Subset.antisymm (e.hom.image_chart_subset i)
  intro y hy
  have hx := e.inv.image_chart_subset (e.hom.indexMap i) ⟨y, hy, rfl⟩
  rw [iso_hom_inv_indexMap] at hx
  exact ⟨e.inv.baseMap y, hx, (isoHomeomorph e).apply_symm_apply y⟩

/-- The actual target chart family is the image of the actual source family. -/
theorem isoHomeomorph_image_chartFamily (e : A ≅ B) :
    AtlasTopology.imageFamily (isoHomeomorph e)
      (Set.range (fun i => Set.range (A.atlas.chart i))) =
        Set.range (fun j => Set.range (B.atlas.chart j)) := by
  ext U
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨e.hom.indexMap i, (isoHomeomorph_image_chart e i).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨_, ⟨e.inv.indexMap j, rfl⟩, ?_⟩
    change isoHomeomorph e '' Set.range (A.atlas.chart (e.inv.indexMap j)) =
      Set.range (B.atlas.chart j)
    rw [isoHomeomorph_image_chart, iso_inv_hom_indexMap]

/-- Transport the contained-original-chart quasinet to the actual image subspace. -/
theorem isoHomeomorph_isOriginalChartDomain (e : A ≅ B) {S : Set A.space}
    (hS : A.atlas.IsOriginalChartDomain S) :
    B.atlas.IsOriginalChartDomain (isoHomeomorph e '' S) := by
  have h := AtlasTopology.IsQuasinet.imageFamily_restricted hS (isoHomeomorph e)
  rwa [isoHomeomorph_image_chartFamily] at h

theorem isoHomeomorph_isOriginalChartDomain_iff (e : A ≅ B) (S : Set A.space) :
    B.atlas.IsOriginalChartDomain (isoHomeomorph e '' S) ↔
      A.atlas.IsOriginalChartDomain S := by
  constructor
  · intro h
    have h' := isoHomeomorph_isOriginalChartDomain e.symm h
    exact (congrArg A.atlas.IsOriginalChartDomain
      ((isoHomeomorph e).toEquiv.symm_image_image S)).mp h'
  · exact isoHomeomorph_isOriginalChartDomain e

/-- The actual image domain, with its domain condition constructed. -/
def isoOriginalDomain (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    B.atlas.OriginalChartDomain :=
  ⟨isoHomeomorph e '' (S : Set A.space), isoHomeomorph_isOriginalChartDomain e S.is_domain⟩

@[simp]
theorem coe_isoOriginalDomain (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    (isoOriginalDomain e S : Set B.space) = isoHomeomorph e '' (S : Set A.space) := rfl

/-- Actual image and inverse image give an order isomorphism of original domains. -/
def isoOriginalDomainOrderIso (e : A ≅ B) :
    A.atlas.OriginalChartDomain ≃o B.atlas.OriginalChartDomain where
  toFun := isoOriginalDomain e
  invFun := isoOriginalDomain e.symm
  left_inv S := by
    apply SetLike.coe_injective
    exact (isoHomeomorph e).toEquiv.symm_image_image (S : Set A.space)
  right_inv T := by
    apply SetLike.coe_injective
    exact (isoHomeomorph e).toEquiv.image_symm_image (T : Set B.space)
  map_rel_iff' := by
    intro S T
    change isoHomeomorph e '' (S : Set A.space) ⊆
      isoHomeomorph e '' (T : Set A.space) ↔ (S : Set A.space) ⊆ T
    exact Set.image_subset_image_iff (isoHomeomorph e).injective

@[simp]
theorem isoOriginalDomainOrderIso_apply (e : A ≅ B) (S : A.atlas.OriginalChartDomain) :
    isoOriginalDomainOrderIso e S = isoOriginalDomain e S := rfl

@[simp]
theorem isoOriginalDomainOrderIso_symm_apply (e : A ≅ B)
    (T : B.atlas.OriginalChartDomain) :
    (isoOriginalDomainOrderIso e).symm T = isoOriginalDomain e.symm T := rfl

@[simp]
theorem isoOriginalDomain_ofChart (e : A ≅ B) (i : A.atlas.Index) :
    isoOriginalDomain e (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i) =
      IndexedAffinoidAtlas.OriginalChartDomain.ofChart (e.hom.indexMap i) := by
  apply SetLike.coe_injective
  exact isoHomeomorph_image_chart e i

/-- The induced equivalence uses literal images on objects and inclusions on arrows. -/
def isoOriginalDomainEquivalence (e : A ≅ B) :
    A.atlas.OriginalChartDomain ≌ B.atlas.OriginalChartDomain :=
  (isoOriginalDomainOrderIso e).equivalence

/-- The family of actual transported domains is the image of their original family. -/
theorem isoOriginalDomain_imageFamily (e : A ≅ B) {ι : Type*}
    (D : ι → A.atlas.OriginalChartDomain) :
    AtlasTopology.imageFamily (isoHomeomorph e) (Set.range (fun i => (D i : Set A.space))) =
      Set.range (fun i => (isoOriginalDomain e (D i) : Set B.space)) := by
  ext U
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D i, ⟨i, rfl⟩, rfl⟩

open IndexedAffinoidAtlas.OriginalChartDomain

/-- Arbitrary quasinet covering families are preserved and reflected. -/
theorem isoOriginalDomain_ofArrows_mem_iff (e : A ≅ B)
    {S : A.atlas.OriginalChartDomain} {ι : Type*}
    (D : ι → A.atlas.OriginalChartDomain) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows (fun i => isoOriginalDomain e (D i))
        (fun i => (isoOriginalDomainEquivalence e).functor.map (f i)) ∈
          quasinetTopology B.atlas (isoOriginalDomain e S) ↔
      Sieve.ofArrows D f ∈ quasinetTopology A.atlas S := by
  refine (ofArrows_mem_iff_isQuasinet (a := B.atlas) (S := isoOriginalDomain e S)
    (fun i => isoOriginalDomain e (D i))
    (fun i => (isoOriginalDomainEquivalence e).functor.map (f i))).trans ?_
  rw [ofArrows_mem_iff_isQuasinet D f]
  rw [← isoOriginalDomain_imageFamily]
  change AtlasTopology.IsQuasinet
    (AtlasTopology.restrictedFamily
      (AtlasTopology.imageFamily (isoHomeomorph e) (Set.range (fun i => (D i : Set A.space))))
      (isoHomeomorph e '' (S : Set A.space))) ↔ _
  rw [← AtlasTopology.imageFamily_restrictedFamily]
  exact AtlasTopology.isQuasinet_imageFamily_iff _ _

/-- The full sieve pushforward preserves and reflects the existing topology. -/
theorem isoOriginalDomain_functorPushforward_mem_iff (e : A ≅ B)
    {S : A.atlas.OriginalChartDomain} (R : Sieve S) :
    R.functorPushforward (isoOriginalDomainEquivalence e).functor ∈
        quasinetTopology B.atlas ((isoOriginalDomainEquivalence e).functor.obj S) ↔
      R ∈ quasinetTopology A.atlas S := by
  obtain ⟨ι, D, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows]
  exact isoOriginalDomain_ofArrows_mem_iff e D f

/-- The full sieve pullback preserves and reflects the existing topology. -/
theorem isoOriginalDomain_functorPullback_mem_iff (e : A ≅ B)
    {S : A.atlas.OriginalChartDomain}
    (R : Sieve ((isoOriginalDomainEquivalence e).functor.obj S)) :
    R.functorPullback (isoOriginalDomainEquivalence e).functor ∈ quasinetTopology A.atlas S ↔
      R ∈ quasinetTopology B.atlas ((isoOriginalDomainEquivalence e).functor.obj S) := by
  have h := isoOriginalDomain_functorPushforward_mem_iff e
    (R.functorPullback (isoOriginalDomainEquivalence e).functor)
  rw [(Sieve.essSurjFullFunctorGaloisInsertion
    (isoOriginalDomainEquivalence e).functor S).l_u_eq R] at h
  exact h.symm

/-- The actual image functor preserves every covering sieve. -/
theorem isoOriginalDomain_coverPreserving (e : A ≅ B) :
    CoverPreserving (quasinetTopology A.atlas) (quasinetTopology B.atlas)
      (isoOriginalDomainEquivalence e).functor where
  cover_preserve h := (isoOriginalDomain_functorPushforward_mem_iff e _).mpr h

/-- The actual image functor lifts every covering sieve by its functorial pullback. -/
instance isoOriginalDomain_isCocontinuous (e : A ≅ B) :
    (isoOriginalDomainEquivalence e).functor.IsCocontinuous
      (quasinetTopology A.atlas) (quasinetTopology B.atlas) where
  cover_lift h := (isoOriginalDomain_functorPullback_mem_iff e _).mpr h

/-- Precomposition by the actual image functor carries sheaves to sheaves. -/
instance isoOriginalDomain_isContinuous (e : A ≅ B) :
    (isoOriginalDomainEquivalence e).functor.IsContinuous
      (quasinetTopology A.atlas) (quasinetTopology B.atlas) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (isoOriginalDomain_coverPreserving e)

end Langlands.Analytic.AffinoidAtlasPresentation
