import Langlands.Geometry.Analytic.OriginalDomainCompactCover
import Langlands.Geometry.Analytic.StrongChartReconstruction
import Langlands.Geometry.Analytic.SaturatedDomainQuotientSeparation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing

/-! # Complete bounded-map separation on refining original source charts -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Actual selected original charts forming a finite cover of one original
chart. Their algebras and bounded restrictions are unchanged. -/
structure FiniteSelectedChartCover (P : a.Index → Prop) (i : a.Index) where
  size : ℕ
  index : Fin size → a.Index
  selected : ∀ t, P (index t)
  subset : ∀ t, Set.range (a.chart (index t)) ⊆ Set.range (a.chart i)
  covers : ∀ x ∈ Set.range (a.chart i), ∃ t, x ∈ Set.range (a.chart (index t))

/-- Compactness collects the finite relative neighborhood witnesses into
an actual finite cover of each original affinoid chart. -/
def finiteSelectedChartCover (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (i : a.Index) :
    a.FiniteSelectedChartCover P i := by
  classical
  apply Classical.choice
  have h : AtlasTopology.LocallyRefines (a.selectedChartFamily P)
      {Set.range (a.chart i)} :=
    AtlasTopology.LocallyRefines.mono hP Subset.rfl
      (singleton_subset_iff.mpr (Set.mem_range_self i))
  obtain ⟨I, hI⟩ := h.exists_finset_cover
    (isCompact_range (a.isEmbedding_chart i).continuous)
  let e := (Fintype.equivFin {j // j ∈ I}).symm
  refine ⟨⟨Fintype.card {j // j ∈ I}, fun t => (e t).val.val,
    fun t => (e t).val.property, ?_, ?_⟩⟩
  · intro t x hx
    rw [← hI]
    exact mem_iUnion₂.mpr ⟨(e t).val, (e t).property, hx⟩
  · intro x hx
    have hx' : x ∈ ⋃ j ∈ I, Set.range (a.chart j.val) := hI.symm ▸ hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx'
    refine ⟨e.symm ⟨j, hj⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact hxj

namespace FiniteSelectedChartCover

variable {a} {P : a.Index → Prop} {i : a.Index}

/-- The original bounded restrictions form a finite full-domain cover of
the whole stored algebra of the original chart. -/
def domainCover (c : a.FiniteSelectedChartCover P i) :
    Domain.FiniteCover (Domain.whole K (a.algebra i)) where
  size := c.size
  obj t := a.restrictionDomain (c.index t) i (c.subset t)
  map t := ⟨a.restriction (c.index t) i (c.subset t), BoundedAlgHom.comp_id _⟩
  covers x _ := c.covers (a.chart i x) ⟨x, rfl⟩

@[simp]
theorem domainCover_map_restriction (c : a.FiniteSelectedChartCover P i)
    (t : Fin c.size) :
    (c.domainCover.map t).restriction = a.restriction (c.index t) i (c.subset t) := rfl

end FiniteSelectedChartCover

/-- Refining selected original-chart restrictions detect equality of
stored algebra elements, including information invisible on spectrum points. -/
theorem algebra_ext_of_refiningSelection (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (i : a.Index) {s t : a.algebra i}
    (h : ∀ j, P j → ∀ hji : Set.range (a.chart j) ⊆ Set.range (a.chart i),
      a.restriction j i hji s = a.restriction j i hji t) : s = t := by
  let c := a.finiteSelectedChartCover P hP i
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro k
  exact h (c.index k) (c.selected k) (c.subset k)

/-- Refining selected restrictions also detect complete bounded algebra
maps from any normed coefficient algebra. -/
theorem boundedAlgHom_ext_of_refiningSelection (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (i : a.Index)
    {R : Type z} [NormedCommRing R] [NormedAlgebra K R]
    {φ ψ : BoundedAlgHom K R (a.algebra i)}
    (h : ∀ j, P j → ∀ hji : Set.range (a.chart j) ⊆ Set.range (a.chart i),
      (a.restriction j i hji).comp φ = (a.restriction j i hji).comp ψ) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro r
  apply a.algebra_ext_of_refiningSelection P hP i
  intro j hj hji
  exact congrArg (fun f : BoundedAlgHom K R (a.algebra j) => f r) (h j hj hji)

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Restriction to any locally refining selection of original source charts
is injective on full strong maps. No downward closure or saturation is needed. -/
theorem restrictSubatlasSource_injective (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    Function.Injective (fun f : StrongHom A B => f.restrictSubatlasSource P hP) := by
  intro f g heq
  refine ext_of_pullback
    (congrArg (fun q : StrongHom (A.subpresentation P hP) B => q.baseMap) heq) ?_
  intro i j hf hg
  apply A.atlas.boundedAlgHom_ext_of_refiningSelection P hP i
  intro k hk hki
  have hfk : f.baseMap '' Set.range (A.atlas.chart k) ⊆
      Set.range (B.atlas.chart j) := (Set.image_mono hki).trans hf
  have hgk : g.baseMap '' Set.range (A.atlas.chart k) ⊆
      Set.range (B.atlas.chart j) := (Set.image_mono hki).trans hg
  have hlocal := pullback_congr heq ⟨k, hk⟩ j hfk hgk
  have hfr := f.restriction_comm k i j j hki Subset.rfl hfk hf
  have hgr := g.restriction_comm k i j j hki Subset.rfl hgk hg
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id] at hfr hgr
  exact hfr.trans (hlocal.trans hgr.symm)

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation.SourceCategory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Equality of two original strong maps in the actual source quotient is
already equality of all their original bounded pullbacks. -/
theorem strongFunctor_map_injective :
    Function.Injective (fun f : A ⟶ B => strongFunctor.map f) := by
  intro f g h
  obtain ⟨P, hP⟩ := (strongFunctor_map_eq_iff_exists_refiningRestriction f g).mp h
  exact AffinoidAtlasPresentation.StrongHom.restrictSubatlasSource_injective
    P.carrier P.locally_refining hP

/-- The constructed original strong-map functor is faithful by actual
finite full-domain algebra separation, rather than by point-map faithfulness. -/
instance strongFunctor_faithful : (strongFunctor (K := K) :
    SaturatedAtlasPresentation.{u, v, w} K ⥤ _).Faithful where
  map_injective := by
    intro X Y f g h
    exact strongFunctor_map_injective h

/-- An actual embedding of the complete original strong Hom type into the
source quotient Hom type. It need not be surjective. -/
def strongHomEmbedding : (A ⟶ B) ↪ (ofPresentation A ⟶ ofPresentation B) where
  toFun := strongFunctor.map
  inj' := strongFunctor_map_injective

end SaturatedAtlasPresentation.SourceCategory
end Langlands.Analytic
