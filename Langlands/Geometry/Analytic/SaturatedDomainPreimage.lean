import Langlands.Geometry.Analytic.SaturatedDomainCorestriction
import Langlands.Geometry.Analytic.OriginalDomainRefinement
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Actual inverse-image domains and pullback squares -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory CategoryTheory.Limits Set Filter Topology
open PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Original source charts refine the intersection of one source chart
with the inverse image of an actual target domain. -/
theorem originalCharts_refine_domainPreimage_chart (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (S : B.atlas.OriginalChartDomain)
    (i : A.atlas.Index) :
    AtlasTopology.LocallyRefines (Set.range (fun k => Set.range (A.atlas.chart k)))
      {Set.range (A.atlas.chart i) ∩ f.baseMap ⁻¹' S.carrier} := by
  classical
  rintro _ ⟨rfl⟩ x hx
  obtain ⟨j, hj⟩ := f.target_exists i
  have hSj := S.is_domain.inter B.atlas (B.atlas.isOriginalChartDomain_chart j)
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hSj
      _ (Set.mem_singleton _) (f.baseMap x) ⟨hx.2, hj ⟨x, hx.1, rfl⟩⟩
  let T : Set A.space := Set.range (A.atlas.chart i)
  let δ : Set (Set A.space) := (fun V => T ∩ f.baseMap ⁻¹' V) '' σ
  have hδ : ⋃₀ δ = T ∩ f.baseMap ⁻¹' ⋃₀ σ := by
    ext y
    constructor
    · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
      exact ⟨hy.1, V, hV, hy.2⟩
    · rintro ⟨hyT, V, hV, hyV⟩
      exact ⟨_, ⟨V, hV, rfl⟩, hyT, hyV⟩
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨k, hk⟩ := hs hV
    change Set.range (B.atlas.chart k) = V at hk
    have hkj : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j) := by
      rw [hk]
      exact (hm V hV).1.trans Set.inter_subset_right
    let U : LocalDomain A.atlas := ⟨i, Domain.whole K (A.atlas.algebra i)⟩
    have hU : U.locus = T := Set.image_univ
    have hlocal : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j) := hU ▸ hj
    exact ⟨f.inverseImageOriginalChart ha U j hlocal k hkj,
      (f.range_inverseImageOriginalChart ha U j hlocal k hkj).trans (by rw [hU, hk])⟩
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨fun y hy => ⟨hy.1, (hm V hV).1 hy.2 |>.1⟩, hx.1, (hm V hV).2⟩
  · rw [hδ]
    have hc : Tendsto f.baseMap (𝓝[T ∩ f.baseMap ⁻¹' S.carrier] x)
        (𝓝[S.carrier ∩ Set.range (B.atlas.chart j)] (f.baseMap x)) :=
      f.baseMap.continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun y hy => ⟨hy.2, hj ⟨y, hy.1, rfl⟩⟩)
    exact Filter.inter_mem
      (Filter.mem_of_superset self_mem_nhdsWithin Set.inter_subset_left) (hc hn)

/-- Full inverse-image domains and source saturation prove the global
finite relative neighborhood condition. -/
theorem isOriginalChartDomain_preimage (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (S : B.atlas.OriginalChartDomain) :
    A.atlas.IsOriginalChartDomain (f.baseMap ⁻¹' S.carrier) := by
  classical
  let κ : Set (Set A.space) := Set.range
    (fun i => Set.range (A.atlas.chart i) ∩ f.baseMap ⁻¹' S.carrier)
  have hκ : AtlasTopology.LocallyRefines κ {f.baseMap ⁻¹' S.carrier} := by
    rintro _ ⟨rfl⟩ x hx
    obtain ⟨σ, hf, hs, hm, hn⟩ := A.atlas.isNet_chartFamily.1 x
    let δ : Set (Set A.space) := (fun V => V ∩ f.baseMap ⁻¹' S.carrier) '' σ
    refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨i, rfl⟩ := hs hV
      exact ⟨i, rfl⟩
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨Set.inter_subset_right, hm V hV, hx⟩
    · have hδ : ⋃₀ δ = (⋃₀ σ) ∩ f.baseMap ⁻¹' S.carrier := by
        ext y
        constructor
        · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
          exact ⟨⟨V, hV, hy.1⟩, hy.2⟩
        · rintro ⟨⟨V, hV, hyV⟩, hyS⟩
          exact ⟨_, ⟨V, hV, rfl⟩, hyV, hyS⟩
      rw [hδ]
      exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hn) self_mem_nhdsWithin
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  apply hκ.trans
  rintro _ ⟨i, rfl⟩ x hx
  exact f.originalCharts_refine_domainPreimage_chart ha S i _ (Set.mem_singleton _) x hx

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation.SourceCategory

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Inverse-image domains descend to arbitrary source-quotient arrows.
Deleting a locally redundant source atlas does not change the domain predicate. -/
theorem isOriginalChartDomain_preimage
    (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    A.presentation.atlas.IsOriginalChartDomain (spaceFunctor.map F ⁻¹' S.carrier) := by
  refine Quotient.inductionOn F ?_
  rintro ⟨P, f⟩
  change A.presentation.atlas.IsOriginalChartDomain
    (spaceFunctor.map (sourceHomι P f) ⁻¹' S.carrier)
  erw [spaceFunctor_map_ι]
  exact (A.presentation.atlas.isOriginalChartDomain_subatlas_iff
    P.carrier P.locally_refining _).mp
      (f.isOriginalChartDomain_preimage (A.refiningSubpresentation P).hasAllLocalDomains S)

/-- The literal inverse-image subset with its proved original-domain structure. -/
def domainPreimage (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    A.presentation.atlas.OriginalChartDomain :=
  ⟨spaceFunctor.map F ⁻¹' S.carrier, isOriginalChartDomain_preimage F S⟩

@[simp]
theorem mem_domainPreimage (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) (x : A.presentation.space) :
    x ∈ domainPreimage F S ↔ spaceFunctor.map F x ∈ S := Iff.rfl

@[simp]
theorem domainPreimage_id (S : A.presentation.atlas.OriginalChartDomain) :
    domainPreimage (𝟙 (ofPresentation A)) S = S := by
  ext x
  simp only [mem_domainPreimage]
  erw [CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem domainPreimage_comp (F : ofPresentation A ⟶ ofPresentation B)
    (G : ofPresentation B ⟶ ofPresentation C)
    (S : C.presentation.atlas.OriginalChartDomain) :
    domainPreimage (F ≫ G) S = domainPreimage F (domainPreimage G S) := by
  ext x
  simp only [mem_domainPreimage, Functor.map_comp]
  rfl

@[simp]
theorem domainPreimage_inf (F : ofPresentation A ⟶ ofPresentation B)
    (S T : B.presentation.atlas.OriginalChartDomain) :
    domainPreimage F (S ⊓ T) = domainPreimage F S ⊓ domainPreimage F T := by
  ext x
  rfl

@[simp]
theorem domainPreimage_top (F : ofPresentation A ⟶ ofPresentation B) :
    domainPreimage F ⊤ = ⊤ := by
  ext x
  rfl

@[simp]
theorem domainPreimage_bot (F : ofPresentation A ⟶ ofPresentation B) :
    domainPreimage F ⊥ = ⊥ := by
  ext x
  rfl

/-- Actual domain inverse image preserves inclusion of literal subsets. -/
def domainPreimageOrderHom (F : ofPresentation A ⟶ ofPresentation B) :
    B.presentation.atlas.OriginalChartDomain →o A.presentation.atlas.OriginalChartDomain where
  toFun := domainPreimage F
  monotone' _ _ h _ hx := h hx

/-- The ambient map from the literal preimage domain has image in S. -/
theorem domainPreimageInclusion_comp_image (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    ∀ x, spaceFunctor.map (domainInclusion A (domainPreimage F S) ≫ F) x ∈ S := by
  intro x
  rw [Functor.map_comp]
  change spaceFunctor.map F
    (spaceFunctor.map (domainInclusion A (domainPreimage F S)) x) ∈ S
  erw [domainInclusion_apply]
  exact x.property

/-- The actual map from the preimage domain to the target domain.
Its full analytic numerator is supplied by the proved image-only factorization. -/
def domainPreimageMap (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    ofPresentation (A.originalDomain (domainPreimage F S)) ⟶
      ofPresentation (B.originalDomain S) :=
  domainLift S (domainInclusion A (domainPreimage F S) ≫ F)
    (domainPreimageInclusion_comp_image F S)

@[simp]
theorem domainPreimageMap_comp_inclusion (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    domainPreimageMap F S ≫ domainInclusion B S =
      domainInclusion A (domainPreimage F S) ≫ F :=
  domainLift_comp_inclusion S _ (domainPreimageInclusion_comp_image F S)

@[simp]
theorem domainPreimageMap_apply (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) (x : (domainPreimage F S).carrier) :
    (spaceFunctor.map (domainPreimageMap F S) x).val = spaceFunctor.map F x.val := by
  erw [domainPreimageMap, domainLift_apply, Functor.map_comp]
  change spaceFunctor.map F
    (spaceFunctor.map (domainInclusion A (domainPreimage F S)) x) = _
  erw [domainInclusion_apply]

/-- A commuting cone's first leg has image in the literal preimage domain. -/
theorem image_mem_domainPreimage (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (G : ofPresentation C ⟶ ofPresentation A)
    (H : ofPresentation C ⟶ ofPresentation (B.originalDomain S))
    (h : G ≫ F = H ≫ domainInclusion B S) :
    ∀ x, spaceFunctor.map G x ∈ domainPreimage F S := by
  intro x
  have hx := congrArg (fun L : ofPresentation C ⟶ ofPresentation B => spaceFunctor.map L x) h
  rw [Functor.map_comp, Functor.map_comp] at hx
  change spaceFunctor.map F (spaceFunctor.map G x) =
    spaceFunctor.map (domainInclusion B S) (spaceFunctor.map H x) at hx
  erw [domainInclusion_apply] at hx
  change spaceFunctor.map F (spaceFunctor.map G x) ∈ S
  rw [hx]
  exact (spaceFunctor.map H x).property

/-- Construct the universal arrow into the actual preimage subspace. -/
def domainPreimageLift (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (G : ofPresentation C ⟶ ofPresentation A)
    (H : ofPresentation C ⟶ ofPresentation (B.originalDomain S))
    (h : G ≫ F = H ≫ domainInclusion B S) :
    ofPresentation C ⟶ ofPresentation (A.originalDomain (domainPreimage F S)) :=
  domainLift (domainPreimage F S) G (image_mem_domainPreimage F S G H h)

@[simp]
theorem domainPreimageLift_fst (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (G : ofPresentation C ⟶ ofPresentation A)
    (H : ofPresentation C ⟶ ofPresentation (B.originalDomain S))
    (h : G ≫ F = H ≫ domainInclusion B S) :
    domainPreimageLift F S G H h ≫ domainInclusion A (domainPreimage F S) = G :=
  domainLift_comp_inclusion (domainPreimage F S) G (image_mem_domainPreimage F S G H h)

@[simp]
theorem domainPreimageLift_snd (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (G : ofPresentation C ⟶ ofPresentation A)
    (H : ofPresentation C ⟶ ofPresentation (B.originalDomain S))
    (h : G ≫ F = H ≫ domainInclusion B S) :
    domainPreimageLift F S G H h ≫ domainPreimageMap F S = H := by
  apply (cancel_mono (domainInclusion B S)).1
  rw [Category.assoc, domainPreimageMap_comp_inclusion, ← Category.assoc,
    domainPreimageLift_fst]
  exact h

/-- The actual preimage domain and the two constructed analytic arrows. -/
def domainPreimageCone (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    PullbackCone F (domainInclusion B S) :=
  PullbackCone.mk (domainInclusion A (domainPreimage F S)) (domainPreimageMap F S)
    (domainPreimageMap_comp_inclusion F S).symm

/-- Every quotient-valued commuting cone factors uniquely through the
literal preimage domain, retaining the full analytic morphisms. -/
def domainPreimageIsLimit (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    IsLimit (domainPreimageCone F S) :=
  PullbackCone.IsLimit.mk (domainPreimageMap_comp_inclusion F S).symm
    (fun c => domainPreimageLift F S c.fst c.snd c.condition)
    (fun c => domainPreimageLift_fst F S c.fst c.snd c.condition)
    (fun c => domainPreimageLift_snd F S c.fst c.snd c.condition)
    (fun c _m hm _ => (cancel_mono (domainInclusion A (domainPreimage F S))).1
      (hm.trans (domainPreimageLift_fst F S c.fst c.snd c.condition).symm))

/-- Literal inverse image realizes base change of original-domain inclusions. -/
theorem domainPreimage_isPullback (F : ofPresentation A ⟶ ofPresentation B)
    (S : B.presentation.atlas.OriginalChartDomain) :
    IsPullback (domainInclusion A (domainPreimage F S)) (domainPreimageMap F S)
      F (domainInclusion B S) where
  w := (domainPreimageMap_comp_inclusion F S).symm
  isLimit' := ⟨domainPreimageIsLimit F S⟩

end SaturatedAtlasPresentation.SourceCategory

end Langlands.Analytic
