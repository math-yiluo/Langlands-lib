import Langlands.Geometry.Analytic.CompatibleStrongCategory

/-! # The actual saturation functor on original compatible atlas maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- For maps between the constructed enlargements, one complete bounded
pullback per original source parent determines the entire map. -/
theorem ext_on_original
    {F G : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hb : F.baseMap = G.baseMap)
    (hp : ∀ i : A.atlas.Index, ∃ (j : B.atlas.Index)
      (h : F.baseMap ''
        Set.range (A.atlas.saturatedChart (A.atlas.originalSaturatedIndex i)) ⊆
          Set.range (B.atlas.saturatedChart (B.atlas.originalSaturatedIndex j))),
      F.pullback (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j) h =
        G.pullback (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
          (by rw [← hb]; exact h)) :
    F = G := by
  refine ext_of_saturated A.atlas.saturatedAtlas_hasAllLocalDomains hb ?_
  intro S
  let i := (A.atlas.saturatedRepresentative S).index
  obtain ⟨j, hIJ, hpIJ⟩ := hp i
  let I := A.atlas.originalSaturatedIndex i
  let J := B.atlas.originalSaturatedIndex j
  have hSI : Set.range (A.saturatedPresentation.atlas.chart S) ⊆
      Set.range (A.saturatedPresentation.atlas.chart I) := saturated_chart_subset_parent S
  have hSJ := (Set.image_mono hSI).trans hIJ
  have hIJG : G.baseMap '' Set.range (A.saturatedPresentation.atlas.chart I) ⊆
      Set.range (B.saturatedPresentation.atlas.chart J) := by rw [← hb]; exact hIJ
  have hSJG : G.baseMap '' Set.range (A.saturatedPresentation.atlas.chart S) ⊆
      Set.range (B.saturatedPresentation.atlas.chart J) := by rw [← hb]; exact hSJ
  have hFp : (A.saturatedPresentation.atlas.restriction S I hSI).comp
      (F.pullback I J hIJ) = F.pullback S J hSJ := by
    simpa only [B.saturatedPresentation.atlas.restriction_id J Subset.rfl,
      BoundedAlgHom.comp_id] using
      F.restriction_comm S I J J hSI Subset.rfl hSJ hIJ
  have hGp : (A.saturatedPresentation.atlas.restriction S I hSI).comp
      (G.pullback I J hIJG) = G.pullback S J hSJG := by
    simpa only [B.saturatedPresentation.atlas.restriction_id J Subset.rfl,
      BoundedAlgHom.comp_id] using
      G.restriction_comm S I J J hSI Subset.rfl hSJG hIJG
  exact ⟨J, hSJ, hFp.symm.trans ((congrArg (fun q =>
    (A.saturatedPresentation.atlas.restriction S I hSI).comp q) hpIJ).trans hGp)⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

omit [CompleteSpace K] in
private theorem boundedId_heq {R R' : PresentedAffinoidAlgebra K} (hR : R = R') :
    HEq (BoundedAlgHom.id K R) (BoundedAlgHom.id K R') := by
  cases hR
  rfl

omit [CompleteSpace K] in
private theorem boundedComp_heq
    {R R' S S' T T' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (hT : T = T')
    {p : BoundedAlgHom K S R} {p' : BoundedAlgHom K S' R'}
    {q : BoundedAlgHom K T S} {q' : BoundedAlgHom K T' S'}
    (hp : HEq p p') (hq : HEq q q') :
    HEq (p.comp q) (p'.comp q') := by
  cases hR
  cases hS
  cases hT
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

/-- The actual extension of the original identity is the entire enlarged
identity, including all bounded pullbacks to unrelated target charts. -/
@[simp]
theorem saturationExtension_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (id A).saturationExtension = StrongHom.id A.saturatedPresentation := by
  refine StrongHom.ext_on_original rfl ?_
  intro i
  let I : A.saturatedPresentation.atlas.Index := A.atlas.originalSaturatedIndex i
  have hi : (id A).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.atlas.chart i) := by
    simp only [id, StrongHom.id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]
  have hI := (id A).toStrongHom.saturationExtension_original_admissible i i hi
  refine ⟨i, hI, ?_⟩
  change (id A).saturationExtension.pullback I I _ =
    A.saturatedPresentation.atlas.restriction I I Subset.rfl
  rw [A.saturatedPresentation.atlas.restriction_id]
  have hr := (id A).toStrongHom.saturationExtension_pullback_original
    (id A).coherent i i hi
  change HEq ((id A).saturationExtension.pullback I I _)
    (A.atlas.restriction i i Subset.rfl) at hr
  rw [A.atlas.restriction_id] at hr
  exact eq_of_heq (hr.trans (boundedId_heq (A.atlas.saturatedAtlas_original_algebra i)).symm)

/-- Saturation preserves the original actual bounded composition. One
admissible original chain per source parent suffices; no target condition
on an unrelated intermediate chart is assumed. -/
theorem saturationExtension_comp (f : CompatibleStrongHom A B)
    (g : CompatibleStrongHom B C) :
    (f.comp g).saturationExtension =
      f.saturationExtension.saturatedComp g.saturationExtension
        A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains := by
  refine StrongHom.ext_on_original rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨k, hg⟩ := g.target_exists j
  let I := A.atlas.originalSaturatedIndex i
  let J := B.atlas.originalSaturatedIndex j
  let L := C.atlas.originalSaturatedIndex k
  have hF := f.toStrongHom.saturationExtension_original_admissible i j hf
  have hG := g.toStrongHom.saturationExtension_original_admissible j k hg
  have hFG := f.saturationExtension.comp_admissible g.saturationExtension I J L hF hG
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom i j k hf hg
  refine ⟨k, hFG, ?_⟩
  rw [StrongHom.saturatedComp_pullback f.saturationExtension g.saturationExtension
    A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains
    I J L hF hG]
  have he := (f.comp g).toStrongHom.saturationExtension_pullback_original
    (f.comp g).coherent i k hfg
  rw [comp_pullback f g i j k hf hg hfg] at he
  have hchain := boundedComp_heq
    (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra j)
    (C.atlas.saturatedAtlas_original_algebra k)
    (f.toStrongHom.saturationExtension_pullback_original f.coherent i j hf)
    (g.toStrongHom.saturationExtension_pullback_original g.coherent j k hg)
  exact eq_of_heq (he.trans hchain.symm)

private theorem pullback_eq_of_eq
    {F G : StrongHom A B} (he : F = G) (i : A.atlas.Index) (j : B.atlas.Index)
    (hF : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hG : G.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    F.pullback i j hF = G.pullback i j hG := by
  cases he
  rfl

/-- Equality of the enlarged maps recovers equality of all original bounded
maps, hence equality in the original compatible category. -/
theorem saturationExtension_injective :
    Function.Injective (saturationExtension : CompatibleStrongHom A B → _) := by
  intro f g he
  have hb : f.baseMap = g.baseMap := congrArg
    (fun F : StrongHom A.saturatedPresentation B.saturatedPresentation => F.baseMap) he
  refine ext_of_pullback hb ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  have hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := by
    rw [← hb]
    exact hf
  have hp := pullback_eq_of_eq he
    (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
    (f.toStrongHom.saturationExtension_original_admissible i j hf)
    (g.toStrongHom.saturationExtension_original_admissible i j hg)
  have hr := (f.toStrongHom.saturationExtension_pullback_original f.coherent i j hf).symm.trans
    ((heq_of_eq hp).trans
      (g.toStrongHom.saturationExtension_pullback_original g.coherent i j hg))
  exact ⟨j, hf, eq_of_heq hr⟩

end Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

namespace Langlands.Analytic.CompatibleAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Construct the enlargement on objects and extend the complete original
bounded-map families on morphisms. Both enlarged index types lie in `v`. -/
def saturationFunctor : CompatibleAtlasPresentation.{u, v, w} K ⥤
    SaturatedAtlasPresentation.{u, v, v} K where
  obj A := SaturatedAtlasPresentation.ofSaturation A.presentation
  map f := f.saturationExtension
  map_id A := AffinoidAtlasPresentation.CompatibleStrongHom.saturationExtension_id A.presentation
  map_comp f g := AffinoidAtlasPresentation.CompatibleStrongHom.saturationExtension_comp f g

@[simp]
theorem saturationFunctor_baseMap
    {A B : CompatibleAtlasPresentation.{u, v, w} K} (f : A ⟶ B) :
    ((saturationFunctor (K := K)).map f).baseMap = f.baseMap := rfl

/-- The constructed functor retains literal ambient spaces and maps. -/
theorem saturationFunctor_spaceFunctor :
    saturationFunctor (K := K) ⋙ SaturatedAtlasPresentation.spaceFunctor =
      (spaceFunctor : CompatibleAtlasPresentation.{u, v, w} K ⥤ _) := rfl

instance : (saturationFunctor (K := K) :
    CompatibleAtlasPresentation.{u, v, w} K ⥤ _).Faithful where
  map_injective h := AffinoidAtlasPresentation.CompatibleStrongHom.saturationExtension_injective h

end Langlands.Analytic.CompatibleAtlasPresentation
