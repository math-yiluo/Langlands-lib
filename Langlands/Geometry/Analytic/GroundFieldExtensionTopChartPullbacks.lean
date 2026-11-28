import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionPushout
import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.SaturatedTopChartComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Analytic pullbacks of greatest-chart presentations under scalar extension -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open _root_.CategoryTheory Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- The bounded universal property of a square of presented affinoid
algebras gives the categorical pushout of the same maps. -/
theorem isPushout_of_existsUnique
    {A B C P : PresentedAffinoidAlgebra K}
    {f : BoundedAlgHom K A B} {g : BoundedAlgHom K A C}
    {p : BoundedAlgHom K B P} {q : BoundedAlgHom K C P}
    (h : p.comp f = q.comp g)
    (hu : ∀ (R : PresentedAffinoidAlgebra K) (a : BoundedAlgHom K B R) (b : BoundedAlgHom K C R),
      a.comp f = b.comp g → ∃! k : BoundedAlgHom K P R, k.comp p = a ∧ k.comp q = b) :
    IsPushout (Z := A) (X := B) (Y := C) (P := P) f g p q := by
  let lift (s : PushoutCocone (show A ⟶ B from f) (show A ⟶ C from g)) : P ⟶ s.pt :=
    (hu s.pt s.inl s.inr s.condition).exists.choose
  have fac (s : PushoutCocone f g) : p ≫ lift s = s.inl ∧ q ≫ lift s = s.inr :=
    (hu s.pt s.inl s.inr s.condition).exists.choose_spec
  exact IsPushout.of_isColimit (PushoutCocone.IsColimit.mk h lift
    (fun s => (fac s).1) (fun s => (fac s).2)
    (fun s k hk₁ hk₂ => (hu s.pt s.inl s.inr s.condition).unique ⟨hk₁, hk₂⟩ (fac s)))

/-- The canonical bounded affinoid pushout is a pushout in the category
of presented affinoid algebras and bounded maps. -/
theorem AffinoidPushout.isPushout {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) :
    IsPushout (Z := A) (X := B) (Y := C) (P := AffinoidPushout.algebra f g)
      f g (AffinoidPushout.leftMap f g) (AffinoidPushout.rightMap f g) :=
  isPushout_of_existsUnique (AffinoidPushout.condition f g)
    (fun R a b h => AffinoidPushout.existsUnique_lift f g R a b h)

namespace GroundFieldExtension

variable (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

private def pushoutComparisonIso {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) :
    algebra K L (AffinoidPushout.algebra f g) ≅ AffinoidPushout.algebra (map K L f) (map K L g) where
  hom := (pushoutComparison L f g).toBoundedAlgHom
  inv := (pushoutComparison L f g).symm.toBoundedAlgHom
  hom_inv_id := BoundedAlgHom.ext (pushoutComparison L f g).toAlgEquiv.symm_apply_apply
  inv_hom_id := BoundedAlgHom.ext (pushoutComparison L f g).toAlgEquiv.apply_symm_apply

/-- Scalar extension preserves every bounded affinoid pushout square. -/
theorem isPushout_map {A B C P : PresentedAffinoidAlgebra K}
    {f : BoundedAlgHom K A B} {g : BoundedAlgHom K A C}
    {p : BoundedAlgHom K B P} {q : BoundedAlgHom K C P}
    (h : IsPushout (Z := A) (X := B) (Y := C) (P := P) f g p q) :
    IsPushout (Z := algebra K L A) (X := algebra K L B) (Y := algebra K L C) (P := algebra K L P)
      (map K L f) (map K L g) (map K L p) (map K L q) := by
  let h₀ := AffinoidPushout.isPushout f g
  let e := h.isoIsPushout B C h₀
  let F := functor (K := K) (L := L)
  let j : F.obj (AffinoidPushout.algebra f g) ≅ AffinoidPushout.algebra (map K L f) (map K L g) :=
    pushoutComparisonIso L f g
  have hp : p ≫ e.hom = AffinoidPushout.leftMap f g := IsPushout.inl_isoIsPushout_hom B C h h₀
  have hq : q ≫ e.hom = AffinoidPushout.rightMap f g := IsPushout.inr_isoIsPushout_hom B C h h₀
  refine (AffinoidPushout.isPushout (map K L f) (map K L g)).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (F.mapIso e ≪≫ j) ?_ ?_ ?_ ?_
  · simp
  · simp
  · change AffinoidPushout.leftMap (map K L f) (map K L g) = F.map p ≫ F.map e.hom ≫ j.hom
    rw [← Category.assoc, ← F.map_comp, hp]
    exact (pushoutComparison_comp_leftMap L f g).symm
  · change AffinoidPushout.rightMap (map K L f) (map K L g) = F.map q ≫ F.map e.hom ≫ j.hom
    rw [← Category.assoc, ← F.map_comp, hq]
    exact (pushoutComparison_comp_rightMap L f g).symm

end GroundFieldExtension

end Langlands.Analytic.PresentedAffinoidAlgebra

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Limits Set SaturatedAtlasPresentation PresentedAffinoidAlgebra
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension (algebra map isPushout_map)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- The saturated presentation and its complete maps underlying the localized
scalar-extension functor on original strong presentations. -/
abbrev saturatedFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤
    SaturatedAtlasPresentation.{u', max u' w, max u' w} L :=
  SaturatedAtlasPresentation.compatibleFunctor ⋙ compatibleFunctor K L ⋙
    CompatibleAtlasPresentation.saturationFunctor

local notation "E" => saturatedFunctor K L

private abbrev retainedChartIndex (S : SaturatedAtlasPresentation.{u, v, w} K)
    (i : S.presentation.atlas.Index) : ((E).obj S).presentation.atlas.Index :=
  (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas).originalSaturatedIndex i

/-- The scalar extension of a greatest chart contains every chart of the
scalar-extended saturated presentation. -/
theorem extendedChart_greatest (S : SaturatedAtlasPresentation.{u, v, w} K)
    (t : S.presentation.atlas.Index)
    (ht : ∀ i, range (S.presentation.atlas.chart i) ⊆ range (S.presentation.atlas.chart t))
    (i : ((E).obj S).presentation.atlas.Index) :
    range (((E).obj S).presentation.atlas.chart i) ⊆
      range (((E).obj S).presentation.atlas.chart (retainedChartIndex K L S t)) := by
  have htop : range (S.presentation.atlas.chart t) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, s, rfl⟩ := mem_iUnion.mp
      (S.presentation.atlas.isNet_chartFamily.1.covers.symm ▸ mem_univ x)
    exact ht j ⟨s, rfl⟩
  let b := IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas
  have hext : range (b.saturatedAtlas.chart (b.originalSaturatedIndex t)) = univ := by
    refine (b.saturatedAtlas_original_range t).trans
      ((range_chart K L S.presentation.atlas t).trans ?_)
    rw [htop, preimage_univ]
  change _ ⊆ range (b.saturatedAtlas.chart (b.originalSaturatedIndex t))
  exact hext.symm ▸ subset_univ _

private theorem extendedChart_algebra (S : SaturatedAtlasPresentation.{u, v, w} K)
    (i : S.presentation.atlas.Index) :
    ((E).obj S).presentation.atlas.algebra (retainedChartIndex K L S i) =
      algebra K L (S.presentation.atlas.algebra i) :=
  (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L S.presentation.atlas).saturatedAtlas_original_algebra i

private theorem extended_pullbackAtTop_heq {S T : SaturatedAtlasPresentation.{u, v, w} K}
    (f : S ⟶ T) (i : S.presentation.atlas.Index) (j : T.presentation.atlas.Index)
    (ht : ∀ t, range (T.presentation.atlas.chart t) ⊆ range (T.presentation.atlas.chart j)) :
    HEq (((E).map f).pullbackAtTop (retainedChartIndex K L T j)
      (extendedChart_greatest K L T j ht) (retainedChartIndex K L S i))
      (map K L (f.pullbackAtTop j ht i)) := by
  let g := (SaturatedAtlasPresentation.compatibleFunctor (K := K)).map f
  let gL := compatibleMap K L g
  let h := (admissible_iff K L g.toStrongHom g.compatible i j).2 (f.image_chart_top j ht i)
  exact gL.toStrongHom.saturationExtension_pullback_original gL.coherent i j h

omit [CompleteSpace K] in
private theorem isPushout_transport
    {A B C P A' B' C' P' : PresentedAffinoidAlgebra K}
    {f : BoundedAlgHom K A B} {g : BoundedAlgHom K A C}
    {p : BoundedAlgHom K B P} {q : BoundedAlgHom K C P}
    {f' : BoundedAlgHom K A' B'} {g' : BoundedAlgHom K A' C'}
    {p' : BoundedAlgHom K B' P'} {q' : BoundedAlgHom K C' P'}
    (hA : A' = A) (hB : B' = B) (hC : C' = C) (hP : P' = P)
    (hf : HEq f' f) (hg : HEq g' g) (hp : HEq p' p) (hq : HEq q' q)
    (h : IsPushout (Z := A) (X := B) (Y := C) (P := P) f g p q) :
    IsPushout (Z := A') (X := B') (Y := C') (P := P') f' g' p' q' := by
  cases hA
  cases hB
  cases hC
  cases hP
  cases eq_of_heq hf
  cases eq_of_heq hg
  cases eq_of_heq hp
  cases eq_of_heq hq
  exact h

variable {P A B C : SaturatedAtlasPresentation.{u, v, w} K}
  {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
  (tP : P.presentation.atlas.Index) (tA : A.presentation.atlas.Index)
  (tB : B.presentation.atlas.Index) (tC : C.presentation.atlas.Index)
  (hP : ∀ i, range (P.presentation.atlas.chart i) ⊆ range (P.presentation.atlas.chart tP))
  (hA : ∀ i, range (A.presentation.atlas.chart i) ⊆ range (A.presentation.atlas.chart tA))
  (hB : ∀ i, range (B.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart tB))
  (hC : ∀ i, range (C.presentation.atlas.chart i) ⊆ range (C.presentation.atlas.chart tC))

include hP in
/-- A square presented by a bounded pushout on greatest charts remains a
pullback in the full analytic localization after scalar extension. -/
theorem localizedFunctor_isPullback_of_topChartPushout
    (h : TopChartPushout p q f g tP tA tB tC hA hB hC) (hc : p ≫ f = q ≫ g) :
    IsPullback ((localizedFunctor K L).map (localizationFunctor.map p))
      ((localizedFunctor K L).map (localizationFunctor.map q))
      ((localizedFunctor K L).map (localizationFunctor.map f))
      ((localizedFunctor K L).map (localizationFunctor.map g)) := by
  have hw : (p.pullbackAtTop tA hA tP).comp (f.pullbackAtTop tC hC tA) =
      (q.pullbackAtTop tB hB tP).comp (g.pullbackAtTop tC hC tB) := by
    rw [← pullbackAtTop_comp _ _ tA tC hA hC, ← pullbackAtTop_comp _ _ tB tC hB hC, hc]
  have hp := isPushout_map L (isPushout_of_existsUnique hw h)
  let tP' := retainedChartIndex K L P tP
  let tA' := retainedChartIndex K L A tA
  let tB' := retainedChartIndex K L B tB
  let tC' := retainedChartIndex K L C tC
  let hA' := extendedChart_greatest K L A tA hA
  let hB' := extendedChart_greatest K L B tB hB
  let hC' := extendedChart_greatest K L C tC hC
  have hp' := isPushout_transport L
    (extendedChart_algebra K L C tC) (extendedChart_algebra K L A tA)
    (extendedChart_algebra K L B tB) (extendedChart_algebra K L P tP)
    (extended_pullbackAtTop_heq K L f tA tC hC) (extended_pullbackAtTop_heq K L g tB tC hC)
    (extended_pullbackAtTop_heq K L p tP tA hA) (extended_pullbackAtTop_heq K L q tP tB hB) hp
  have htop : TopChartPushout ((E).map p) ((E).map q) ((E).map f) ((E).map g)
      tP' tA' tB' tC' hA' hB' hC' := by
    intro R a b hab
    refine ⟨hp'.desc a b hab, ⟨hp'.inl_desc a b hab, hp'.inr_desc a b hab⟩, ?_⟩
    exact fun k hk => hp'.hom_ext (hk.1.trans (hp'.inl_desc a b hab).symm)
      (hk.2.trans (hp'.inr_desc a b hab).symm)
  have hc' : (E).map p ≫ (E).map f = (E).map q ≫ (E).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, hc]
  have hs := htop.isPullback (extendedChart_greatest K L P tP hP) hc'
  rw [localizedFunctor_map, localizedFunctor_map, localizedFunctor_map, localizedFunctor_map]
  exact (refinedStrongPullback_of_strongIsPullback hs).isPullback

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
