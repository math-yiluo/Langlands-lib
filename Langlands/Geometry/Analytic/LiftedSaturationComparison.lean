import Langlands.Geometry.Analytic.AtlasUniverseLift
import Langlands.Geometry.Analytic.LocalDomainSaturatedTransport
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction

/-! # Compare the two orders of universe lift and saturation -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology PresentedAffinoidAlgebra
open IndexedAffinoidAtlas (LocalDomain)
open IndexedAffinoidAtlas.LocalDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

private abbrev liftedAtlas : AffinoidAtlasPresentation.{u, max v z, max w t} K :=
  AffinoidAtlasPresentation.universeLift.{u, v, w, z, t} A

private abbrev liftedSat : SaturatedAtlasPresentation.{u, max v z, max v z} K :=
  SaturatedAtlasPresentation.universeLift.{u, v, v, z, z} (SaturatedAtlasPresentation.ofSaturation A)

private abbrev satLifted : SaturatedAtlasPresentation.{u, max v z, max v z} K :=
  SaturatedAtlasPresentation.ofSaturation (liftedAtlas.{u, v, w, z, t} A)

private abbrev liftHomeo : A.space ≃ₜ ULift.{z} A.space := Homeomorph.ulift.symm
private abbrev liftIndex : ULift.{t} A.atlas.Index ≃ A.atlas.Index := Equiv.ulift

private def chosenIndex (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index) : (satLifted.{u, v, w, z, t} A).presentation.atlas.Index :=
  transportedSaturatedIndex A.atlas (liftHomeo.{u, v, w, z} A) (liftIndex.{u, v, w, t} A)
    (A.atlas.saturatedRepresentative i.down)

private def chosenEquiv (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index) :
    BoundedAlgEquiv K ((liftedSat.{u, v, w, z} A).presentation.atlas.algebra i)
      ((satLifted.{u, v, w, z, t} A).presentation.atlas.algebra (chosenIndex.{u, v, w, z, t} A i)) :=
  transportedSaturatedEquiv A.atlas (liftHomeo.{u, v, w, z} A) (liftIndex.{u, v, w, t} A)
    (A.atlas.saturatedRepresentative i.down)

private theorem chosen_range (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index) :
    range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i)) =
      range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i) := by
  let h := liftHomeo.{u, v, w, z} A
  let c := liftIndex.{u, v, w, t} A
  let a := A.atlas
  change range (((a.transport h).reindex c).saturatedAtlas.chart
    (transportedSaturatedIndex a h c (a.saturatedRepresentative i.down))) =
      range (h ∘ a.saturatedChart i.down)
  rw [range_transportedSaturatedIndex, range_comp]
  exact congrArg (fun U : Set A.space => h '' U) (a.saturatedRepresentative i.down).range_ambientMap.symm

private theorem chosen_chart (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index)
    (x : BanachSpectrum ((satLifted.{u, v, w, z, t} A).presentation.atlas.algebra (chosenIndex.{u, v, w, z, t} A i))) :
    (liftedSat.{u, v, w, z} A).presentation.atlas.chart i ((chosenEquiv.{u, v, w, z, t} A i).spectrumHomeomorph x) =
      (satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i) x :=
  transportedSaturatedEquiv_chart A.atlas (liftHomeo.{u, v, w, z} A) (liftIndex.{u, v, w, t} A)
    (A.atlas.saturatedRepresentative i.down) x

private theorem chosen_admissible (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index) :
    id '' range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i) ⊆
        range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i)) := by
  rw [image_id]
  exact (chosen_range.{u, v, w, z, t} A i).superset

private theorem chosen_restriction (i i' : (liftedSat.{u, v, w, z} A).presentation.atlas.Index)
    (hi : range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i) ⊆ range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i'))
    (hj : range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i)) ⊆
      range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i'))) :
    ((satLifted.{u, v, w, z, t} A).presentation.atlas.restriction (chosenIndex.{u, v, w, z, t} A i)
      (chosenIndex.{u, v, w, z, t} A i') hj).comp (chosenEquiv.{u, v, w, z, t} A i').toBoundedAlgHom =
      (chosenEquiv.{u, v, w, z, t} A i).toBoundedAlgHom.comp ((liftedSat.{u, v, w, z} A).presentation.atlas.restriction i i' hi) := by
  let a := A.atlas
  let h := liftHomeo.{u, v, w, z} A
  have hh : range (a.saturatedChart i.down) ⊆ range (a.saturatedChart i'.down) :=
    a.saturatedAtlas.chart_subset_of_transportSubset h i.down i'.down hi
  exact transportedSaturatedEquiv_naturality a h (liftIndex.{u, v, w, t} A)
    (a.saturatedInclusion i.down i'.down hh)

private theorem subset_chosen (i : (liftedSat.{u, v, w, z} A).presentation.atlas.Index) (j : (satLifted.{u, v, w, z, t} A).presentation.atlas.Index)
    (h : id '' range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i) ⊆ range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart j)) :
    range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart (chosenIndex.{u, v, w, z, t} A i)) ⊆
      range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart j) :=
  (chosen_range.{u, v, w, z, t} A i).subset.trans (by rwa [image_id] at h)

/-- The lifted original saturation maps to the saturation of the lifted atlas,
with the identity on the lifted ambient space. -/
def liftSaturationHom :
    liftedSat.{u, v, w, z} A ⟶ satLifted.{u, v, w, z, t} A where
  baseMap := ContinuousMap.id _
  target_exists i := ⟨chosenIndex.{u, v, w, z, t} A i, chosen_admissible.{u, v, w, z, t} A i⟩
  pullback i j h := (chosenEquiv.{u, v, w, z, t} A i).symm.toBoundedAlgHom.comp
    ((satLifted.{u, v, w, z, t} A).presentation.atlas.restriction (chosenIndex.{u, v, w, z, t} A i) j
      (subset_chosen.{u, v, w, z, t} A i j h))
  chart_comm i j h x := by
    let b := (satLifted.{u, v, w, z, t} A).presentation.atlas
    let p := chosenIndex.{u, v, w, z, t} A i
    let q := chosenEquiv.{u, v, w, z, t} A i
    let r := b.restriction p j (subset_chosen.{u, v, w, z, t} A i j h)
    let y := q.symm.spectrumHomeomorph x
    change b.chart j (BanachSpectrum.comap r.toBoundedRingHom y) = _
    exact (b.restriction_chart p j _ y).trans
      ((chosen_chart.{u, v, w, z, t} A i y).symm.trans
        (congrArg ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i)
          (Homeomorph.apply_symm_apply q.spectrumHomeomorph x)))
  restriction_comm i i' j j' hi hj h h' := by
    let b := (satLifted.{u, v, w, z, t} A).presentation.atlas
    let p := chosenIndex.{u, v, w, z, t} A i
    let p' := chosenIndex.{u, v, w, z, t} A i'
    have hp : range (b.chart p) ⊆ range (b.chart p') :=
      (chosen_range.{u, v, w, z, t} A i).subset.trans
        (hi.trans (chosen_range.{u, v, w, z, t} A i').superset)
    have hlaw := chosen_restriction.{u, v, w, z, t} A i i' hi hp
    apply BoundedAlgHom.ext
    intro x
    let y := b.restriction p' j' (subset_chosen.{u, v, w, z, t} A i' j' h') x
    have he := congrArg (fun (r : BoundedAlgHom K _ _) =>
      r ((chosenEquiv.{u, v, w, z, t} A i').symm y)) hlaw
    apply (chosenEquiv.{u, v, w, z, t} A i).injective
    change (chosenEquiv.{u, v, w, z, t} A i)
      ((liftedSat.{u, v, w, z} A).presentation.atlas.restriction i i' hi ((chosenEquiv.{u, v, w, z, t} A i').symm y)) =
      (chosenEquiv.{u, v, w, z, t} A i) ((chosenEquiv.{u, v, w, z, t} A i).symm
        (b.restriction p j (subset_chosen.{u, v, w, z, t} A i j h) (b.restriction j j' hj x)))
    rw [BoundedAlgEquiv.apply_symm_apply]
    have hchain := (b.restriction_comp p p' j' hp
      (subset_chosen.{u, v, w, z, t} A i' j' h') (hp.trans (subset_chosen.{u, v, w, z, t} A i' j' h'))).symm.trans
        (b.restriction_comp p j j' (subset_chosen.{u, v, w, z, t} A i j h) hj
          (hp.trans (subset_chosen.{u, v, w, z, t} A i' j' h')))
    have hpoint := congrArg (fun (r : BoundedAlgHom K (b.algebra j') (b.algebra p)) => r x) hchain
    change b.restriction p p' hp ((chosenEquiv.{u, v, w, z, t} A i')
      ((chosenEquiv.{u, v, w, z, t} A i').symm y)) = _ at he
    rw [BoundedAlgEquiv.apply_symm_apply] at he
    exact he.symm.trans hpoint

theorem liftSaturationHom_isQuasiIso : (liftSaturationHom.{u, v, w, z, t} A).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i j h
  let b := (satLifted.{u, v, w, z, t} A).presentation.atlas
  let p := chosenIndex.{u, v, w, z, t} A i
  let hp := subset_chosen.{u, v, w, z, t} A i j h
  have hrep := (b.restriction_represents p j hp).postcomp_equiv
    (chosenEquiv.{u, v, w, z, t} A i).symm
  change Represents K ((chosenEquiv.{u, v, w, z, t} A i).symm.toBoundedAlgHom.comp
    (b.restriction p j hp)) (b.chart j ⁻¹' (id '' range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i)))
  have heq : range (b.chart p) =
      range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i) :=
    chosen_range.{u, v, w, z, t} A i
  have hlocus : b.chart j ⁻¹' range (b.chart p) = b.chart j ⁻¹'
      (id '' range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart i)) :=
    congrArg (preimage (b.chart j)) (heq.trans (image_id _).symm)
  exact (congrArg (Represents K ((chosenEquiv.{u, v, w, z, t} A i).symm.toBoundedAlgHom.comp
    (b.restriction p j hp))) hlocus).mp hrep

/-- The two actual orders of lifting and saturation agree after localization. -/
def localizedLiftSaturationIso :
    SaturatedAtlasPresentation.localizationFunctor.obj (liftedSat.{u, v, w, z} A) ≅
      SaturatedAtlasPresentation.localizationFunctor.obj (satLifted.{u, v, w, z, t} A) :=
  SaturatedAtlasPresentation.localizedQuasiIso (liftSaturationHom.{u, v, w, z, t} A)
    (liftSaturationHom_isQuasiIso.{u, v, w, z, t} A)

/-- The inverse localized comparison still induces the identity point map. -/
theorem localizedLiftSaturationIso_inv_apply (x : ULift.{z} A.space) :
    SaturatedAtlasPresentation.localizedSpaceFunctor.map
      (localizedLiftSaturationIso.{u, v, w, z, t} A).inv x = x := by
  let S := SaturatedAtlasPresentation.localizationFunctor.obj (liftedSat.{u, v, w, z} A)
  let T := SaturatedAtlasPresentation.localizationFunctor.obj (satLifted.{u, v, w, z, t} A)
  let F := SaturatedAtlasPresentation.localizedSpaceFunctor (K := K)
  let e : S ≅ T := localizedLiftSaturationIso.{u, v, w, z, t} A
  have h (y : ULift.{z} A.space) : F.map e.hom y = y := by
    have hp := SaturatedAtlasPresentation.localizedSpaceFunctor_map
      (liftSaturationHom.{u, v, w, z, t} A)
    exact congrArg (fun (f : F.obj S ⟶ F.obj T) => f y) hp
  have hc : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
  have hy : F.map e.hom (F.map e.inv x) = x :=
    congrArg (fun (f : F.obj T ⟶ F.obj T) => f x) hc
  exact (h (F.map e.inv x)).symm.trans hy

private theorem chosenIndex_original (i : A.atlas.Index) :
    chosenIndex.{u, v, w, z, t} A (ULift.up (A.atlas.originalSaturatedIndex i)) =
      (liftedAtlas.{u, v, w, z, t} A).atlas.originalSaturatedIndex (ULift.up i) := by
  apply (satLifted.{u, v, w, z, t} A).presentation.atlas.chartDomain_injective
  let h := liftHomeo.{u, v, w, z} A
  let I := A.atlas.originalSaturatedIndex i
  have himage : range ((liftedSat.{u, v, w, z} A).presentation.atlas.chart (ULift.up I)) =
      h '' range (A.atlas.saturatedAtlas.chart I) :=
    A.atlas.saturatedAtlas.range_transportChart h I
  exact (chosen_range.{u, v, w, z, t} A _).trans (himage.trans
    ((congrArg (fun U : Set A.space => h '' U) (A.atlas.saturatedAtlas_original_range i)).trans
      ((A.atlas.range_transportChart h i).symm.trans
        ((liftedAtlas.{u, v, w, z, t} A).atlas.saturatedAtlas_original_range (ULift.up i)).symm)))

omit [CompleteSpace K] in
private theorem boundedId_heq {R S : PresentedAffinoidAlgebra K} (h : R = S) :
    HEq (BoundedAlgHom.id K R) (BoundedAlgHom.id K S) := by
  cases h
  rfl

omit [CompleteSpace K] in
private theorem id_heq_of_equiv {R S : PresentedAffinoidAlgebra K} (h : R = S)
    (e : BoundedAlgEquiv K R S) (he : HEq e.toBoundedAlgHom (BoundedAlgHom.id K R)) :
    HEq e.symm.toBoundedAlgHom (BoundedAlgHom.id K R) := by
  cases h
  have h' := eq_of_heq he
  apply heq_of_eq
  apply BoundedAlgHom.ext
  intro x
  have hc := congrArg (fun f : BoundedAlgHom K R R => f (e.symm x)) h'
  exact hc.symm.trans (e.apply_symm_apply x)

private theorem chosenEquiv_original (i : A.atlas.Index) :
    HEq (chosenEquiv.{u, v, w, z, t} A (ULift.up (A.atlas.originalSaturatedIndex i))).toBoundedAlgHom
      (BoundedAlgHom.id K (A.atlas.algebra i)) := by
  let h := liftHomeo.{u, v, w, z} A
  let c := liftIndex.{u, v, w, t} A
  let b := (liftedAtlas.{u, v, w, z, t} A).atlas
  let U := A.atlas.saturatedRepresentative (A.atlas.originalSaturatedIndex i)
  let V := (transportReindexFunctor A.atlas h c).obj U
  let W := b.saturatedRepresentative (transportedSaturatedIndex A.atlas h c U)
  let D := b.originalLocalDomain (ULift.up i)
  have hW : W = D := by
    change b.saturatedRepresentative (chosenIndex.{u, v, w, z, t} A
      (ULift.up (A.atlas.originalSaturatedIndex i))) = _
    exact (congrArg b.saturatedRepresentative (chosenIndex_original.{u, v, w, z, t} A i)).trans
      (b.saturatedRepresentative_original (ULift.up i))
  let U₀ := LocalDomain.transport A.atlas h U
  let p : LocalDomain.Inclusion (ofReindex (A.atlas.transport h) c V) U₀ :=
    ((reindexEquivalence (A.atlas.transport h) c).counitIso.app U₀).hom
  let q : LocalDomain.Inclusion W V :=
    (isoOfLocusEq V W (b.saturatedRepresentative_locus
      (transportedSaturatedIndex A.atlas h c U)).symm).inv
  let F := ofReindexFunctor (A.atlas.transport h) c
  have hD : F.obj D = U₀ :=
    congrArg (LocalDomain.transport A.atlas h) (A.atlas.saturatedRepresentative_original i).symm
  have key : ∀ (U' : LocalDomain (A.atlas.transport h)), U' = F.obj D →
      ∀ r : LocalDomain.Inclusion (F.obj D) U',
        HEq r.restriction (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    intro U' hU' r
    subst U'
    let r₀ : LocalDomain.Inclusion (F.obj D) (F.obj D) := 𝟙 (F.obj D)
    have hr : r = r₀ := Subsingleton.elim _ _
    exact heq_of_eq (show r.restriction = r₀.restriction from congrArg LocalDomain.Inclusion.restriction hr)
  have key' : ∀ (W' : LocalDomain b), W' = D → ∀ q' : LocalDomain.Inclusion W' V,
      HEq (q'.restriction.comp p.restriction) (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    intro W' hW' q'
    subst W'
    let q₀ : LocalDomain.Inclusion (F.obj D) (F.obj V) := F.map (show D ⟶ V from q')
    exact key _ hD.symm (show LocalDomain.Inclusion (F.obj D) U₀ from
      (show F.obj D ⟶ F.obj V from q₀) ≫ (show F.obj V ⟶ U₀ from p))
  exact key' W hW q

theorem liftSaturationHom_admissible_original (i : A.atlas.Index) :
    (liftSaturationHom.{u, v, w, z, t} A).baseMap '' range
      ((liftedSat.{u, v, w, z} A).presentation.atlas.chart (ULift.up (A.atlas.originalSaturatedIndex i))) ⊆
    range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart
      ((liftedAtlas.{u, v, w, z, t} A).atlas.originalSaturatedIndex (ULift.up i))) :=
  (chosen_admissible.{u, v, w, z, t} A _).trans
    (congrArg (fun j => range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart j))
      (chosenIndex_original.{u, v, w, z, t} A i)).subset

/-- At the original charts, the lift–saturation comparison is the bounded
identity after identification of the whole-domain representatives. -/
theorem liftSaturationHom_pullback_original_heq (i : A.atlas.Index) :
    HEq ((liftSaturationHom.{u, v, w, z, t} A).pullback
      (ULift.up (A.atlas.originalSaturatedIndex i))
      ((liftedAtlas.{u, v, w, z, t} A).atlas.originalSaturatedIndex (ULift.up i))
      (liftSaturationHom_admissible_original.{u, v, w, z, t} A i))
      (BoundedAlgHom.id K (A.atlas.algebra i)) := by
  let s := (liftedSat.{u, v, w, z} A).presentation
  let b := (satLifted.{u, v, w, z, t} A).presentation
  let I : s.atlas.Index := ULift.up (A.atlas.originalSaturatedIndex i)
  let J : b.atlas.Index := (liftedAtlas.{u, v, w, z, t} A).atlas.originalSaturatedIndex (ULift.up i)
  let C := chosenIndex.{u, v, w, z, t} A I
  let e := chosenEquiv.{u, v, w, z, t} A I
  have hCJ : C = J := chosenIndex_original.{u, v, w, z, t} A i
  have ha : s.atlas.algebra I = A.atlas.algebra i := A.atlas.saturatedAtlas_original_algebra i
  have hb : b.atlas.algebra C = A.atlas.algebra i :=
    (congrArg b.atlas.algebra hCJ).trans
      ((liftedAtlas.{u, v, w, z, t} A).atlas.saturatedAtlas_original_algebra (ULift.up i))
  have he : HEq e.symm.toBoundedAlgHom (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    have he' := id_heq_of_equiv (ha.trans hb.symm) e
      ((chosenEquiv_original.{u, v, w, z, t} A i).trans
        (boundedId_heq ha.symm))
    exact he'.trans (boundedId_heq ha)
  have hkey (j : b.atlas.Index) (h : C = j) (hsub : range (b.atlas.chart C) ⊆ range (b.atlas.chart j)) :
      HEq (e.symm.toBoundedAlgHom.comp (b.atlas.restriction C j hsub)) e.symm.toBoundedAlgHom := by
    subst j
    exact heq_of_eq ((congrArg (fun p => e.symm.toBoundedAlgHom.comp p)
      (b.atlas.restriction_id C hsub)).trans (BoundedAlgHom.comp_id _))
  exact (hkey J hCJ _).trans he

section Naturality

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

private abbrev liftedSatHom (f : CompatibleStrongHom A B) :
    liftedSat.{u, v, w, z} A ⟶ liftedSat.{u, v, w, z} B :=
  (SaturatedAtlasPresentation.universeLiftFunctor.{u, v, v, z, z} (K := K)).map
    (show SaturatedAtlasPresentation.ofSaturation A ⟶ SaturatedAtlasPresentation.ofSaturation B from
      f.saturationExtension)

private abbrev satLiftedHom (f : CompatibleStrongHom A B) :
    satLifted.{u, v, w, z, t} A ⟶ satLifted.{u, v, w, z, t} B :=
  (CompatibleStrongHom.universeLift.{u, v, w, z, t} f).saturationExtension

/-- Lifting the saturated map and saturating the lifted map commute with
our actual comparison on all bounded pullbacks. -/
theorem liftSaturationHom_naturality (f : CompatibleStrongHom A B) :
    liftedSatHom.{u, v, w, z} f ≫ liftSaturationHom.{u, v, w, z, t} B =
      liftSaturationHom.{u, v, w, z, t} A ≫ satLiftedHom.{u, v, w, z, t} f := by
  let S := liftedSat.{u, v, w, z} A
  let T := satLifted.{u, v, w, z, t} B
  let F := liftedSatHom.{u, v, w, z} f
  let G := satLiftedHom.{u, v, w, z, t} f
  let e := liftSaturationHom.{u, v, w, z, t} A
  let e' := liftSaturationHom.{u, v, w, z, t} B
  let cA := (liftedAtlas.{u, v, w, z, t} A).atlas
  let cB := (liftedAtlas.{u, v, w, z, t} B).atlas
  let f' := CompatibleStrongHom.universeLift.{u, v, w, z, t} f
  refine StrongHom.ext_of_saturated (f := F ≫ e') (g := e ≫ G) S.hasAllLocalDomains rfl ?_
  intro s
  let i := (A.atlas.saturatedRepresentative s.down).index
  let I : S.presentation.atlas.Index := ULift.up (A.atlas.originalSaturatedIndex i)
  have hs : range (S.presentation.atlas.chart s) ⊆ range (S.presentation.atlas.chart I) :=
    A.atlas.saturatedAtlas.transportChart_subset (liftHomeo.{u, v, w, z} A)
      s.down (A.atlas.originalSaturatedIndex i) (StrongHom.saturated_chart_subset_parent s.down)
  obtain ⟨j, hj⟩ := f.target_exists i
  let J : (liftedSat.{u, v, w, z} B).presentation.atlas.Index := ULift.up (B.atlas.originalSaturatedIndex j)
  let I' : (satLifted.{u, v, w, z, t} A).presentation.atlas.Index := cA.originalSaturatedIndex (ULift.up i)
  let J' : T.presentation.atlas.Index := cB.originalSaturatedIndex (ULift.up j)
  have hF₀ := f.toStrongHom.saturationExtension_original_admissible i j hj
  have hF : F.baseMap '' range (S.presentation.atlas.chart I) ⊆
      range ((liftedSat.{u, v, w, z} B).presentation.atlas.chart J) :=
    (StrongHom.transportedBaseMap_admissible_iff
      (A := A.saturatedPresentation) (B := B.saturatedPresentation)
      (liftHomeo.{u, v, w, z} A) (liftHomeo.{u, v, w, z} B)
      Equiv.ulift Equiv.ulift f.saturationExtension I J).mpr hF₀
  have he : e.baseMap '' range (S.presentation.atlas.chart I) ⊆
      range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart I') :=
    liftSaturationHom_admissible_original.{u, v, w, z, t} A i
  have he' : e'.baseMap '' range ((liftedSat.{u, v, w, z} B).presentation.atlas.chart J) ⊆
      range (T.presentation.atlas.chart J') :=
    liftSaturationHom_admissible_original.{u, v, w, z, t} B j
  have hj' : f'.baseMap '' range (cA.chart (ULift.up i)) ⊆ range (cB.chart (ULift.up j)) :=
    (StrongHom.transportedBaseMap_admissible_iff (liftHomeo.{u, v, w, z} A)
      (liftHomeo.{u, v, w, z} B) (liftIndex.{u, v, w, t} A)
      (liftIndex.{u, v, w, t} B) f.toStrongHom (ULift.up i) (ULift.up j)).mpr hj
  have hG : G.baseMap '' range ((satLifted.{u, v, w, z, t} A).presentation.atlas.chart I') ⊆
      range (T.presentation.atlas.chart J') :=
    f'.toStrongHom.saturationExtension_original_admissible (ULift.up i) (ULift.up j) hj'
  have h₁ := F.comp_admissible e' I J J' hF he'
  have h₂ := e.comp_admissible G I I' J' he hG
  have hs₁ := (image_mono hs).trans h₁
  have hs₂ := (image_mono hs).trans h₂
  refine ⟨J', hs₁, ?_⟩
  have hp₁ := (show StrongHom S.presentation T.presentation from F ≫ e').restriction_comp_pullback
    s I J' hs hs₁ h₁
  have hp₂ := (show StrongHom S.presentation T.presentation from e ≫ G).restriction_comp_pullback
    s I J' hs hs₂ h₂
  have hmain : (F ≫ e').pullback I J' h₁ = (e ≫ G).pullback I J' h₂ := by
    change (F.saturatedComp e' S.hasAllLocalDomains (liftedSat.{u, v, w, z} B).hasAllLocalDomains).pullback I J' h₁ =
      (e.saturatedComp G S.hasAllLocalDomains (satLifted.{u, v, w, z, t} A).hasAllLocalDomains).pullback I J' h₂
    rw [StrongHom.saturatedComp_pullback F e' _ _ I J J' hF he' h₁,
      StrongHom.saturatedComp_pullback e G _ _ I I' J' he hG h₂]
    have hF' : HEq (F.pullback I J hF) (f.pullback i j hj) :=
      f.toStrongHom.saturationExtension_pullback_original f.coherent i j hj
    have hG' : HEq (G.pullback I' J' hG) (f.pullback i j hj) :=
      f'.toStrongHom.saturationExtension_pullback_original f'.coherent (ULift.up i) (ULift.up j) hj'
    have hsA : S.presentation.atlas.algebra I = A.atlas.algebra i := A.atlas.saturatedAtlas_original_algebra i
    have hsB : (liftedSat.{u, v, w, z} B).presentation.atlas.algebra J = B.atlas.algebra j :=
      B.atlas.saturatedAtlas_original_algebra j
    have htA := cA.saturatedAtlas_original_algebra (ULift.up i)
    have htB := cB.saturatedAtlas_original_algebra (ULift.up j)
    have hcomp₁ := BoundedAlgHom.comp_heq hsA hsB htB hF'
      (liftSaturationHom_pullback_original_heq.{u, v, w, z, t} B j)
    have hcomp₂ := BoundedAlgHom.comp_heq hsA htA htB
      (liftSaturationHom_pullback_original_heq.{u, v, w, z, t} A i) hG'
    exact eq_of_heq ((hcomp₁.trans (heq_of_eq (BoundedAlgHom.comp_id (f.pullback i j hj)))).trans
      (hcomp₂.trans (heq_of_eq (BoundedAlgHom.id_comp (f.pullback i j hj)))).symm)
  exact hp₁.symm.trans ((congrArg (fun p => (S.presentation.atlas.restriction s I hs).comp p) hmain).trans hp₂)

end Naturality
end Langlands.Analytic.AffinoidAtlasPresentation
