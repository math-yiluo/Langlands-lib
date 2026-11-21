import Langlands.Geometry.Analytic.QuasiEtaleFieldPointImageLift
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality
import Langlands.Geometry.Analytic.PairSystemLocalizedMorphisms
import Langlands.Geometry.Analytic.Spectrum.ResidueField.AlgebraicLift
import Langlands.Geometry.Analytic.CommonPointField.Transport

/-! # Lifting full points along maps with quasi-étale composite -/

noncomputable section

universe u v uE uM uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Topology AffinoidAtlasPresentation BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Φ" => localizedFieldPointFunctor (K := K)
local notation "π" => localizedFieldPointProjection (K := K)
local notation "loc" => localizationFunctor (K := K)

section ChangeValues

variable {E : Type uE} [NormedField E] [NormedAlgebra K E]
  {M : Type uM} [NormedField M] [NormedAlgebra K M]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

private def changeValues {X : LocalizedCategory.{u, v, v} (K := K)} (i : BoundedAlgHom K E M) (hi : Isometry i)
    (q : (Φ E).obj X) : (Φ M).obj X :=
  FieldPoint.mapField (A := (presentationOf X).presentation) q i.toAlgHom hi

private theorem changeValues_point {X : LocalizedCategory.{u, v, v} (K := K)} (i : BoundedAlgHom K E M) (hi : Isometry i)
    (q : (Φ E).obj X) : ((π M).app X (changeValues i hi q)).down = ((π E).app X q).down := rfl

private theorem changeValues_comp {X : LocalizedCategory.{u, v, v} (K := K)} (i : BoundedAlgHom K E M) (hi : Isometry i)
    (j : BoundedAlgHom K M L) (hj : Isometry j) (p : (Φ E).obj X) :
    changeValues j hj (changeValues i hi p) = changeValues (j.comp i) (hj.comp hi) p := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  apply FieldPoint.ext' rfl
  intro _ _ _
  exact AlgHom.comp_assoc _ _ _

private theorem changeValues_strong {A B : SaturatedAtlasPresentation.{u,v,v} K}
    (f : A ⟶ B) (i : BoundedAlgHom K E M) (hi : Isometry i)
    (p : (Φ E).obj ((loc).obj A)) :
    (Φ M).map ((loc).map f) (changeValues i hi p) =
      changeValues i hi ((Φ E).map ((loc).map f) p) := by
  apply FieldPoint.ext' rfl
  intro _ _ _
  exact AlgHom.comp_assoc _ _ _

private theorem changeValues_naturality {X Y : LocalizedCategory.{u, v, v} (K := K)} (f : X ⟶ Y)
    (i : BoundedAlgHom K E M) (hi : Isometry i) (p : (Φ E).obj X) :
    (Φ M).map f (changeValues i hi p) = changeValues i hi ((Φ E).map f p) := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  let : IsIso ((loc).map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
  let p' := (Φ E).map (inv ((loc).map φ.s)) p
  have hp : (Φ E).map ((loc).map φ.s) p' = p := by
    exact Iso.inv_hom_id_apply ((Φ E).mapIso (localizedQuasiIso φ.s φ.hs)) p
  calc
    _ = (Φ M).map (localizedRightFraction φ) ((Φ M).map ((loc).map φ.s) (changeValues i hi p')) := by
      rw [changeValues_strong, hp]; rfl
    _ = (Φ M).map ((loc).map φ.f) (changeValues i hi p') := by
      rw [← Functor.map_comp_apply, localizationFunctor_map_s_comp_localizedRightFraction]
    _ = _ := by
      rw [changeValues_strong, ← localizationFunctor_map_s_comp_localizedRightFraction,
        Functor.map_comp_apply, hp]; rfl

end ChangeValues

/-- A chart on a presentation of a localized object with a specified spectrum point. -/
private structure ResidueChart (X : LocalizedCategory.{u, v, v} (K := K)) where
  S : SaturatedAtlasPresentation.{u,v,v} K
  e : (loc).obj S ≅ X
  i : S.presentation.atlas.Index
  z : BanachSpectrum (S.presentation.atlas.algebra i)

namespace ResidueChart

variable {X : LocalizedCategory.{u, v, v} (K := K)} (C : ResidueChart X)

private abbrev Field := CompletedResidueField K C.z

private def point : localizedSpaceFunctor.obj X :=
  localizedSpaceFunctor.map C.e.hom (C.S.presentation.atlas.chart C.i C.z)

private theorem exists_at (x : localizedSpaceFunctor.obj X) :
    ∃ C : ResidueChart X, C.point = x := by
  obtain ⟨S, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨i, z, hz⟩ := S.presentation.atlas.exists_mem_range_chart x
  refine ⟨⟨S, Iso.refl _, i, z⟩, ?_⟩
  let x' : localizedSpaceFunctor.obj ((loc).obj S) := S.presentation.atlas.chart i z
  change localizedSpaceFunctor.map (𝟙 ((loc).obj S)) x' = x
  rw [CategoryTheory.Functor.map_id, TopCat.id_app]
  exact hz

private def chartCharacter : C.S.presentation.atlas.algebra C.i →ₐ[K] C.Field :=
  (completedResidueMap K C.z).toAlgHom

private theorem exists_chartRealization :
    ∃ p : FieldPoint C.Field C.S.presentation,
      p.point = C.S.presentation.atlas.chart C.i C.z ∧
        ∃ h : p.point ∈ Set.range (C.S.presentation.atlas.chart C.i),
          p.eval C.i h = C.chartCharacter :=
  (FieldPoint.existsUnique_of_chartCharacter
    PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity _ _ C.chartCharacter
    ⟨C.z, rfl, norm_completedResidueMap K C.z⟩).exists

private def chartRealization : FieldPoint C.Field C.S.presentation :=
  C.exists_chartRealization.choose

private theorem chartRealization_point :
    C.chartRealization.point = C.S.presentation.atlas.chart C.i C.z :=
  C.exists_chartRealization.choose_spec.1

private theorem chartRealization_eval (h : C.chartRealization.point ∈
    Set.range (C.S.presentation.atlas.chart C.i)) :
    C.chartRealization.eval C.i h = C.chartCharacter :=
  C.exists_chartRealization.choose_spec.2.choose_spec

private def realization : (Φ C.Field).obj X :=
  (Φ C.Field).map C.e.hom C.chartRealization

private theorem realization_point : ((π C.Field).app X C.realization).down = C.point := by
  exact (localizedFieldPointProjection_map_down C.e.hom C.chartRealization).trans
    (congrArg (localizedSpaceFunctor.map C.e.hom) C.chartRealization_point)

private theorem realization_onChart :
    (Φ C.Field).map C.e.inv C.realization = C.chartRealization :=
  Iso.hom_inv_id_apply ((Φ C.Field).mapIso C.e) C.chartRealization

variable {M : Type uM} [NormedField M] [NormedAlgebra K M]

private theorem exists_lift [CompleteSpace M] (p : (Φ M).obj X) (hp : ((π M).app X p).down = C.point) :
    ∃ (i : BoundedAlgHom K C.Field M) (hi : Isometry i),
      changeValues i hi C.realization = p := by
  let p' : FieldPoint M C.S.presentation := (Φ M).map C.e.inv p
  have hp' : p'.point = C.S.presentation.atlas.chart C.i C.z := by
    change ((π M).app ((loc).obj C.S) ((Φ M).map C.e.inv p)).down = _
    rw [localizedFieldPointProjection_map_down, hp, point]
    exact Iso.hom_inv_id_apply (localizedSpaceFunctor.mapIso C.e)
      (C.S.presentation.atlas.chart C.i C.z)
  have hz : p'.point ∈ Set.range (C.S.presentation.atlas.chart C.i) := ⟨C.z, hp'.symm⟩
  obtain ⟨z, hzp, hn⟩ := p'.isChartPoint C.i hz
  have hzC : z = C.z := (C.S.presentation.atlas.isEmbedding_chart C.i).injective (hzp.trans hp')
  subst z
  let i := completedResidueLift K C.z (p'.eval C.i hz) hn
  let hi := isometry_completedResidueLift K C.z (p'.eval C.i hz) hn
  have he : changeValues (X := (loc).obj C.S) i hi C.chartRealization = p' := by
    have hC : C.chartRealization.point ∈ Set.range (C.S.presentation.atlas.chart C.i) :=
      ⟨C.z, C.chartRealization_point.symm⟩
    apply FieldPoint.eq_of_eval_eq (L := M)
      PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity
      (C.chartRealization_point.trans hp'.symm) C.i hC hz
    change (i.toAlgHom.comp (C.chartRealization.eval C.i hC)) = _
    rw [C.chartRealization_eval]
    ext a
    exact completedResidueLift_map K C.z (p'.eval C.i hz) hn a
  refine ⟨i, hi, ?_⟩
  exact (changeValues_naturality C.e.hom i hi C.chartRealization).symm.trans
    ((congrArg ((Φ M).map C.e.hom) he).trans
      (Iso.inv_hom_id_apply ((Φ M).mapIso C.e) p))

private theorem lift_unique {i j : BoundedAlgHom K C.Field M} (hi : Isometry i) (hj : Isometry j)
    (h : changeValues i hi C.realization = changeValues j hj C.realization) : i = j := by
  have h' := congrArg ((Φ M).map C.e.inv) h
  rw [changeValues_naturality, changeValues_naturality, C.realization_onChart] at h'
  have hz : C.chartRealization.point ∈ Set.range (C.S.presentation.atlas.chart C.i) :=
    ⟨C.z, C.chartRealization_point.symm⟩
  have he := FieldPoint.eval_congr h' C.i hz hz
  change i.toAlgHom.comp (C.chartRealization.eval C.i hz) =
    j.toAlgHom.comp (C.chartRealization.eval C.i hz) at he
  rw [C.chartRealization_eval] at he
  apply completedResidueBoundedAlgHom_ext K C.z
  exact AlgHom.congr_fun he

/-- Move the same chart and character along an analytic isomorphism. -/
private def transport {Y : LocalizedCategory.{u, v, v} (K := K)} (e : X ≅ Y) :
    ResidueChart Y := ⟨C.S, C.e ≪≫ e, C.i, C.z⟩

private theorem realization_transport {Y : LocalizedCategory.{u, v, v} (K := K)} (e : X ≅ Y) :
    (C.transport e).realization = (Φ C.Field).map e.hom C.realization :=
  (Φ C.Field).map_comp_apply C.e.hom e.hom C.chartRealization

end ResidueChart

/-- The algebra structure on the larger field is the one induced by the specified map. -/
private def IsAlgebraicVia {E : Type uE} [NormedField E] [Algebra K E]
    {M : Type uM} [NormedField M] [Algebra K M] (i : BoundedAlgHom K E M) : Prop :=
  let : Algebra E M := i.toAlgHom.toRingHom.toAlgebra
  Algebra.IsAlgebraic E M

/-- A full point at the selected preimage whose field of values is algebraic over the
residue of a chart at its image. The witness records equality of the full image point. -/
private structure FinitePointWitness {Y X : LocalizedCategory.{u, v, v} (K := K)}
    (f : Y ⟶ X) (y : localizedSpaceFunctor.obj Y) where
  chart : ResidueChart X
  sourceAlgebra : PresentedAffinoidAlgebra K
  z : BanachSpectrum sourceAlgebra
  embed : BoundedAlgHom K chart.Field (CompletedResidueField K z)
  isometry_embed : Isometry embed
  algebraic_embed : IsAlgebraicVia embed
  lift : (Φ (CompletedResidueField K z)).obj Y
  lift_point : ((π (CompletedResidueField K z)).app Y lift).down = y
  lift_map : (Φ (CompletedResidueField K z)).map f lift =
    changeValues embed isometry_embed chart.realization

set_option maxHeartbeats 800000 in
private theorem finitePointWitness_localizationFunctor_map_of_finiteAt
    {A B : AffinoidAtlasPresentation.{u, v, v} K} (g : ofSaturation A ⟶ ofSaturation B)
    (y : A.space) (hg : StrongHom.IsFiniteAt (A := A) (B := B) g y) :
    Nonempty (FinitePointWitness ((loc).map g) y) := by
  obtain ⟨V, W, hVW, s, hs, hfin⟩ := hg.hasFiniteFullRecognitionPairAt
  let f := g.fullRecognitionPairs.pullback V W hVW
  let t := comap f.toBoundedRingHom s
  let a := localizedQuasiIso (StrongHom.localDomainToFullRecognitionHom A)
    A.localDomainToFullRecognition_isQuasiIso
  let b := localizedQuasiIso (StrongHom.localDomainToFullRecognitionHom B)
    B.localDomainToFullRecognition_isQuasiIso
  let D : ResidueChart ((loc).obj (ofSaturation A)) := ⟨ofFullRecognition A, a.symm, V, s⟩
  let C : ResidueChart ((loc).obj (ofSaturation B)) := ⟨ofFullRecognition B, b.symm, W, t⟩
  let i : BoundedAlgHom K C.Field D.Field := completedResidueComap K f s
  have hi : Isometry i := isometry_completedResidueComap K f s
  let q := D.realization
  have hqA : q.map A.localDomainToFullRecognition A.atlas.saturatedAtlas_hasAllLocalDomains =
      D.chartRealization := D.realization_onChart
  have hqy : FieldPoint.point (A := A.saturatedPresentation) (L := D.Field) q = y :=
    (congrArg FieldPoint.point hqA).trans (D.chartRealization_point.trans hs)
  refine ⟨⟨C, V.algebra, s, i, hi, ?_, q, hqy, ?_⟩⟩
  · let : Algebra C.Field D.Field := i.toAlgHom.toRingHom.toAlgebra
    let : Module.Finite C.Field D.Field := finite_completedResidueComap K f hfin.finite s
    exact Algebra.IsAlgebraic.of_finite C.Field D.Field
  let q' : FieldPoint D.Field B.fullRecognitionPresentation :=
    q.map g.toFullRecognitionTarget A.atlas.saturatedAtlas_hasAllLocalDomains
  have hqq' : (Φ D.Field).map b.hom ((Φ D.Field).map ((loc).map g) q) = q' :=
    (q.map_saturatedComp g B.localDomainToFullRecognition
      A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains).symm
  have hqt : q'.point = W.chart t :=
    (congrArg g.baseMap hqy).trans ((congrArg g.baseMap hs).symm.trans
      (g.fullRecognitionPairs.chart_comm V W hVW s).symm)
  have hqV : (FieldPoint.point (A := A.saturatedPresentation) (L := D.Field) q) ∈
      Set.range V.chart := ⟨s, hs.trans hqy.symm⟩
  have hDV : D.chartRealization.point ∈ Set.range V.chart := ⟨s, D.chartRealization_point.symm⟩
  have hqW : q'.point ∈ Set.range W.chart := ⟨t, hqt.symm⟩
  have hCW : C.chartRealization.point ∈ Set.range W.chart := ⟨t, C.chartRealization_point.symm⟩
  let p : FieldPoint D.Field B.fullRecognitionPresentation :=
    changeValues (X := (loc).obj (ofFullRecognition B)) i hi C.chartRealization
  have hp : q'.point = p.point := hqt.trans C.chartRealization_point.symm
  have hqC : q' = p := by
    refine FieldPoint.eq_of_eval_eq (p := q') (q := p)
      PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity hp W hqW hCW ?_
    have hD : D.chartRealization.eval V hDV = (completedResidueMap K s).toAlgHom :=
      D.chartRealization_eval hDV
    have hC : C.chartRealization.eval W hCW = (completedResidueMap K t).toAlgHom :=
      C.chartRealization_eval hCW
    have h0 := q.map_toFullRecognitionTarget_eval g V W hVW hqV hqW
    have h1 := (FieldPoint.eval_congr hqA V hqV hDV).trans hD
    have h2 : (completedResidueMap K s).toAlgHom.comp f.toAlgHom =
        i.toAlgHom.comp (completedResidueMap K t).toAlgHom :=
      AlgHom.ext fun r => (completedResidueComap_map K f s r).symm
    exact h0.trans ((congrArg (fun ev => ev.comp f.toAlgHom) h1).trans
      (h2.trans (congrArg (fun ev => i.toAlgHom.comp ev) hC).symm))
  apply (CategoryTheory.Iso.toEquiv ((Φ D.Field).mapIso b)).injective
  change (Φ D.Field).map b.hom ((Φ D.Field).map ((loc).map g) q) =
    (Φ D.Field).map b.hom (changeValues i hi C.realization)
  exact hqq'.trans (hqC.trans
    ((congrArg (changeValues (X := (loc).obj (ofFullRecognition B)) i hi)
      C.realization_onChart.symm).trans (changeValues_naturality b.hom i hi C.realization).symm))

namespace FinitePointWitness

variable {T Y X Z : LocalizedCategory.{u, v, v} (K := K)}
  {f : Y ⟶ X} {j : T ⟶ Y} {y : localizedSpaceFunctor.obj Y}
  {t : localizedSpaceFunctor.obj T}

private abbrev Field (h : FinitePointWitness f y) := CompletedResidueField K h.z

/-- The witness can be restricted along an arrow with pointed lifts for its field. -/
private theorem precomp (h : FinitePointWitness f (localizedSpaceFunctor.map j t))
    (hj : PointedFieldPointLift h.Field j) : Nonempty (FinitePointWitness (j ≫ f) t) := by
  obtain ⟨q, hq, hqj⟩ := hj h.lift t h.lift_point.symm
  refine ⟨⟨h.chart, h.sourceAlgebra, h.z, h.embed, h.isometry_embed, h.algebraic_embed,
    q, hq, ?_⟩⟩
  exact ((Φ h.Field).map_comp_apply j f q).trans
    ((congrArg ((Φ h.Field).map f) hqj).trans h.lift_map)

private def pushSource (h : FinitePointWitness (j ≫ f) t) :
    FinitePointWitness f (localizedSpaceFunctor.map j t) where
  chart := h.chart
  sourceAlgebra := h.sourceAlgebra
  z := h.z
  embed := h.embed
  isometry_embed := h.isometry_embed
  algebraic_embed := h.algebraic_embed
  lift := (Φ h.Field).map j h.lift
  lift_point := (localizedFieldPointProjection_map_down j h.lift).trans
    (congrArg (localizedSpaceFunctor.map j) h.lift_point)
  lift_map := ((Φ h.Field).map_comp_apply j f h.lift).symm.trans h.lift_map

private def postcompIso (h : FinitePointWitness f y) (e : X ≅ Z) :
    FinitePointWitness (f ≫ e.hom) y where
  chart := h.chart.transport e
  sourceAlgebra := h.sourceAlgebra
  z := h.z
  embed := h.embed
  isometry_embed := h.isometry_embed
  algebraic_embed := h.algebraic_embed
  lift := h.lift
  lift_point := h.lift_point
  lift_map := ((Φ h.Field).map_comp_apply f e.hom h.lift).trans
    ((congrArg ((Φ h.Field).map e.hom) h.lift_map).trans
      ((changeValues_naturality e.hom h.embed h.isometry_embed h.chart.realization).trans
        (congrArg (changeValues h.embed h.isometry_embed)
          (h.chart.realization_transport e).symm)))

end FinitePointWitness

private theorem finitePointWitness_of_etale
    {Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Y ⟶ X} (hf : etale f)
    (y : localizedSpaceFunctor.obj Y) : Nonempty (FinitePointWitness f y) := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let a : (loc).obj (ofSaturation A) ≅ Y := Arrow.leftFunc.mapIso e
  let b : (loc).obj (ofSaturation B) ≅ X := Arrow.rightFunc.mapIso e
  let y' := localizedSpaceFunctor.map a.inv y
  obtain ⟨h⟩ := finitePointWitness_localizationFunctor_map_of_finiteAt g y'
    (hg.isEtale.isQuasifinite y')
  have hs : a.hom ≫ f = (loc).map g ≫ b.hom := e.hom.w
  have he : a.inv ≫ ((loc).map g ≫ b.hom) = f := by
    rw [← hs, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (h.postcompIso b).precomp (pointedFieldPointLift_of_isIso a.inv)

private theorem finitePointWitness_of_quasiEtale
    {Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Y ⟶ X} (hf : quasiEtale f)
    (y : localizedSpaceFunctor.obj Y) : Nonempty (FinitePointWitness f y) := by
  let S := presentationOf Y
  obtain ⟨σ, -, hn, hσ⟩ := isLocalizedQuasiEtaleAt_of_quasiEtale (S := S) hf y
  obtain ⟨V, hV, hy⟩ := Set.mem_sUnion.mp (mem_of_mem_nhds hn)
  obtain ⟨i, hi, W, w, j, hw, hj, hjw⟩ := hσ V hV
  let D := S.chartDomain i
  have hyD : y ∈ D.carrier := by
    rw [chartDomain_carrier, hi]
    exact hy
  let d : localizedSpaceFunctor.obj (domainObj Y D) := (⟨y, hyD⟩ : D.carrier)
  have hd : localizedSpaceFunctor.map (domainι Y D) d = y := domainι_apply D d
  obtain ⟨h⟩ := finitePointWitness_of_etale hw (localizedSpaceFunctor.map j d)
  obtain ⟨h'⟩ := h.precomp (pointedFieldPointLift_of_isAffinoidDomainEmbedding hj)
  have h'' : FinitePointWitness (domainι Y D ≫ f) d := hjw ▸ h'
  exact ⟨hd ▸ h''.pushSource⟩

section CompareFields

variable {Y U X : LocalizedCategory.{u, v, v} (K := K)}
  {f : Y ⟶ U} {g : U ⟶ X}
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L]

set_option maxHeartbeats 800000 in
/-- Compare the intermediate residue field with the two ends of the witness. The resulting
algebraic extension allows the prescribed embedding into `L` to be extended. -/
private theorem FinitePointWitness.lift_prescribed {y : localizedSpaceFunctor.obj Y}
    (h : FinitePointWitness (f ≫ g) y) (p : (Φ L).obj U)
    (hy : localizedSpaceFunctor.map f y = ((π L).app U p).down) :
    ∃ q : (Φ L).obj Y, ((π L).app Y q).down = y ∧ (Φ L).map f q = p := by
  let M := h.Field
  let pM := (Φ M).map f h.lift
  have hpM : ((π M).app U pM).down = ((π L).app U p).down :=
    (localizedFieldPointProjection_map_down f h.lift).trans
      ((congrArg (localizedSpaceFunctor.map f) h.lift_point).trans hy)
  obtain ⟨D, hD⟩ := ResidueChart.exists_at (((π L).app U p).down)
  obtain ⟨a, ha, hae⟩ := D.exists_lift pM (hpM.trans hD.symm)
  obtain ⟨b, hb, hbe⟩ := D.exists_lift p hD.symm
  let r := (Φ D.Field).map g D.realization
  have hr : changeValues a ha r = changeValues h.embed h.isometry_embed h.chart.realization :=
    (changeValues_naturality g a ha D.realization).symm.trans
      ((congrArg ((Φ M).map g) hae).trans
        (((Φ M).map_comp_apply f g h.lift).symm.trans h.lift_map))
  have hrp : ((π D.Field).app X r).down = h.chart.point :=
    (congrArg (fun q => ((π M).app X q).down) hr).trans h.chart.realization_point
  obtain ⟨c, hc, hce⟩ := h.chart.exists_lift r hrp
  have hac : a.comp c = h.embed := h.chart.lift_unique (ha.comp hc) h.isometry_embed
    ((changeValues_comp c hc a ha _).symm.trans
      ((congrArg (changeValues a ha) hce).trans hr))
  let : NormedAlgebra D.Field M :=
    { toAlgebra := a.toAlgHom.toRingHom.toAlgebra
      norm_smul_le := fun x z => by
        change ‖a x * z‖ ≤ ‖x‖ * ‖z‖
        rw [norm_mul, ha.norm_map_of_map_zero (map_zero _) x] }
  let : IsScalarTower K D.Field M :=
    IsScalarTower.of_algebraMap_eq fun k => (a.toAlgHom.commutes k).symm
  let E := h.chart.Field
  let : Algebra E D.Field := c.toAlgHom.toRingHom.toAlgebra
  let : Algebra E M := h.embed.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower E D.Field M := IsScalarTower.of_algebraMap_eq fun e =>
    congrArg (fun i : BoundedAlgHom K E M => i e) hac.symm
  let : Algebra.IsAlgebraic E M := h.algebraic_embed
  let : Algebra.IsAlgebraic D.Field M := Algebra.IsAlgebraic.tower_top (K := E) D.Field
  obtain ⟨j, hj, hjb⟩ := exists_isometric_algebraic_extension (F := M) b.toAlgHom hb
  have hjb' : j.comp a = b := BoundedAlgHom.ext hjb
  refine ⟨changeValues j hj h.lift, (changeValues_point j hj h.lift).trans h.lift_point, ?_⟩
  calc
    _ = changeValues j hj pM := changeValues_naturality f j hj h.lift
    _ = changeValues j hj (changeValues a ha D.realization) := congrArg (changeValues j hj) hae.symm
    _ = changeValues (j.comp a) (hj.comp ha) D.realization := changeValues_comp a ha j hj _
    _ = p := by
      subst b
      exact hbe

/-- An arrow with quasi-étale composite lifts a full `L`-valued point at every ordinary
preimage. The argument does not use a quasi-étale cancellation theorem. -/
theorem pointedFieldPointLift_of_quasiEtale_comp (h : quasiEtale (f ≫ g)) :
    PointedFieldPointLift L f := by
  intro p y hy
  obtain ⟨w⟩ := finitePointWitness_of_quasiEtale h y
  exact w.lift_prescribed p hy

end CompareFields

namespace QuasiEtaleSite

/-- The full point of a quasi-étale site object lifts along a site arrow whenever its
ordinary point lies in the image. -/
theorem geometricPointImageLift : GeometricPointImageLiftStatement.{u, v, uL} := by
  intro K _ _ _ L _ _ _ _ _ X U V f p hp
  obtain ⟨y, hy⟩ := hp
  have hf : quasiEtale (f.left ≫ U.hom) := (MorphismProperty.Over.w f).symm ▸ V.prop
  obtain ⟨q, -, hq⟩ := pointedFieldPointLift_of_quasiEtale_comp hf p y hy
  exact ⟨q, hq⟩

end QuasiEtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
