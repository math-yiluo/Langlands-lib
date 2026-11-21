import Langlands.Geometry.Analytic.FieldPointValueChange
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.FullRecognitionFiniteFieldPointLifting
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof

/-! # Finiteness of full geometric fibres of étale maps -/

noncomputable section

universe u v uL

namespace Langlands.Analytic

open _root_.CategoryTheory Set Filter Topology AffinoidAtlasPresentation PresentedAffinoidAlgebra
open scoped TensorProduct Topology

private theorem finite_algHom_of_moduleFinite
    (B C M : Type*) [CommRing B] [CommRing C] [Field M]
    [Algebra B C] [Algebra B M] [Module.Finite B C] : Finite (C →ₐ[B] M) := by
  let T := M ⊗[B] C
  let : IsArtinianRing T := IsArtinianRing.of_finite M T
  let e : (C →ₐ[B] M) ≃ (T →ₐ[M] M) := AlgHom.liftEquiv B M C M
  let F (f : C →ₐ[B] M) : PrimeSpectrum T := ⟨RingHom.ker (e f).toRingHom, RingHom.ker_isPrime _⟩
  apply Finite.of_injective F
  intro f g hfg
  have hker : RingHom.ker (e f).toRingHom = RingHom.ker (e g).toRingHom :=
    congrArg PrimeSpectrum.asIdeal hfg
  apply e.injective
  apply AlgHom.ext
  intro a
  let b := a - algebraMap M T (e f a)
  have hb : b ∈ RingHom.ker (e f).toRingHom := by
    change e f b = 0
    rw [show b = a - algebraMap M T (e f a) from rfl, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self_apply, sub_self]
  have hg : b ∈ RingHom.ker (e g).toRingHom := hker ▸ hb
  change e g b = 0 at hg
  rw [show b = a - algebraMap M T (e f a) from rfl, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self_apply, sub_eq_zero] at hg
  exact hg.symm

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {A B : AffinoidAtlasPresentation.{u, v, v} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

private theorem IsFiniteOver.finite_recognizedGeometricFibre
    {V : Set A.space} {W : Set B.space} (hf : g.IsFiniteOver V W)
    (r : FieldPoint L B.saturatedPresentation) (U : B.atlas.saturatedAtlas.RecognizedSubset)
    (hU : U.locus ⊆ W) (hr : r.point ∈ U.locus) :
    {q : FieldPoint L A.saturatedPresentation |
      q.point ∈ V ∧ q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r}.Finite := by
  obtain ⟨P, h, hP, hfin⟩ := hf.2 U hU
  let f := g.fullRecognitionPairs.pullback P U h
  let : Algebra U.algebra P.algebra := f.toAlgHom.toRingHom.toAlgebra
  let : Module.Finite U.algebra P.algebra := hfin.finite
  let r' := r.map B.localDomainToFullRecognition B.atlas.saturatedAtlas_hasAllLocalDomains
  have hr' : r'.point ∈ range U.chart := U.range_chart.symm ▸ hr
  let : Algebra U.algebra L := (r'.eval U hr').toRingHom.toAlgebra
  let F : Set (FieldPoint L A.saturatedPresentation) := {q |
    q.point ∈ V ∧ q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r}
  let Q := ↥F
  let extend (q : Q) := q.val.map A.localDomainToFullRecognition A.atlas.saturatedAtlas_hasAllLocalDomains
  have hgpt (q : Q) : g.baseMap q.val.point = r.point := congrArg FieldPoint.point q.property.2
  have hq (q : Q) : (extend q).point ∈ range P.chart := by
    rw [P.range_chart, hP]
    exact ⟨q.property.1, (congrArg (fun z : B.space => z ∈ U.locus) (hgpt q)).mpr hr⟩
  let χ (q : Q) : P.algebra →ₐ[U.algebra] L :=
    { toRingHom := ((extend q).eval P (hq q)).toRingHom
      commutes' := fun a => by
        have hmap : q.val.map g.toFullRecognitionTarget A.atlas.saturatedAtlas_hasAllLocalDomains = r' :=
          (q.val.map_saturatedComp g B.localDomainToFullRecognition
            A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains).trans
            (congrArg (fun s => s.map B.localDomainToFullRecognition
              B.atlas.saturatedAtlas_hasAllLocalDomains) q.property.2)
        have hqU : g.baseMap q.val.point ∈ range U.chart := (hgpt q).symm ▸ hr'
        have hχ := q.val.map_toFullRecognitionTarget_eval g P U h (hq q) hqU
        have he : (r'.eval U hr') = ((extend q).eval P (hq q)).comp f.toAlgHom :=
          (FieldPoint.eval_congr hmap U hqU hr').symm.trans hχ
        exact (congrArg (fun θ : U.algebra →ₐ[K] L => θ a) he).symm }
  have : Finite (P.algebra →ₐ[U.algebra] L) := finite_algHom_of_moduleFinite U.algebra P.algebra L
  have hF : Finite Q := by
    apply Finite.of_injective χ
    intro q t hqt
    have he : (extend q).eval P (hq q) = (extend t).eval P (hq t) :=
      AlgHom.ext fun a => congrArg (fun θ : P.algebra →ₐ[U.algebra] L => θ a) hqt
    obtain ⟨x, hx, hxn⟩ := (extend q).isChartPoint P (hq q)
    obtain ⟨y, hy, hyn⟩ := (extend t).isChartPoint P (hq t)
    have hxy : x = y := BanachSpectrum.ext fun a =>
      (hxn a).symm.trans ((congrArg (fun θ : P.algebra →ₐ[K] L => ‖θ a‖) he).trans (hyn a))
    have hpt : (extend q).point = (extend t).point := hx.symm.trans ((congrArg P.chart hxy).trans hy)
    have hv := FieldPoint.eq_of_eval_eq domainCompletedResidueSurjectivity hpt P (hq q) (hq t) he
    exact Subtype.ext (FieldPoint.map_injective A.localDomainToFullRecognition_isQuasiIso
      A.fullRecognitionPresentation_hasAllLocalDomains A.atlas.saturatedAtlas_hasAllLocalDomains hv)
  exact @Set.toFinite _ F hF

/-- Full geometric fibres of strong étale maps are finite when the ordinary
fibre is compact. -/
theorem IsEtaleAllPieces.finite_geometricFibre_of_isCompact
    (hg : g.IsEtaleAllPieces) (r : FieldPoint L B.saturatedPresentation)
    (hcompact : IsCompact (g.baseMap ⁻¹' ({r.point} : Set B.space))) :
    Finite {q : FieldPoint L A.saturatedPresentation //
      q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r} := by
  classical
  let S : Set A.space := g.baseMap ⁻¹' ({r.point} : Set B.space)
  have hlocal (y : S) : ∃ V : Set A.space, IsOpen V ∧ y.val ∈ V ∧
      {q : FieldPoint L A.saturatedPresentation |
        q.point ∈ V ∧ q.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r}.Finite := by
    obtain ⟨V, W, hV, hW, hyV, hf⟩ := hg.isEtale.isQuasifinite y.val
    have hy : g.baseMap y.val = r.point := y.property
    have hrW : r.point ∈ W := hy ▸ hf.1 ⟨y.val, hyV, rfl⟩
    obtain ⟨I, _, hIW, hn⟩ := B.atlas.exists_finite_recognized_nhds_subset r.point W (hW.mem_nhds hrW)
    obtain ⟨U, hUI, hrU⟩ := mem_iUnion₂.mp (mem_of_mem_nhds hn)
    exact ⟨V, hV, hyV, hf.finite_recognizedGeometricFibre r U (hIW U hUI).2 hrU⟩
  choose V hV hyV hfinite using hlocal
  have hcover : S ⊆ ⋃ y : S, V y := fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨J, hJ⟩ := hcompact.elim_finite_subcover V hV hcover
  have hfin := J.finite_toSet.biUnion (fun (j : S) _ => hfinite j)
  apply Set.Finite.to_subtype
  refine hfin.subset ?_
  intro q hq
  have hqS : q.point ∈ S := congrArg FieldPoint.point hq
  obtain ⟨y, hy, hqy⟩ := mem_iUnion₂.mp (hJ hqS)
  exact mem_iUnion₂.mpr ⟨y, hy, ⟨hqy, hq⟩⟩

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}

/-- The full geometric fibre of an étale map over a full point is finite if
the ordinary fibre of its underlying point is compact. -/
def FiniteEtaleGeometricFibreStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (L : Type uL) [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
    {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
    (x : (localizedFieldPointFunctor L).obj X), etale p →
    IsCompact (localizedSpaceFunctor.map p ⁻¹' {((localizedFieldPointProjection L).app X x).down}) →
    Finite {q : (localizedFieldPointFunctor L).obj Y // (localizedFieldPointFunctor L).map p q = x}

theorem finiteEtaleGeometricFibre : FiniteEtaleGeometricFibreStatement.{u, v, uL} K := by
  intro L _ _ _ Y X p x hp hcompact
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hp
  let Y₀ := localizationFunctor.obj (ofSaturation A)
  let X₀ := localizationFunctor.obj (ofSaturation B)
  let a : Y₀ ≅ Y := Arrow.leftFunc.mapIso e
  let b : X₀ ≅ X := Arrow.rightFunc.mapIso e
  let aTop := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso a)
  let bTop := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso b)
  let Φ := localizedFieldPointFunctor (K := K) L
  let r := Φ.map b.inv x
  have hr : r.point = bTop.symm (((localizedFieldPointProjection L).app X x).down) :=
    localizedFieldPointProjection_down_naturality b.inv x
  let f : A.space → B.space := g.baseMap
  have hpoint (y : localizedSpaceFunctor.obj Y₀) : localizedSpaceFunctor.map p (aTop y) = bTop (f y) := by
    have hw : a.hom ≫ p = localizationFunctor.map g ≫ b.hom := e.hom.w
    have h := congrArg (fun φ : Y₀ ⟶ X => localizedSpaceFunctor.map φ y) hw
    rw [localizedSpaceFunctor.map_comp, localizedSpaceFunctor.map_comp,
      TopCat.comp_app, TopCat.comp_app, localizedSpaceFunctor_map] at h
    exact h
  have hrTop : bTop r.point = ((localizedFieldPointProjection L).app X x).down :=
    (congrArg bTop hr).trans (bTop.apply_symm_apply _)
  have hset : f ⁻¹' ({r.point} : Set B.space) = aTop ⁻¹'
      (localizedSpaceFunctor.map p ⁻¹' {((localizedFieldPointProjection L).app X x).down}) := by
    ext y
    change f y = r.point ↔ localizedSpaceFunctor.map p (aTop y) =
      ((localizedFieldPointProjection L).app X x).down
    constructor
    · intro h
      exact (hpoint y).trans ((congrArg bTop h).trans hrTop)
    · intro h
      exact bTop.injective ((hpoint y).symm.trans (h.trans hrTop.symm))
  have hrc : IsCompact (g.baseMap ⁻¹' ({r.point} : Set B.space)) := by
    exact hset.symm ▸ aTop.isCompact_preimage.mpr hcompact
  have hfin := hg.finite_geometricFibre_of_isCompact r hrc
  let F (q : {q : Φ.obj Y // Φ.map p q = x}) :
      {s : FieldPoint L A.saturatedPresentation // s.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r} :=
    ⟨Φ.map a.inv q.val, by
      change Φ.map (localizationFunctor.map g) (Φ.map a.inv q.val) = r
      rw [← Φ.map_comp_apply, show a.inv ≫ localizationFunctor.map g = p ≫ b.inv from e.inv.w,
        Φ.map_comp_apply]
      exact congrArg (fun t => Φ.map b.inv t) q.property⟩
  have : Finite {s : FieldPoint L A.saturatedPresentation //
      s.map g A.atlas.saturatedAtlas_hasAllLocalDomains = r} := hfin
  apply Finite.of_injective F
  intro q q' h
  apply Subtype.ext
  have hh := congrArg (fun s => Φ.map a.hom s.val) h
  change Φ.map a.hom (Φ.map a.inv q.val) = Φ.map a.hom (Φ.map a.inv q'.val) at hh
  simpa only [← Φ.map_comp_apply, a.inv_hom_id, Φ.map_id_apply] using hh

end SaturatedAtlasPresentation
end Langlands.Analytic
