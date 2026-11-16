import Langlands.Geometry.Analytic.QuasiIsoEtaleTransport

/-! # Source transport of finite pieces along quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace BoundedAlgEquiv

variable {R S : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
/-- A bounded algebra equivalence is a finite Banach map. -/
theorem isFiniteBanach (e : BoundedAlgEquiv K R S) : e.toBoundedAlgHom.IsFiniteBanach := by
  obtain ⟨M, hM, hb⟩ := e.symm.bounded
  refine BoundedAlgHom.isFiniteBanach_of_lift _ hM fun z => ?_
  exact ⟨e.symm z, e.apply_symm_apply z, hb z⟩

end BoundedAlgEquiv

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace IsQuasiIso

variable {f : StrongHom A.saturatedPresentation B.saturatedPresentation}
  (hf : f.IsQuasiIso)

/-- The actual recognized image for a map between constructed saturations. -/
def fullRecognitionImage (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    B.atlas.saturatedAtlas.RecognizedSubset :=
  (hf.originalRestriction (A := A) (B := B)).recognizedImage
    f.originalRestriction.coherent V

theorem fullRecognitionImage_locus (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.fullRecognitionImage V).locus = f.baseMap '' V.locus :=
  (hf.originalRestriction (A := A) (B := B)).recognizedImage_locus
    f.originalRestriction.coherent V

theorem fullRecognitionImage_admissible (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    f.baseMap '' Set.range V.chart ⊆ Set.range (hf.fullRecognitionImage V).chart := by
  exact (Set.image_mono V.range_chart.subset).trans
    ((hf.fullRecognitionImage_locus V).symm.subset.trans
      (hf.fullRecognitionImage V).range_chart.superset)

/-- The image comparison is the actual forward pair-system pullback. -/
def fullRecognitionImageEquiv (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K (hf.fullRecognitionImage V).algebra V.algebra :=
  hf.fullRecognitionPairEquiv V (hf.fullRecognitionImage V)
    (hf.fullRecognitionImage_admissible V)
    (hf.fullRecognitionImage_locus V).symm.subset (by
      apply Set.eq_univ_of_forall
      intro x
      change (hf.fullRecognitionImage V).chart x ∈ f.baseMap '' V.locus
      exact (hf.fullRecognitionImage_locus V) ▸
        ((hf.fullRecognitionImage V).range_chart ▸ Set.mem_range_self x))

theorem fullRecognitionImageEquiv_toBoundedAlgHom
    (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    (hf.fullRecognitionImageEquiv V).toBoundedAlgHom =
      f.fullRecognitionPairs.pullback V (hf.fullRecognitionImage V)
        (hf.fullRecognitionImage_admissible V) :=
  hf.fullRecognitionPairEquiv_toBoundedAlgHom _ _ _ _ _

/-- Image under a homeomorphism carries the restricted inverse-image locus
of a composite to the corresponding locus for the second map. -/
theorem image_inter_comp_preimage
    (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : Set A.space) (U : Set C.space) :
    f.baseMap '' (V ∩ (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' U) =
        (f.baseMap '' V) ∩ g.baseMap ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hU⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hU⟩
  · rintro ⟨⟨x, hx, rfl⟩, hU⟩
    exact ⟨x, ⟨hx, hU⟩, rfl⟩

end IsQuasiIso

section SourceTransport

variable {f : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  (hf : f.IsQuasiIso)

include hf in
/-- Finiteness over a neighborhood descends along a full source
quasi-isomorphism, with the source neighborhood transported by its image. -/
theorem IsFiniteOver.of_precomp_quasiIso
    {V : Set A.space} {U : Set C.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V U) :
    g.IsFiniteOver (f.baseMap '' V) U := by
  refine ⟨?_, fun Z hZ => ?_⟩
  · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact hfg.1 ⟨x, hx, rfl⟩
  · obtain ⟨P, hPZ, hP, hfin⟩ := hfg.2 Z hZ
    let Y := hf.fullRecognitionImage P
    let e := hf.fullRecognitionImageEquiv P
    have hPY := hf.fullRecognitionImage_admissible P
    have hY : Y.locus = (f.baseMap '' V) ∩ g.baseMap ⁻¹' Z.locus := by
      rw [hf.fullRecognitionImage_locus, hP]
      exact IsQuasiIso.image_inter_comp_preimage (f := f) g V Z.locus
    have hYZ : g.baseMap '' Set.range Y.chart ⊆ Set.range Z.chart := by
      change g.originalRestriction.baseMap '' Set.range Y.chart ⊆ Set.range Z.chart
      rw [Y.range_chart, Z.range_chart]
      rintro _ ⟨y, hy, rfl⟩
      exact (hY ▸ hy).2
    refine ⟨Y, hYZ, hY, ?_⟩
    have heq : e.symm.toBoundedAlgHom.comp
        ((f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
          B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
            P Z hPZ) = g.fullRecognitionPairs.pullback Y Z hYZ := by
      rw [fullRecognitionPairs_comp f g P Y Z hPY hYZ hPZ]
      apply BoundedAlgHom.ext
      intro z
      exact e.symm_apply_apply _
    exact heq ▸ e.symm.isFiniteBanach.comp hfin

include hf in
/-- Pointwise conditions on every finite piece descend through a source
quasi-isomorphism when they compose and hold for bounded equivalences. -/
theorem HasAllPiecesAt.of_precomp_quasiIso
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hcomp : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄ (a : BoundedAlgHom K S T)
      (b : BoundedAlgHom K R S) (t : BanachSpectrum T),
      a.toAlgHom.toRingHom.FiniteType → b.toAlgHom.toRingHom.FiniteType →
        Q a t → Q b (BanachSpectrum.comap a.toBoundedRingHom t) → Q (a.comp b) t)
    (he : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄ (e : BoundedAlgEquiv K R S)
      (t : BanachSpectrum S), Q e.toBoundedAlgHom t)
    {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).HasAllPiecesAt Q x) :
    g.HasAllPiecesAt Q (f.baseMap x) := by
  obtain ⟨V, U, hV, hU, hx, hfin, hQ⟩ := hfg
  refine ⟨f.baseMap '' V, U, hf.1.homeomorph.isOpenMap V hV, hU, ⟨x, hx, rfl⟩,
    hfin.of_precomp_quasiIso hf, ?_⟩
  intro Z hZ hxZ W hWZ hW t ht
  obtain ⟨P, hPZ, hP, hPfin⟩ := hfin.2 Z hZ
  let Y := hf.fullRecognitionImage P
  let e := hf.fullRecognitionImageEquiv P
  have hPY := hf.fullRecognitionImage_admissible P
  have hY : Y.locus = (f.baseMap '' V) ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hf.fullRecognitionImage_locus, hP]
    exact IsQuasiIso.image_inter_comp_preimage (f := f) g V Z.locus
  have hWY : W = Y := by
    apply Subtype.ext
    apply Subtype.ext
    change W.locus = Y.locus
    exact hW.trans hY.symm
  subst W
  have heq : e.symm.toBoundedAlgHom.comp
      ((f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
          P Z hPZ) = g.fullRecognitionPairs.pullback Y Z hWZ := by
    rw [fullRecognitionPairs_comp f g P Y Z hPY hWZ hPZ]
    apply BoundedAlgHom.ext
    intro z
    exact e.symm_apply_apply _
  let s := e.spectrumHomeomorph.symm t
  have hst : BanachSpectrum.comap
      (f.fullRecognitionPairs.pullback P Y hPY).toBoundedRingHom s = t := by
    change e.spectrumHomeomorph (e.spectrumHomeomorph.symm t) = t
    exact e.spectrumHomeomorph.apply_symm_apply t
  have hs : P.chart s = x := by
    apply hf.1.injective
    exact (f.fullRecognitionPairs.chart_comm P Y hPY s).symm.trans
      ((congrArg Y.chart hst).trans ht)
  have hQt := hQ Z hZ hxZ P hPZ hP s hs
  have hres := hcomp e.symm.toBoundedAlgHom _ t
    e.symm.isFiniteBanach.finite.finiteType hPfin.finite.finiteType (he e.symm t) hQt
  exact (congrArg (fun q => Q q t) heq).mp hres

include hf in
/-- Flatness over all pieces descends along a source quasi-isomorphism. -/
theorem IsFlatAtAllPieces.of_precomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFlatAtAllPieces x) :
    g.IsFlatAtAllPieces (f.baseMap x) :=
  HasAllPiecesAt.of_precomp_quasiIso hf
    (Q := fun _ _ a t => a.IsFlatAtPoint t)
    (fun _ _ _ _ _ _ _ _ ha hb => ha.comp hb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).1) hfg

include hf in
/-- Unramifiedness over all pieces descends along a source quasi-isomorphism. -/
theorem IsUnramifiedAtAllPieces.of_precomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsUnramifiedAtAllPieces x) :
    g.IsUnramifiedAtAllPieces (f.baseMap x) :=
  HasAllPiecesAt.of_precomp_quasiIso hf
    (Q := fun _ _ a t => a.IsUnramifiedAtPoint t)
    (fun _ _ _ _ _ _ ha hb hQa hQb => BoundedAlgHom.IsUnramifiedAtPoint.comp ha hb hQa hQb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).2) hfg

include hf in
/-- An étale neighborhood descends to the homeomorphic source image. -/
theorem IsEtaleAtAllPieces.of_precomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces x) :
    g.IsEtaleAtAllPieces (f.baseMap x) := by
  obtain ⟨V, hV, hx, hQ⟩ := hfg
  refine ⟨f.baseMap '' V, hf.1.homeomorph.isOpenMap V hV, ⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨(hQ a ha).1.of_precomp_quasiIso hf, (hQ a ha).2.of_precomp_quasiIso hf⟩

include hf in
/-- Étaleness on all recognized pieces is unchanged by precomposition
with a full source quasi-isomorphism. -/
theorem isEtaleAllPieces_precomp_quasiIso_iff :
    (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces ↔ g.IsEtaleAllPieces := by
  constructor
  · intro hfg y
    obtain ⟨x, rfl⟩ := hf.1.surjective y
    exact (hfg x).of_precomp_quasiIso hf
  · intro hg
    exact hf.isEtaleAllPieces.comp hg

end SourceTransport
end AffinoidAtlasPresentation.StrongHom
end Langlands.Analytic
