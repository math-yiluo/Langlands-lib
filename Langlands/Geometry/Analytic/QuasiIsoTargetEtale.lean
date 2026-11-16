import Langlands.Geometry.Analytic.QuasiIsoSourceEtale

/-! # Target transport of finite pieces along quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

section TargetTransport

variable {f : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  (hg : g.IsQuasiIso)

include hg in
/-- Injectivity of the second map identifies the inverse image of the
image of any subset with the original composite inverse-image locus. -/
theorem IsQuasiIso.comp_preimage_image (W : Set B.space) :
    (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' (g.baseMap '' W) =
        f.baseMap ⁻¹' W := by
  ext x
  constructor
  · rintro ⟨y, hy, h⟩
    change f.baseMap x ∈ W
    exact hg.1.injective h ▸ hy
  · intro hx
    exact ⟨f.baseMap x, hx, rfl⟩

/-- Recognized images give the same inverse-image locus for the composite. -/
theorem IsQuasiIso.comp_preimage_fullRecognitionImage
    (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹'
        (hg.fullRecognitionImage W).locus = f.baseMap ⁻¹' W.locus :=
  (congrArg (fun s : Set C.space =>
    (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' s)
    (hg.fullRecognitionImage_locus W)).trans
      (hg.comp_preimage_image (f := f) W.locus)

include hg in
/-- Finiteness descends along a target quasi-isomorphism by pulling the
target neighborhood back through its homeomorphism. -/
theorem IsFiniteOver.of_postcomp_quasiIso
    {V : Set A.space} {U : Set C.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V U) :
    f.IsFiniteOver V (g.baseMap ⁻¹' U) := by
  refine ⟨?_, fun W hW => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hfg.1 ⟨x, hx, rfl⟩
  · let Z := hg.fullRecognitionImage W
    let e := hg.fullRecognitionImageEquiv W
    have hWZ := hg.fullRecognitionImage_admissible W
    have hZ : Z.locus ⊆ U := by
      rw [hg.fullRecognitionImage_locus]
      rintro _ ⟨y, hy, rfl⟩
      exact hW hy
    obtain ⟨P, hPZ, hP, hfin⟩ := hfg.2 Z hZ
    have hPWl : P.locus = V ∩ f.baseMap ⁻¹' W.locus := by
      exact hP.trans (congrArg (fun s : Set A.space => V ∩ s)
        (hg.comp_preimage_fullRecognitionImage (f := f) W))
    have hPW : f.baseMap '' Set.range P.chart ⊆ Set.range W.chart := by
      change f.originalRestriction.baseMap '' Set.range P.chart ⊆ Set.range W.chart
      rw [P.range_chart, W.range_chart]
      rintro _ ⟨x, hx, rfl⟩
      exact (hPWl ▸ hx).2
    refine ⟨P, hPW, hPWl, ?_⟩
    have heq :
        ((f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
          B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
            P Z hPZ).comp e.symm.toBoundedAlgHom =
              f.fullRecognitionPairs.pullback P W hPW := by
      rw [fullRecognitionPairs_comp f g P W Z hPW hWZ hPZ]
      apply BoundedAlgHom.ext
      intro z
      exact congrArg (f.fullRecognitionPairs.pullback P W hPW) (e.apply_symm_apply z)
    exact heq ▸ hfin.comp e.symm.isFiniteBanach

include hg in
/-- Conditions on every finite piece descend through a target
quasi-isomorphism when they compose and hold for bounded equivalences. -/
theorem HasAllPiecesAt.of_postcomp_quasiIso
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
    f.HasAllPiecesAt Q x := by
  obtain ⟨V, U, hV, hU, hx, hfin, hQ⟩ := hfg
  refine ⟨V, g.baseMap ⁻¹' U, hV, hU.preimage g.baseMap.continuous, hx,
    hfin.of_postcomp_quasiIso hg, ?_⟩
  intro W hW hxW P hPW hP t ht
  let Z := hg.fullRecognitionImage W
  let e := hg.fullRecognitionImageEquiv W
  have hWZ := hg.fullRecognitionImage_admissible W
  have hZ : Z.locus ⊆ U := by
    rw [hg.fullRecognitionImage_locus]
    rintro _ ⟨y, hy, rfl⟩
    exact hW hy
  have hxZ : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap x ∈ Z.locus := by
    rw [hg.fullRecognitionImage_locus]
    exact ⟨f.baseMap x, hxW, rfl⟩
  have hPZ : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap '' Set.range P.chart ⊆
        Set.range Z.chart := by
    rintro _ ⟨y, hy, rfl⟩
    exact hWZ ⟨f.baseMap y, hPW ⟨y, hy, rfl⟩, rfl⟩
  have hPl : P.locus = V ∩ (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' Z.locus := by
    exact hP.trans (congrArg (fun s : Set A.space => V ∩ s)
      (hg.comp_preimage_fullRecognitionImage (f := f) W)).symm
  obtain ⟨P', hP'Z, hP'l, hP'fin⟩ := hfin.2 Z hZ
  have hPP : P' = P := by
    apply Subtype.ext
    apply Subtype.ext
    change P'.locus = P.locus
    exact hP'l.trans hPl.symm
  subst P'
  have heq :
      ((f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
          P Z hPZ).comp e.symm.toBoundedAlgHom =
            f.fullRecognitionPairs.pullback P W hPW := by
    rw [fullRecognitionPairs_comp f g P W Z hPW hWZ hPZ]
    apply BoundedAlgHom.ext
    intro z
    exact congrArg (f.fullRecognitionPairs.pullback P W hPW) (e.apply_symm_apply z)
  have hQt := hQ Z hZ hxZ P hPZ hPl t ht
  have hres := hcomp _ e.symm.toBoundedAlgHom t hP'fin.finite.finiteType
    e.symm.isFiniteBanach.finite.finiteType hQt (he e.symm _)
  exact (congrArg (fun q => Q q t) heq).mp hres

include hg in
/-- Flatness over all pieces descends through a target quasi-isomorphism. -/
theorem IsFlatAtAllPieces.of_postcomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFlatAtAllPieces x) :
    f.IsFlatAtAllPieces x :=
  HasAllPiecesAt.of_postcomp_quasiIso hg
    (Q := fun _ _ a t => a.IsFlatAtPoint t)
    (fun _ _ _ _ _ _ _ _ ha hb => ha.comp hb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).1) hfg

include hg in
/-- Unramifiedness over all pieces descends through a target quasi-isomorphism. -/
theorem IsUnramifiedAtAllPieces.of_postcomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsUnramifiedAtAllPieces x) :
    f.IsUnramifiedAtAllPieces x :=
  HasAllPiecesAt.of_postcomp_quasiIso hg
    (Q := fun _ _ a t => a.IsUnramifiedAtPoint t)
    (fun _ _ _ _ _ _ ha hb hQa hQb => BoundedAlgHom.IsUnramifiedAtPoint.comp ha hb hQa hQb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).2) hfg

include hg in
/-- The same open étale source neighborhood works after target descent. -/
theorem IsEtaleAtAllPieces.of_postcomp_quasiIso {x : A.space}
    (hfg : (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces x) :
    f.IsEtaleAtAllPieces x := by
  obtain ⟨V, hV, hx, hQ⟩ := hfg
  exact ⟨V, hV, hx, fun a ha =>
    ⟨(hQ a ha).1.of_postcomp_quasiIso hg, (hQ a ha).2.of_postcomp_quasiIso hg⟩⟩

include hg in
/-- Étaleness on all recognized pieces is unchanged by postcomposition
with a full target quasi-isomorphism. -/
theorem isEtaleAllPieces_postcomp_quasiIso_iff :
    (f.saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces ↔ f.IsEtaleAllPieces := by
  constructor
  · intro hfg x
    exact (hfg x).of_postcomp_quasiIso hg
  · intro hf
    exact hf.comp hg.isEtaleAllPieces

end TargetTransport
end AffinoidAtlasPresentation.StrongHom
end Langlands.Analytic
