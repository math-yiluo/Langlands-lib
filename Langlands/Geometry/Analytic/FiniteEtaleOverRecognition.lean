import Langlands.Geometry.Analytic.AffinoidEtaleLocus
import Langlands.Geometry.Analytic.AffinoidProductChartSystem
import Langlands.Geometry.Analytic.EtaleOpenMap.StrongOpen
import Langlands.Geometry.Analytic.FullRecognitionAllPiecesRestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.RecognizedNestedEtale
import Mathlib.RingTheory.RingHom.Surjective

/-! # Finite étale models of a strong étale morphism -/

noncomputable section

open scoped Topology

universe u v w

namespace Langlands.Analytic

open Set Filter PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace BoundedAlgHom

omit [CompleteSpace K] in
private theorem isEtaleAtPoint_of_postcomp_clopen
    {R S T : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K R S) (r : BoundedAlgHom K S T)
    (hft : f.toAlgHom.toRingHom.FiniteType)
    (hr : r.toAlgHom.toRingHom.Flat) (hs : Function.Surjective r)
    (z : BanachSpectrum T) (hz : (r.comp f).IsEtaleAtPoint z) :
    f.IsEtaleAtPoint (BanachSpectrum.comap r.toBoundedRingHom z) := by
  let y := BanachSpectrum.comap r.toBoundedRingHom z
  let p := y.kernel
  let q := z.kernel
  let Rₚ := Localization.AtPrime p
  let Rq := Localization.AtPrime q
  let e := Localization.localRingHom p q r.toAlgHom.toRingHom (r.kernel_comap z)
  have hf : e.Flat := hr.localRingHom q p (r.kernel_comap z)
  have hbij : Function.Bijective e := by
    refine ⟨?_, RingHom.surjective_localRingHom_of_surjective r.toAlgHom.toRingHom hs q⟩
    let : Algebra Rₚ Rq := e.toAlgebra
    have : Module.Flat Rₚ Rq := hf
    have : IsLocalHom (algebraMap Rₚ Rq) := inferInstanceAs (IsLocalHom e)
    have : Module.FaithfullyFlat Rₚ Rq := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra R T := (r.comp f).toAlgHom.toRingHom.toAlgebra
  let E : Rₚ ≃ₐ[R] Rq := AlgEquiv.ofBijective
    { e with
      commutes' := fun a => by
        change e (algebraMap S Rₚ (f a)) = algebraMap T Rq (r (f a))
        exact Localization.localRingHom_to_map p q r.toAlgHom.toRingHom (r.kernel_comap z) _ }
    hbij
  have hrt : r.toAlgHom.toRingHom.FiniteType := (RingHom.Finite.of_surjective _ hs).finiteType
  have : Module.Flat R Rq := ((r.comp f).isFlatAtPoint_iff_flat_atPrime z).1 hz.1
  have : Algebra.FormallyUnramified R Rq :=
    ((r.comp f).isUnramifiedAtPoint_iff_isUnramifiedAt (hrt.comp hft) z).1 hz.2
  exact ⟨(f.isFlatAtPoint_iff_flat_atPrime y).2 (Module.Flat.of_linearEquiv E.toLinearEquiv),
    (f.isUnramifiedAtPoint_iff_isUnramifiedAt hft y).2
      (Algebra.FormallyUnramified.of_equiv E.symm)⟩

/-- Pointwise étaleness on the bounded spectrum of a finite affinoid map
implies algebraic finite étaleness of the whole map. -/
theorem algebraicallyFiniteEtale_of_isEtaleAtPoint
    {R S : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K R S)
    (hf : f.toAlgHom.toRingHom.Finite) (h : ∀ s, f.IsEtaleAtPoint s) :
    f.AlgebraicallyFiniteEtale := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  have : Algebra.FiniteType R S := hf.finiteType
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp hf.finiteType
  refine ⟨hf, (Algebra.etaleLocus_eq_univ_iff_etale (R := R) (A := S)).mp ?_⟩
  have hpre := f.pointwiseEtaleLocus_eq_prime_preimage hf.finiteType
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (Algebra.isOpen_etaleLocus (R := R) (A := S)).isClosed_compl
  have htop : I = ⊤ := by
    by_contra hi
    obtain ⟨s, hs⟩ := exists_spectrum_kernel_of_proper_ideal S I hi
    have he : s ∈ f.pointwiseEtaleLocus := h s
    rw [hpre] at he
    have hn : s.primePoint ∈ (Algebra.etaleLocus R S)ᶜ := by
      rw [hI]
      exact hs
    exact hn he
  have hnil : (Algebra.etaleLocus R S)ᶜ = ∅ := by
    rw [hI]
    exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr htop
  simpa using congrArg (fun Z : Set (PrimeSpectrum S) => Zᶜ) hnil

end BoundedAlgHom

namespace AffinoidAtlasPresentation.StrongHom

open IndexedAffinoidAtlas

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

private theorem finitePair_isEtaleAtPoint
    (he : g.IsEtaleAllPieces) {V : Set A.space} {U : Set B.space}
    (hV : IsOpen V) (hf : g.IsFiniteOver V U)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U)
    (P : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range P.chart ⊆ range W.chart)
    (hP : P.locus = V ∩ g.baseMap ⁻¹' W.locus)
    (hfin : (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach)
    (s : BanachSpectrum P.algebra) :
    (g.fullRecognitionPairs.pullback P W h).IsEtaleAtPoint s := by
  let y := P.chart s
  have hy : y ∈ V ∩ g.baseMap ⁻¹' W.locus := by
    rw [← hP, ← P.range_chart]
    exact mem_range_self s
  obtain ⟨N, -, hyN, hN⟩ := he y
  have hlocal := hasAllPiecesAt_isEtaleAtPoint_iff.mpr (hN y hyN)
  obtain ⟨V', U', hV', hU', hy', hV'V, hf', he'⟩ :=
    hlocal.exists_small (fun _ _ _ r f z hr hs hft hq =>
      ⟨(r.isFlatAtPoint_of_flat hr z).comp hq.1,
        BoundedAlgHom.IsUnramifiedAtPoint.comp
          (RingHom.Finite.of_surjective _ hs).finiteType hft
          (r.isUnramifiedAtPoint_of_formallyUnramified
            (RingHom.FormallyUnramified.of_surjective hs) z) hq.2⟩)
      (hV.mem_nhds hy.1)
  have hxU' : g.baseMap y ∈ U' := hf'.1 ⟨y, hy', rfl⟩
  obtain ⟨I, _, hI, hIn⟩ :=
    B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U' (hU'.mem_nhds hxU')
  obtain ⟨Z, hZI, hxZ⟩ := mem_iUnion₂.mp (mem_of_mem_nhds hIn)
  have hxZchart : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart Z) :=
    Z.range_chart.symm ▸ hxZ
  have hxWchart : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart W) :=
    W.range_chart.symm ▸ hy.2
  obtain ⟨Z', hzinter, hxZ'⟩ := IndexedAffinoidAtlas.exists_chart_inter
    (a := B.atlas.fullRecognitionAtlas) hxZchart hxWchart
  change B.atlas.saturatedAtlas.RecognizedSubset at Z'
  change range Z'.chart ⊆ range Z.chart ∩ range W.chart at hzinter
  change g.baseMap y ∈ range Z'.chart at hxZ'
  rw [Z'.range_chart, Z.range_chart, W.range_chart] at hzinter
  rw [Z'.range_chart] at hxZ'
  have hzsub : Z'.locus ⊆ W.locus := hzinter.trans inter_subset_right
  have hzU' : Z'.locus ⊆ U' := hzinter.trans (inter_subset_left.trans (hI Z hZI).2)
  obtain ⟨Q, hQ, hQpre, hQfin⟩ := hf.2 Z' (hzsub.trans hWU)
  obtain ⟨Q', hQ', hQ'pre, -⟩ := hf'.2 Z' hzU'
  have hQQ' : Q'.locus = Q.locus ∩ V' := by
    rw [hQ'pre, hQpre]
    ext t
    exact ⟨fun ht => ⟨⟨hV'V ht.1, ht.2⟩, ht.1⟩, fun ht => ⟨ht.2, ht.1.2⟩⟩
  have hsub : Q'.locus ⊆ Q.locus := hQQ'.trans_subset inter_subset_left
  have hcl := Q'.isClopen_chart_preimage_of_eq_inter Q hV' hQQ'
  obtain ⟨hrflat, hrsurj⟩ := Q'.restriction_flat_and_surjective Q hsub hcl
  have hyQ' : y ∈ range Q'.chart := by
    rw [Q'.range_chart, hQ'pre]
    exact ⟨hy', hxZ'⟩
  obtain ⟨t, ht⟩ := hyQ'
  have het := he' Z' hzU' hxZ' Q' hQ' hQ'pre t ht
  have hQr : range Q'.chart ⊆ range Q.chart := by
    rw [Q'.range_chart, Q.range_chart]
    exact hsub
  have hr := g.fullRecognitionPairs.restriction_comm Q' Q Z' Z' hQr
    Subset.rfl hQ' hQ
  rw [B.fullRecognitionPresentation.atlas.restriction_id Z' Subset.rfl,
    BoundedAlgHom.comp_id] at hr
  rw [← hr] at het
  let q := BanachSpectrum.comap (Q'.restriction Q hsub).toBoundedRingHom t
  have hq : (g.fullRecognitionPairs.pullback Q Z' hQ).IsEtaleAtPoint q :=
    BoundedAlgHom.isEtaleAtPoint_of_postcomp_clopen _ _ hQfin.finite.finiteType hrflat hrsurj t het
  have hQP : Q.locus ⊆ P.locus := by
    rw [hP, hQpre]
    exact fun _ hz => ⟨hz.1, hzsub hz.2⟩
  have hpre : Q.locus = P.locus ∩ g.baseMap ⁻¹' Z'.locus := by
    rw [hP, hQpre]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1, hzsub hz.2⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  have hq' := (g.recognizedNested_isEtaleAtPoint_iff Domain.flatness
    AffinoidPushout.finiteTensorComparison P Q W Z' h hQ hzsub hQP hpre hfin q).mp hq
  have hqs : BanachSpectrum.comap (Q.restriction P hQP).toBoundedRingHom q = s := by
    apply P.isEmbedding_chart.injective
    exact (Q.chart_restriction P hQP q).trans
      ((Q'.chart_restriction Q hsub t).trans ht)
  exact hqs ▸ hq'

/-- Every finite open model of an étale strong morphism is finite étale
over the same open target. -/
theorem IsEtaleAllPieces.isFiniteEtaleOver
    (he : g.IsEtaleAllPieces) {V : Set A.space} {U : Set B.space}
    (hV : IsOpen V) (hf : g.IsFiniteOver V U) : g.IsFiniteEtaleOver V U := by
  refine ⟨hf.1, fun W hWU => ?_⟩
  obtain ⟨P, h, hP, hfin⟩ := hf.2 W hWU
  exact ⟨P, h, hP, hfin, BoundedAlgHom.algebraicallyFiniteEtale_of_isEtaleAtPoint _
    hfin.finite (finitePair_isEtaleAtPoint he hV hf W hWU P h hP hfin)⟩

/-- A strong étale map admits finite étale models around all source points. -/
def StrongEtaleLocallyFiniteEtaleStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation),
    g.IsEtaleAllPieces → ∀ y, g.IsLocallyFiniteEtaleAt y

theorem strongEtaleLocallyFiniteEtale :
    StrongEtaleLocallyFiniteEtaleStatement.{u, v, w} K := by
  intro A B g he y
  obtain ⟨N, -, hyN, hN⟩ := he y
  obtain ⟨V, U, hV, hU, hyV, hfin, -⟩ := (hN y hyN).2
  exact ⟨V, U, hV, hU, hyV, he.isFiniteEtaleOver hV hfin⟩

end AffinoidAtlasPresentation.StrongHom
end Langlands.Analytic
