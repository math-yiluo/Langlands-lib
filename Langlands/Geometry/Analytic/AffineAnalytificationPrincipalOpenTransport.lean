import Langlands.Geometry.Analytic.AffineAnalytificationLocalDomainMaps
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.DirectedQuasiIsoInverses
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.RecognizedContainedMap
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Principal-open transport for affine analytification -/

noncomputable section

universe u v w x

namespace Langlands.Analytic.AffineAnalytification.PrincipalOpenTransport

open Set PresentedAffinoidAlgebra AnalyticAffineSpace IndexedAffinoidAtlas
open LocalDomainMaps

section Algebra

variable {K : Type u} [Field K]
  {C : Type v} [CommRing C] [Algebra K C]
  {B : Type w} [CommRing B] [Algebra K B]
  {T : Type x} [CommRing T] [Algebra K T]
  {h : C →ₐ[K] B} {r : C}

private theorem exists_extension_of_away (hinj : Function.Injective h)
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b)
    (α : C →ₐ[K] T) (hunit : IsUnit (α r)) :
    ∃ β : B →ₐ[K] T, β.comp h = α := by
  let g := Localization.awayMap h.toRingHom r
  have hg : Function.Bijective g := by
    refine ⟨Localization.awayMap_injective_iff.mpr ?_, Localization.awayMap_surjective_iff.mpr hclear⟩
    intro c hc
    refine ⟨0, ?_⟩
    have hc₀ : c = 0 := hinj (hc.trans (map_zero h).symm)
    simp [hc₀]
  let e := RingEquiv.ofBijective g hg
  let β₀ := (Localization.awayLift α.toRingHom r hunit).comp
    (e.symm.toRingHom.comp (algebraMap B (Localization.Away (h r))))
  have hβ₀ (c : C) : β₀ (h c) = α c := by
    have he : e (algebraMap C (Localization.Away r) c) =
        algebraMap B (Localization.Away (h r)) (h c) := by
      change Localization.awayMap h.toRingHom r (algebraMap C (Localization.Away r) c) = _
      simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    change Localization.awayLift α.toRingHom r hunit
      (e.symm (algebraMap B (Localization.Away (h r)) (h c))) = α c
    rw [← he, e.symm_apply_apply]
    exact IsLocalization.Away.lift_eq r hunit c
  let β : B →ₐ[K] T :=
    { β₀ with
      commutes' := fun a => (congrArg β₀ (h.commutes a).symm).trans
        ((hβ₀ (algebraMap K C a)).trans (α.commutes a)) }
  exact ⟨β, AlgHom.ext hβ₀⟩

private theorem extension_of_away_unique
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b)
    {β₁ β₂ : B →ₐ[K] T} (he : β₁.comp h = β₂.comp h)
    (hunit : IsUnit (β₁ (h r))) : β₁ = β₂ := by
  have hagree (c : C) : β₁ (h c) = β₂ (h c) :=
    congrArg (fun α : C →ₐ[K] T => α c) he
  ext b
  obtain ⟨c, n, hc⟩ := hclear b
  have hc₁ : β₁ (h c) = β₁ (h r) ^ n * β₁ b := by rw [hc, map_mul, map_pow]
  have hc₂ : β₂ (h c) = β₂ (h r) ^ n * β₂ b := by rw [hc, map_mul, map_pow]
  exact (hunit.pow n).mul_left_cancel (by rw [← hc₁, hagree c, hc₂, hagree r])

end Algebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {C : Type v} [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K C)
  {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (h : C →ₐ[K] B) (r : C)

private theorem injOn_baseMap_preimage_nonvanishing
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b) :
    Set.InjOn (baseMap K P Q h)
      (baseMap K P Q h ⁻¹' {z | pointSeminorm K P z r ≠ 0}) := by
  intro y hy y' _ he
  apply SeminormComparison.pointSeminorm_injective K Q
  have hagree (c : C) : pointSeminorm K Q y (h c) = pointSeminorm K Q y' (h c) := by
    rw [← pointSeminorm_baseMap K P Q h, ← pointSeminorm_baseMap K P Q h, he]
  have hne : pointSeminorm K Q y (h r) ≠ 0 := by
    rw [← pointSeminorm_baseMap K P Q h]
    exact hy
  ext b
  obtain ⟨c, n, hc⟩ := hclear b
  have hc₁ : pointSeminorm K Q y (h c) =
      pointSeminorm K Q y (h r) ^ n * pointSeminorm K Q y b := by
    rw [hc, map_mul, map_pow]
  have hc₂ : pointSeminorm K Q y' (h c) =
      pointSeminorm K Q y' (h r) ^ n * pointSeminorm K Q y' b := by
    rw [hc, map_mul, map_pow]
  exact mul_left_cancel₀ (pow_ne_zero n hne) (by rw [← hc₁, hagree c, hc₂, hagree r])

/-- A local domain over the nonvanishing locus lifts with a bounded equivalence
of its actual algebra that respects the coordinate maps. -/
private theorem exists_localDomain_preimage_of_away (hinj : Function.Injective h)
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b)
    (L : LocalDomain (atlas K P)) (hL : ∀ z ∈ L.locus, pointSeminorm K P z r ≠ 0) :
    ∃ M : LocalDomain (atlas K Q), M.locus = baseMap K P Q h ⁻¹' L.locus ∧
      ∃ e : BoundedAlgEquiv K L.algebra M.algebra,
        ∀ c, e (localAlgebraMap P L c) = localAlgebraMap Q M (h c) := by
  let α := localAlgebraMap P L
  have hunit : IsUnit (α r) := by
    apply (isUnit_iff_forall_spectrum_ne_zero L.algebra (α r)).mpr
    intro s
    rw [← pointSeminorm_affinoidBaseMap P L.algebra α]
    change pointSeminorm K P (affinoidBaseMap K P L.algebra (localAlgebraMap P L) s) r ≠ 0
    rw [affinoidBaseMap_localAlgebraMap]
    exact hL _ (L.range_ambientMap ▸ ⟨s, rfl⟩)
  obtain ⟨β, hβ⟩ := exists_extension_of_away hinj hclear α hunit
  have hbase (s : BanachSpectrum L.algebra) :
      baseMap K P Q h (affinoidBaseMap K Q L.algebra β s) = L.ambientMap s := by
    rw [baseMap_affinoidBaseMap P Q, hβ]
    exact affinoidBaseMap_localAlgebraMap P L s
  have hrange :
      range (affinoidBaseMap K Q L.algebra β) = baseMap K P Q h ⁻¹' L.locus := by
    apply Subset.antisymm
    · rintro _ ⟨s, rfl⟩
      rw [mem_preimage, hbase, ← L.range_ambientMap]
      exact ⟨s, rfl⟩
    · intro y hy
      obtain ⟨s, hs⟩ := L.range_ambientMap.symm ▸ (show baseMap K P Q h y ∈ L.locus from hy)
      have he := (hbase s).trans hs
      have hne : pointSeminorm K P (baseMap K P Q h y) r ≠ 0 := hL _ hy
      refine ⟨s, injOn_baseMap_preimage_nonvanishing P Q h r hclear ?_ hne he⟩
      change pointSeminorm K P (baseMap K P Q h (affinoidBaseMap K Q L.algebra β s)) r ≠ 0
      rwa [he]
  let m := affinoidLevel K Q L.algebra β
  let γ := affinoidChartMap K Q L.algebra β
  let U := range (BanachSpectrum.comap γ.toBoundedRingHom)
  have hrep : Represents K γ U := by
    have hclosed : IsClosed U :=
      (isCompact_range (BanachSpectrum.comapContinuous γ.toBoundedRingHom).continuous).isClosed
    refine ⟨hclosed, rfl, ?_⟩
    intro T θ hθ
    let φ := θ.toAlgHom.comp (PolynomialLocus.algebraMap Q (polyradius K Q.arity m))
    have hφ (s : BanachSpectrum T) : affinoidBaseMap K P T (φ.comp h) s ∈ L.locus := by
      have hs : affinoidBaseMap K Q T φ s ∈ range (affinoidBaseMap K Q L.algebra β) := by
        obtain ⟨t, ht⟩ := hθ s
        refine ⟨t, ?_⟩
        rw [← chart_comap_eq_affinoidBaseMap Q m θ φ (fun _ => rfl), affinoidBaseMap_apply]
        exact congrArg (chart K Q m) ht
      rw [hrange] at hs
      rwa [← baseMap_affinoidBaseMap P Q]
    obtain ⟨δ, hδ⟩ := exists_localDomain_lift P L T (φ.comp h) hφ
    have hδβ : δ.toAlgHom.comp β = φ := by
      apply extension_of_away_unique hclear
      · rw [AlgHom.comp_assoc, hβ]
        exact hδ
      · have he : β (h r) = α r :=
          congrArg (fun ψ : C →ₐ[K] L.algebra => ψ r) hβ
        change IsUnit (δ (β (h r)))
        rw [he]
        exact hunit.map δ.toAlgHom
    refine ⟨δ, ?_, ?_⟩
    · apply chart_hom_ext Q m
      intro b
      rw [BoundedAlgHom.comp_apply, affinoidChartMap_algebraMap]
      exact congrArg (fun ψ : B →ₐ[K] T => ψ b) hδβ
    · intro δ' hδ'
      have hδ'β : δ'.toAlgHom.comp β = φ := by
        ext b
        have he := congrArg
          (fun ψ : BoundedAlgHom K (algebra K Q m) T =>
            ψ (PolynomialLocus.algebraMap Q (polyradius K Q.arity m) b)) hδ'
        rwa [BoundedAlgHom.comp_apply, affinoidChartMap_algebraMap] at he
      apply localDomain_hom_ext P L
      intro c
      have he : δ'.toAlgHom.comp α = δ.toAlgHom.comp α := by
        rw [← hβ, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hδ'β, hδβ]
      exact congrArg (fun ψ : C →ₐ[K] T => ψ c) he
  let D : Domain K (algebra K Q m) := ⟨L.algebra, γ, U, hrep⟩
  let M : LocalDomain (atlas K Q) :=
    ⟨representative K Q m, D.transportBase (representativeEquiv K Q m).symm⟩
  have hM : localAlgebraMap Q M = β := by
    ext b
    change γ (equalRangeEquiv K Q (range_representative K Q m)
      (PolynomialLocus.algebraMap Q (polyradius K Q.arity (representative K Q m).val) b)) = β b
    rw [equalRangeEquiv_algebraMap, affinoidChartMap_algebraMap]
  refine ⟨M, ?_, BoundedAlgEquiv.refl K L.algebra, ?_⟩
  · rw [← hrange, ← M.range_ambientMap]
    congr 1
    funext s
    rw [← affinoidBaseMap_localAlgebraMap Q, hM]
    rfl
  · intro c
    rw [hM]
    exact congrArg (fun ψ : C →ₐ[K] L.algebra => ψ c) hβ.symm

/-- Use a containing saturated chart to view a recognized subset as a
local domain of the original atlas, with the same algebra. -/
private def containedLocalDomain (W : (atlas K P).RecognizedAffinoidSubset)
    (j : (atlas K P).saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((atlas K P).saturatedAtlas.chart j)) :
    LocalDomain (atlas K P) :=
  let S := (atlas K P).saturatedRepresentative j
  ⟨S.index, S.domain.extend (W.containedDomain j hW)⟩

private theorem containedLocalDomain_locus (W : (atlas K P).RecognizedAffinoidSubset)
    (j : (atlas K P).saturatedAtlas.Index)
    (hW : W.locus ⊆ range ((atlas K P).saturatedAtlas.chart j)) :
    (containedLocalDomain P W j hW).locus = W.locus := by
  rw [← (containedLocalDomain P W j hW).range_ambientMap, ← W.range_chart]
  congr 1
  funext s
  let S := (atlas K P).saturatedRepresentative j
  change (atlas K P).chart S.index ((S.domain.extend (W.containedDomain j hW)).spectrumMap s) =
    W.chart s
  exact (congrArg ((atlas K P).chart S.index)
    (Domain.extend_spectrumMap S.domain (W.containedDomain j hW) s)).trans
    (W.chart_containedRestriction j hW s)

/-- The preimage of a recognized subset in the principal open is recognized,
and the actual bounded pullback of its algebra is finite. -/
private theorem exists_recognized_preimage_of_away (hinj : Function.Injective h)
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b)
    (W : (atlas K P).RecognizedAffinoidSubset)
    (hW : ∀ z ∈ W.locus, pointSeminorm K P z r ≠ 0) :
    ∃ (V : (atlas K Q).RecognizedAffinoidSubset)
      (hVW : (saturatedHom K P Q h).baseMap '' range V.chart ⊆ range W.chart),
      V.locus = baseMap K P Q h ⁻¹' W.locus ∧
      ((saturatedHom K P Q h).fullRecognitionPairs.pullback V W hVW).IsFiniteBanach := by
  have hcompact : IsCompact W.locus := by
    rw [← W.range_chart]
    exact isCompact_range W.isEmbedding_chart.continuous
  let _ : Nonempty (atlas K P).Index := ⟨representative K P 0⟩
  obtain ⟨j₀, hj₀⟩ := (atlas K P).exists_subset_chart (atlas_hasDirectedCharts K P) hcompact
  let j := (atlas K P).originalSaturatedIndex j₀
  have hj : W.locus ⊆ range ((atlas K P).saturatedAtlas.chart j) := by
    change W.locus ⊆ range ((atlas K P).saturatedChart j)
    rw [(atlas K P).range_saturatedChart]
    exact hj₀
  let L := containedLocalDomain P W j hj
  have hL : L.locus = W.locus := containedLocalDomain_locus P W j hj
  obtain ⟨M, hM, e, he⟩ := exists_localDomain_preimage_of_away P Q h r hinj hclear L
    (by rwa [hL])
  let V := (atlas K Q).recognizedLocalDomain M
  have hV : V.locus = M.locus := (atlas K Q).recognizedLocalDomain_locus M
  have hpre : V.locus = baseMap K P Q h ⁻¹' W.locus := by rw [hV, hM, hL]
  let i : (atlas K Q).saturatedAtlas.Index := ⟨M.locus, ⟨M, rfl⟩⟩
  have hi : range ((atlas K Q).saturatedAtlas.chart i) = V.locus := by
    rw [hV]
    exact (atlas K Q).range_saturatedChart i
  have hVW : (saturatedHom K P Q h).baseMap '' range V.chart ⊆ range W.chart := by
    change baseMap K P Q h '' range V.chart ⊆ range W.chart
    rw [V.range_chart, W.range_chart, hpre]
    exact image_preimage_subset _ _
  have hij : (saturatedHom K P Q h).baseMap '' range ((atlas K Q).saturatedAtlas.chart i) ⊆
      range ((atlas K P).saturatedAtlas.chart j) := by
    change baseMap K P Q h '' range ((atlas K Q).saturatedAtlas.chart i) ⊆ _
    rw [hi, ← V.range_chart]
    exact hVW.trans (W.range_chart.subset.trans hj)
  let M' := containedLocalDomain Q V i hi.symm.subset
  have hMM' : M.locus = M'.locus :=
    hV.symm.trans (containedLocalDomain_locus Q V i hi.symm.subset).symm
  let e' := LocalDomain.boundedEquivOfLocusEq M M' hMM'
  let E : BoundedAlgEquiv K W.algebra V.algebra := e.trans e'
  let ψ : BoundedAlgHom K W.algebra V.algebra :=
    (saturatedHom K P Q h).fullRecognitionPairs.pullback V W hVW
  refine ⟨V, hVW, hpre, ?_⟩
  have hE : ψ = E.toBoundedAlgHom := by
    apply localDomain_hom_ext P L
    intro c
    have hcoord : ψ (localAlgebraMap P L c) = localAlgebraMap Q M' (h c) := by
      let a := localAlgebraMap P ((atlas K P).saturatedRepresentative j) c
      have hp := (saturatedHom K P Q h).fullRecognitionPairs_comp_containedRestriction
        V W i j hi.symm.subset hj hij hVW
      change ψ (W.containedRestriction j hj a) =
        V.containedRestriction i hi.symm.subset
          (localAlgebraMap Q ((atlas K Q).saturatedRepresentative i) (h c))
      exact (congrArg (fun f : BoundedAlgHom K ((atlas K P).saturatedAtlas.algebra j) V.algebra =>
        f a) hp).trans (congrArg (V.containedRestriction i hi.symm.subset)
          (saturatedHom_pullback_localAlgebraMap P Q h i j hij c))
    refine hcoord.trans ?_
    change localAlgebraMap Q M' (h c) = e' (e (localAlgebraMap P L c))
    rw [he]
    exact (inclusion_localAlgebraMap Q (LocalDomain.isoOfLocusEq M M' hMM').inv (h c)).symm
  change ψ.IsFiniteBanach
  exact hE.symm ▸ E.isFiniteBanach

/-- Local finiteness of the finite factor transfers to the original map at
each point in the inverse image of the nonvanishing locus. -/
theorem isFiniteAt_comp_of_away
    {A : Type x} [CommRing A] [Algebra K A] (R : FinitePolynomialPresentation K A)
    (f : A →ₐ[K] C) (hinj : Function.Injective h)
    (hclear : ∀ b : B, ∃ c : C, ∃ n : ℕ, h c = h r ^ n * b)
    (y : Space K Q) (hy : pointSeminorm K P (baseMap K P Q h y) r ≠ 0)
    (hf : (saturatedHom K R P f).IsFiniteAt (baseMap K P Q h y)) :
    (saturatedHom K R Q (h.comp f)).IsFiniteAt y := by
  let U : Set (Space K P) := {z | pointSeminorm K P z r ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (continuous_pointSeminorm_apply K P r) continuous_const
  have hh : (saturatedHom K P Q h).IsFiniteAt y := by
    refine ⟨baseMap K P Q h ⁻¹' U, U, hU.preimage (baseMap K P Q h).continuous, hU, hy, ?_⟩
    refine ⟨image_preimage_subset _ _, fun W hW => ?_⟩
    obtain ⟨V, hVW, hV, hfin⟩ :=
      exists_recognized_preimage_of_away P Q h r hinj hclear W (fun z hz => hW hz)
    refine ⟨V, hVW, hV.trans ?_, hfin⟩
    change baseMap K P Q h ⁻¹' W.locus =
      baseMap K P Q h ⁻¹' U ∩ baseMap K P Q h ⁻¹' W.locus
    exact (inter_eq_right.mpr (preimage_mono hW)).symm
  rw [LocalizedFunctorialityComparison.saturatedHom_comp R P f Q h
    (LocalizedFunctorialityComparison.OriginalStrongMaps.strongHom_comp R P f Q h)]
  exact hh.comp hf

end Langlands.Analytic.AffineAnalytification.PrincipalOpenTransport
