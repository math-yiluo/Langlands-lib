import Langlands.Geometry.Analytic.AffineAnalytificationExtensionCoordinates
import Langlands.Geometry.Analytic.FieldPointValueChange

/-! # Naturality of extension-valued affine analytic coordinates -/

noncomputable section

universe u v w uL uM

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation SaturatedAtlasPresentation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- Coordinate recovery commutes with the strong map of saturated affine
analytifications induced by an algebra map. -/
theorem extensionAlgHom_saturatedHom (t : FieldPoint L (saturated K Q).presentation) :
    extensionAlgHom K P (t.map (saturatedHom K P Q f) (saturated K Q).hasAllLocalDomains) =
      (extensionAlgHom K Q t).comp f := by
  let X := presentation K Q
  let Y := presentation K P
  let h := strongHom K P Q f
  obtain ⟨i, hi⟩ := X.atlas.exists_mem_range_chart t.point
  let j := indexMap K P Q f i
  have hij : h.baseMap '' range (X.atlas.chart i) ⊆ range (Y.atlas.chart j) :=
    (atlasHom K P Q f).image_chart_subset i
  have hj : h.baseMap t.point ∈ range (Y.atlas.chart j) := hij ⟨_, hi, rfl⟩
  let I := X.atlas.originalSaturatedIndex i
  let J := Y.atlas.originalSaturatedIndex j
  have hI : t.point ∈ range (X.atlas.saturatedChart I) :=
    (X.atlas.saturatedAtlas_original_range i).ge hi
  have hJ : h.baseMap t.point ∈ range (Y.atlas.saturatedChart J) :=
    (Y.atlas.saturatedAtlas_original_range j).ge hj
  have hIJ := h.saturationExtension_original_admissible i j hij
  have hlocal : h.baseMap '' (X.atlas.saturatedRepresentative I).locus ⊆
      (Y.atlas.saturatedRepresentative J).locus := by
    rw [← (X.atlas.saturatedRepresentative I).range_ambientMap,
      ← (Y.atlas.saturatedRepresentative J).range_ambientMap]
    exact hIJ
  let c := X.atlas.saturatedToOriginalInclusion I i (X.atlas.saturatedAtlas_original_range i).le
  let d := Y.atlas.saturatedToOriginalInclusion J j (Y.atlas.saturatedAtlas_original_range j).le
  have hcomm := h.localDomainPullback_naturality (strongHom_hasCoherentPullbacks K P Q f)
    c d hlocal (by
      rw [X.atlas.originalLocalDomain_locus i, Y.atlas.originalLocalDomain_locus j]
      exact hij)
  have hselected : h.pullback i j hij = pullback K P Q f i :=
    StrongHom.ofDirected_pullback_selected (atlasHom K P Q f) (atlas_hasDirectedCharts K P) i
  rw [h.localDomainPullback_original (strongHom_hasCoherentPullbacks K P Q f) i j hij,
    hselected] at hcomm
  let r := t.map (saturatedHom K P Q f) (saturated K Q).hasAllLocalDomains
  ext a
  change originalExtensionAlgHom K P r.restrictSaturation a =
    originalExtensionAlgHom K Q t.restrictSaturation (f a)
  rw [originalExtensionAlgHom_apply_eq K P r.restrictSaturation j hj,
    originalExtensionAlgHom_apply_eq K Q t.restrictSaturation i hi]
  change r.eval J hJ (d.restriction (chartAlgebraMap K P j a)) =
    t.eval I hI (c.restriction (chartAlgebraMap K Q i (f a)))
  have heval := t.map_eval (saturatedHom K P Q f) (saturated K Q).hasAllLocalDomains J hJ I hI hIJ
  refine (AlgHom.congr_fun heval (d.restriction (chartAlgebraMap K P j a))).trans ?_
  change t.eval I hI ((h.localDomainPullback (X.atlas.saturatedRepresentative I)
    (Y.atlas.saturatedRepresentative J) hlocal).comp d.restriction (chartAlgebraMap K P j a)) = _
  exact (congrArg (fun k => t.eval I hI (k (chartAlgebraMap K P j a))) hcomm.symm).trans
    (congrArg (fun b => t.eval I hI (c.restriction b)) (pullback_algebraMap K P Q f i a))

/-- Coordinate recovery sends the localized affine map induced by `f` to
precomposition by `f`. -/
theorem extensionAlgHom_localizedHom (t : (localizedFieldPointFunctor L).obj (localized K Q)) :
    extensionAlgHom K P ((localizedFieldPointFunctor L).map (localizedHom K P Q f) t) =
      (extensionAlgHom K Q t).comp f :=
  extensionAlgHom_saturatedHom K P Q f t

/-- Changing the value field of a full point postcomposes its algebraic
coordinates by the same map. -/
theorem extensionAlgHom_mapValue {M : Type uM} [NormedField M] [NormedAlgebra K M]
    (t : FieldPoint L (saturated K P).presentation)
    (e : L →ₐ[K] M) (he : ∀ a, ‖e a‖ = ‖a‖) :
    extensionAlgHom K P (t.mapValue e he) = e.comp (extensionAlgHom K P t) := by
  let r := t.mapValue e he
  obtain ⟨i, hi⟩ := (presentation K P).atlas.exists_mem_range_chart t.point
  ext a
  change originalExtensionAlgHom K P r.restrictSaturation a =
    e (originalExtensionAlgHom K P t.restrictSaturation a)
  rw [originalExtensionAlgHom_apply_eq K P r.restrictSaturation i hi,
    originalExtensionAlgHom_apply_eq K P t.restrictSaturation i hi]
  rfl

end Langlands.Analytic.AffineAnalytification
