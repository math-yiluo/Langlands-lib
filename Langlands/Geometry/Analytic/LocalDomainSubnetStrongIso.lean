import Langlands.Geometry.Analytic.LocalDomainSubnetRecognition

/-! # Actual strong isomorphism for local-domain subnets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.LocalDomainSubnet

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)
  (σ : Set (Set A.space)) (hσ : A.atlas.IsLocalDomainSubnet σ)

local notation "S" => A.localDomainSubnetPresentation σ hσ
local notation "F" => Equivalence.functor (A.localDomainSubnetRecognitionEquivalence σ hσ)
local notation "G" => Equivalence.inverse (A.localDomainSubnetRecognitionEquivalence σ hσ)

/-- Extract the actual mutually inverse bounded maps from the constructed
forward natural isomorphism. -/
def forwardAlgebraEquiv (V : (S).atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K V.algebra ((F).obj V).algebra := by
  let e := (A.localDomainSubnetRecognitionAffinoidNatIso σ hσ).app V
  exact BoundedAlgEquiv.ofHomInv (Quiver.Hom.unop e.hom) (Quiver.Hom.unop e.inv)
    (fun b => congrArg
      (fun q : Opposite.op V.algebra ⟶ Opposite.op V.algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.inv_hom_id)
    (fun b => congrArg
      (fun q : Opposite.op ((F).obj V).algebra ⟶ Opposite.op ((F).obj V).algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.hom_inv_id)

theorem forwardAlgebraEquiv_naturality
    {U V : (S).atlas.saturatedAtlas.RecognizedSubset} (p : U ⟶ V) :
    (forwardAlgebraEquiv A σ hσ U).toBoundedAlgHom.comp p.restriction =
      ((F).map p).restriction.comp (forwardAlgebraEquiv A σ hσ V).toBoundedAlgHom :=
  (congrArg
    (fun q : Opposite.op ((F).obj U).algebra ⟶ Opposite.op V.algebra =>
      Quiver.Hom.unop q)
    ((A.localDomainSubnetRecognitionAffinoidNatIso σ hσ).hom.naturality p)).symm

/-- Both steps of the forward comparison lie over the literal identity
on the original ambient space. -/
theorem forwardNatIso_over_ambient
    (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum ((F).obj V).algebra) :
    V.chart ((affinoidSpectrumFunctor K).map
      ((A.localDomainSubnetRecognitionAffinoidNatIso σ hσ).hom.app V) x) =
        ((F).obj V).chart x := by
  let hf := A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ
  let hc := A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ
  let Y := hf.recognizedImage hc V
  let y := (affinoidSpectrumFunctor K).map
    (A.atlas.fullRecognitionIdempotenceAffinoidNatIso.hom.app Y) x
  exact (hf.recognizedImageAffinoidNatIso_over_ambient hc V y).trans
    (A.atlas.fullRecognitionIdempotenceAffinoidNatIso_over_ambient Y x)

theorem forwardAlgebraEquiv_chart
    (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum ((F).obj V).algebra) :
    ((F).obj V).chart x =
      V.chart ((forwardAlgebraEquiv A σ hσ V).spectrumHomeomorph x) :=
  (forwardNatIso_over_ambient A σ hσ V x).symm

/-- Pull back at every admissible pair, through the actual recognized
image and its bounded inverse comparison. -/
def forwardPullback (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (W : A.atlas.saturatedAtlas.RecognizedSubset) (h : V.locus ⊆ W.locus) :
    BoundedAlgHom K W.algebra V.algebra :=
  (forwardAlgebraEquiv A σ hσ V).symm.toBoundedAlgHom.comp
    (((F).obj V).restriction W (by
      rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
      exact h))

theorem forwardPullback_chart (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (W : A.atlas.saturatedAtlas.RecognizedSubset) (h : V.locus ⊆ W.locus)
    (x : BanachSpectrum V.algebra) :
    W.chart (BanachSpectrum.comap (forwardPullback A σ hσ V W h).toBoundedRingHom x) =
      V.chart x := by
  let e := forwardAlgebraEquiv A σ hσ V
  let Y := (F).obj V
  let r := Y.restriction W (by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
    exact h)
  have hp : BanachSpectrum.comap (forwardPullback A σ hσ V W h).toBoundedRingHom x =
      BanachSpectrum.comap r.toBoundedRingHom (e.spectrumHomeomorph.symm x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg W.chart hp).trans
    ((Y.chart_restriction W _ (e.spectrumHomeomorph.symm x)).trans
      ((forwardAlgebraEquiv_chart A σ hσ V (e.spectrumHomeomorph.symm x)).trans
        (congrArg V.chart (e.spectrumHomeomorph.apply_symm_apply x))))

set_option maxRecDepth 2000 in
theorem forwardPullback_naturality
    (U V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (W Z : A.atlas.saturatedAtlas.RecognizedSubset)
    (hUV : U.locus ⊆ V.locus) (hWZ : W.locus ⊆ Z.locus)
    (hUW : U.locus ⊆ W.locus) (hVZ : V.locus ⊆ Z.locus) :
    (U.restriction V hUV).comp (forwardPullback A σ hσ V Z hVZ) =
      (forwardPullback A σ hσ U W hUW).comp (W.restriction Z hWZ) := by
  let Y := (F).obj U
  let T := (F).obj V
  let e := forwardAlgebraEquiv A σ hσ U
  let d := forwardAlgebraEquiv A σ hσ V
  have hYT : Y.locus ⊆ T.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ U,
      A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
    exact hUV
  have hYW : Y.locus ⊆ W.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ U]
    exact hUW
  have hTZ : T.locus ⊆ Z.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
    exact hVZ
  have hn := forwardAlgebraEquiv_naturality A σ hσ (show U ⟶ V from ⟨hUV⟩)
  ext x
  apply e.injective
  have h₁ := congrArg (fun q : BoundedAlgHom K V.algebra Y.algebra =>
    q (d.symm (T.restriction Z hTZ x))) hn
  have h₂ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp T Z hYT hTZ)
  have h₃ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp W Z hYW hWZ)
  change e (U.restriction V hUV (d.symm (T.restriction Z hTZ x))) =
    e (e.symm (Y.restriction W hYW (W.restriction Z hWZ x)))
  rw [e.apply_symm_apply]
  exact h₁.trans ((congrArg (Y.restriction T hYT)
    (d.apply_symm_apply (T.restriction Z hTZ x))).trans (h₂.trans h₃.symm))

theorem forwardPullback_represents
    (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (W : A.atlas.saturatedAtlas.RecognizedSubset) (h : V.locus ⊆ W.locus) :
    Represents K (forwardPullback A σ hσ V W h) (W.chart ⁻¹' V.locus) := by
  have hr := (((F).obj V).restriction_represents W (by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
    exact h)).postcomp_equiv (forwardAlgebraEquiv A σ hσ V).symm
  have he : W.chart ⁻¹' ((F).obj V).locus = W.chart ⁻¹' V.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
  rw [he] at hr
  exact hr

/-- The identity ambient image of a source recognized chart is its locus. -/
theorem ambient_image_range_chart (V : (S).atlas.saturatedAtlas.RecognizedSubset) :
    (ContinuousMap.id A.space) '' Set.range V.chart = V.locus := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [← V.range_chart]
    exact ⟨z, rfl⟩
  · intro hx
    rw [← V.range_chart] at hx
    obtain ⟨z, rfl⟩ := hx
    exact ⟨V.chart z, ⟨z, rfl⟩, rfl⟩

theorem locus_subset_of_ambient_image
    (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : (ContinuousMap.id A.space) '' Set.range V.chart ⊆ Set.range W.chart) :
    V.locus ⊆ W.locus := by
  rw [← ambient_image_range_chart A σ hσ V, ← W.range_chart]
  exact h

theorem ambient_image_subset_forward_range
    (V : (S).atlas.saturatedAtlas.RecognizedSubset) :
    (ContinuousMap.id A.space) '' Set.range V.chart ⊆ Set.range ((F).obj V).chart := by
  rw [ambient_image_range_chart A σ hσ V, ((F).obj V).range_chart,
    A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V]
  exact Set.Subset.rfl

/-- The forward comparison is an actual all-admissible-pair strong map,
on the original ambient space. -/
def forward : StrongHom (S).fullRecognitionPresentation A.fullRecognitionPresentation where
  baseMap := ContinuousMap.id A.space
  target_exists V := ⟨(F).obj V, ambient_image_subset_forward_range A σ hσ V⟩
  pullback V W h := forwardPullback A σ hσ V W
    (locus_subset_of_ambient_image A σ hσ V W h)
  chart_comm V W h x := forwardPullback_chart A σ hσ V W _ x
  restriction_comm U V W Z hUV hWZ hUW hVZ := by
    change (S).atlas.saturatedAtlas.RecognizedSubset at U V
    change A.atlas.saturatedAtlas.RecognizedSubset at W Z
    change Set.range U.chart ⊆ Set.range V.chart at hUV
    change Set.range W.chart ⊆ Set.range Z.chart at hWZ
    exact forwardPullback_naturality A σ hσ U V W Z
      (by simpa only [U.range_chart, V.range_chart] using hUV)
      (by simpa only [W.range_chart, Z.range_chart] using hWZ) _ _

@[simp]
theorem forward_baseMap :
    (forward A σ hσ).baseMap = ContinuousMap.id A.space := rfl

theorem forward_isQuasiIso : (forward A σ hσ).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro V W h
  change (S).atlas.saturatedAtlas.RecognizedSubset at V
  change A.atlas.saturatedAtlas.RecognizedSubset at W
  change Represents K (forwardPullback A σ hσ V W (locus_subset_of_ambient_image A σ hσ V W h))
    (W.chart ⁻¹' ((ContinuousMap.id A.space) '' Set.range V.chart))
  rw [ambient_image_range_chart A σ hσ V]
  exact forwardPullback_represents A σ hσ V W _

set_option maxRecDepth 4000 in
/-- Extract the actual mutually inverse bounded maps from the constructed
reverse natural isomorphism. -/
def reverseAlgebraEquiv (W : A.atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K W.algebra ((G).obj W).algebra := by
  let e := (A.localDomainSubnetReverseRecognitionAffinoidNatIso σ hσ).app W
  exact BoundedAlgEquiv.ofHomInv (Quiver.Hom.unop e.hom) (Quiver.Hom.unop e.inv)
    (fun b => congrArg
      (fun q : Opposite.op W.algebra ⟶ Opposite.op W.algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.inv_hom_id)
    (fun b => congrArg
      (fun q : Opposite.op ((G).obj W).algebra ⟶ Opposite.op ((G).obj W).algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.hom_inv_id)

theorem reverseAlgebraEquiv_naturality
    {U W : A.atlas.saturatedAtlas.RecognizedSubset} (p : U ⟶ W) :
    (reverseAlgebraEquiv A σ hσ U).toBoundedAlgHom.comp p.restriction =
      ((G).map p).restriction.comp (reverseAlgebraEquiv A σ hσ W).toBoundedAlgHom :=
  (congrArg
    (fun q : Opposite.op ((G).obj U).algebra ⟶ Opposite.op W.algebra =>
      Quiver.Hom.unop q)
    ((A.localDomainSubnetReverseRecognitionAffinoidNatIso σ hσ).hom.naturality p)).symm

set_option maxRecDepth 2000 in
/-- The reverse comparison is the inverse forward comparison followed by
the counit inclusion, so it also lies over the identity ambient map. -/
theorem reverseAlgebraEquiv_chart (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (y : BanachSpectrum ((G).obj W).algebra) :
    ((G).obj W).chart y =
      W.chart ((reverseAlgebraEquiv A σ hσ W).spectrumHomeomorph y) := by
  let c := ((A.localDomainSubnetRecognitionEquivalence σ hσ).counitIso.app W).hom
  let e := forwardAlgebraEquiv A σ hσ ((G).obj W)
  have hp : (reverseAlgebraEquiv A σ hσ W).spectrumHomeomorph y =
      c.spectrumMap (e.spectrumHomeomorph.symm y) :=
    BanachSpectrum.ext fun _ => rfl
  rw [hp]
  exact ((congrArg ((G).obj W).chart (e.spectrumHomeomorph.apply_symm_apply y)).symm.trans
    (forwardAlgebraEquiv_chart A σ hσ ((G).obj W) (e.spectrumHomeomorph.symm y)).symm).trans
      (c.chart_naturality (e.spectrumHomeomorph.symm y)).symm

/-- Pull back at every reverse-admissible pair, through the actual reverse
recognized image and its bounded inverse comparison. -/
def reversePullback (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (V : (S).atlas.saturatedAtlas.RecognizedSubset) (h : W.locus ⊆ V.locus) :
    BoundedAlgHom K V.algebra W.algebra :=
  (reverseAlgebraEquiv A σ hσ W).symm.toBoundedAlgHom.comp
    (((G).obj W).restriction V (by
      rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
      exact h))

set_option maxRecDepth 4000 in
theorem reversePullback_chart (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (V : (S).atlas.saturatedAtlas.RecognizedSubset) (h : W.locus ⊆ V.locus)
    (x : BanachSpectrum W.algebra) :
    V.chart (BanachSpectrum.comap (reversePullback A σ hσ W V h).toBoundedRingHom x) =
      W.chart x := by
  let e := reverseAlgebraEquiv A σ hσ W
  let Y := (G).obj W
  let r := Y.restriction V (by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
    exact h)
  have hp : BanachSpectrum.comap (reversePullback A σ hσ W V h).toBoundedRingHom x =
      BanachSpectrum.comap r.toBoundedRingHom (e.spectrumHomeomorph.symm x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg V.chart hp).trans
    ((Y.chart_restriction V _ (e.spectrumHomeomorph.symm x)).trans
      ((reverseAlgebraEquiv_chart A σ hσ W (e.spectrumHomeomorph.symm x)).trans
        (congrArg W.chart (e.spectrumHomeomorph.apply_symm_apply x))))

set_option maxRecDepth 2000 in
theorem reversePullback_naturality
    (U W : A.atlas.saturatedAtlas.RecognizedSubset)
    (V Z : (S).atlas.saturatedAtlas.RecognizedSubset)
    (hUW : U.locus ⊆ W.locus) (hVZ : V.locus ⊆ Z.locus)
    (hUV : U.locus ⊆ V.locus) (hWZ : W.locus ⊆ Z.locus) :
    (U.restriction W hUW).comp (reversePullback A σ hσ W Z hWZ) =
      (reversePullback A σ hσ U V hUV).comp (V.restriction Z hVZ) := by
  let Y := (G).obj U
  let T := (G).obj W
  let e := reverseAlgebraEquiv A σ hσ U
  let d := reverseAlgebraEquiv A σ hσ W
  have hYT : Y.locus ⊆ T.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ U,
      A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
    exact hUW
  have hYV : Y.locus ⊆ V.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ U]
    exact hUV
  have hTZ : T.locus ⊆ Z.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
    exact hWZ
  have hn := reverseAlgebraEquiv_naturality A σ hσ (show U ⟶ W from ⟨hUW⟩)
  ext x
  apply e.injective
  have h₁ := congrArg (fun q : BoundedAlgHom K W.algebra Y.algebra =>
    q (d.symm (T.restriction Z hTZ x))) hn
  have h₂ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp T Z hYT hTZ)
  have h₃ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp V Z hYV hVZ)
  change e (U.restriction W hUW (d.symm (T.restriction Z hTZ x))) =
    e (e.symm (Y.restriction V hYV (V.restriction Z hVZ x)))
  rw [e.apply_symm_apply]
  exact h₁.trans ((congrArg (Y.restriction T hYT)
    (d.apply_symm_apply (T.restriction Z hTZ x))).trans (h₂.trans h₃.symm))

theorem reversePullback_represents (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (V : (S).atlas.saturatedAtlas.RecognizedSubset) (h : W.locus ⊆ V.locus) :
    Represents K (reversePullback A σ hσ W V h) (V.chart ⁻¹' W.locus) := by
  have hr := (((G).obj W).restriction_represents V (by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
    exact h)).postcomp_equiv (reverseAlgebraEquiv A σ hσ W).symm
  have he : V.chart ⁻¹' ((G).obj W).locus = V.chart ⁻¹' W.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
  rw [he] at hr
  exact hr

theorem reverse_ambient_image_range_chart (W : A.atlas.saturatedAtlas.RecognizedSubset) :
    (ContinuousMap.id A.space) '' Set.range W.chart = W.locus := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    rw [← W.range_chart]
    exact ⟨z, rfl⟩
  · intro hx
    rw [← W.range_chart] at hx
    obtain ⟨z, rfl⟩ := hx
    exact ⟨W.chart z, ⟨z, rfl⟩, rfl⟩

theorem locus_subset_of_reverse_ambient_image
    (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (V : (S).atlas.saturatedAtlas.RecognizedSubset)
    (h : (ContinuousMap.id A.space) '' Set.range W.chart ⊆ Set.range V.chart) :
    W.locus ⊆ V.locus :=
  (reverse_ambient_image_range_chart A W).symm.trans_subset
    (h.trans V.range_chart.subset)

theorem reverse_ambient_image_subset_range (W : A.atlas.saturatedAtlas.RecognizedSubset) :
    (ContinuousMap.id A.space) '' Set.range W.chart ⊆ Set.range ((G).obj W).chart :=
  (reverse_ambient_image_range_chart A W).trans_subset
    ((A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W).symm.trans
      ((G).obj W).range_chart.symm).subset

/-- The reverse comparison is an actual all-admissible-pair strong map on
the entire full recognition atlas, again on the identity ambient space. -/
def reverse : StrongHom A.fullRecognitionPresentation (S).fullRecognitionPresentation where
  baseMap := ContinuousMap.id A.space
  target_exists W := ⟨(G).obj W, reverse_ambient_image_subset_range A σ hσ W⟩
  pullback W V h := reversePullback A σ hσ W V
    (locus_subset_of_reverse_ambient_image A σ hσ W V h)
  chart_comm W V h x := reversePullback_chart A σ hσ W V _ x
  restriction_comm U W V Z hUW hVZ hUV hWZ := by
    change A.atlas.saturatedAtlas.RecognizedSubset at U W
    change (S).atlas.saturatedAtlas.RecognizedSubset at V Z
    change Set.range U.chart ⊆ Set.range W.chart at hUW
    change Set.range V.chart ⊆ Set.range Z.chart at hVZ
    exact reversePullback_naturality A σ hσ U W V Z
      (by simpa only [U.range_chart, W.range_chart] using hUW)
      (by simpa only [V.range_chart, Z.range_chart] using hVZ) _ _

@[simp]
theorem reverse_baseMap :
    (reverse A σ hσ).baseMap = ContinuousMap.id A.space := rfl

theorem reverse_isQuasiIso : (reverse A σ hσ).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro W V h
  change A.atlas.saturatedAtlas.RecognizedSubset at W
  change (S).atlas.saturatedAtlas.RecognizedSubset at V
  change Represents K
    (reversePullback A σ hσ W V (locus_subset_of_reverse_ambient_image A σ hσ W V h))
    (V.chart ⁻¹' ((ContinuousMap.id A.space) '' Set.range W.chart))
  have he : V.chart ⁻¹' ((ContinuousMap.id A.space) '' Set.range W.chart) =
      V.chart ⁻¹' W.locus :=
    congrArg (Set.preimage V.chart) (reverse_ambient_image_range_chart A W)
  exact (congrArg (Represents K _) he).mpr (reversePullback_represents A σ hσ W V _)

/-- At its own reverse image, the reverse pullback is the entire inverse
of the reverse comparison. -/
theorem reversePullback_inverse (W : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : W.locus ⊆ ((G).obj W).locus) :
    reversePullback A σ hσ W ((G).obj W) h =
      (reverseAlgebraEquiv A σ hσ W).symm.toBoundedAlgHom := by
  change (reverseAlgebraEquiv A σ hσ W).symm.toBoundedAlgHom.comp
    (((G).obj W).restriction ((G).obj W) _) = _
  rw [RecognizedSubset.restriction_self, BoundedAlgHom.comp_id]

set_option maxRecDepth 4000 in
/-- The reverse followed by the forward comparison is the entire strong
identity of the original full recognition atlas. -/
theorem reverse_comp_forward :
    (reverse A σ hσ).saturatedComp (forward A σ hσ)
      A.fullRecognitionPresentation_hasAllLocalDomains
      (S).fullRecognitionPresentation_hasAllLocalDomains =
        StrongHom.id A.fullRecognitionPresentation := by
  have hbase :
      ((reverse A σ hσ).saturatedComp (forward A σ hσ)
        A.fullRecognitionPresentation_hasAllLocalDomains
        (S).fullRecognitionPresentation_hasAllLocalDomains).baseMap =
          (StrongHom.id A.fullRecognitionPresentation).baseMap := by
    ext x
    rfl
  refine StrongHom.ext_of_saturated
    A.fullRecognitionPresentation_hasAllLocalDomains hbase ?_
  intro W
  change A.atlas.saturatedAtlas.RecognizedSubset at W
  let V := (G).obj W
  have hR : (reverse A σ hσ).baseMap '' Set.range W.chart ⊆ Set.range V.chart :=
    reverse_ambient_image_subset_range A σ hσ W
  have hE : (forward A σ hσ).baseMap '' Set.range V.chart ⊆ Set.range W.chart :=
    (ambient_image_range_chart A σ hσ V).trans_subset
      ((A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W).trans
        W.range_chart.symm).subset
  have h := (reverse A σ hσ).comp_admissible (forward A σ hσ) W V W hR hE
  refine ⟨W, h, ?_⟩
  rw [StrongHom.saturatedComp_pullback (reverse A σ hσ) (forward A σ hσ)
    A.fullRecognitionPresentation_hasAllLocalDomains
    (S).fullRecognitionPresentation_hasAllLocalDomains W V W hR hE h]
  change (reversePullback A σ hσ W V
      (locus_subset_of_reverse_ambient_image A σ hσ W V hR)).comp
    (forwardPullback A σ hσ V W (locus_subset_of_ambient_image A σ hσ V W hE)) =
      W.restriction W Subset.rfl
  rw [reversePullback_inverse A σ hσ W]
  let c := ((A.localDomainSubnetRecognitionEquivalence σ hσ).counitIso.app W).inv
  let e := forwardAlgebraEquiv A σ hσ V
  have hx : ((F).obj V).locus ⊆ W.locus := by
    rw [A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V,
      A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W]
  ext x
  change c.restriction (e (e.symm (((F).obj V).restriction W hx x))) =
    W.restriction W Subset.rfl x
  rw [e.apply_symm_apply]
  exact congrArg (fun q : BoundedAlgHom K W.algebra W.algebra => q x)
    (W.restriction_comp ((F).obj V) W c.subset hx)

set_option maxRecDepth 2000 in
/-- Cancellation by the forward full quasi-isomorphism recovers the other
entire strong identity. -/
theorem forward_comp_reverse :
    (forward A σ hσ).saturatedComp (reverse A σ hσ)
      (S).fullRecognitionPresentation_hasAllLocalDomains
      A.fullRecognitionPresentation_hasAllLocalDomains =
        StrongHom.id (S).fullRecognitionPresentation := by
  apply (forward_isQuasiIso A σ hσ).cancel_saturatedComp
    (S).fullRecognitionPresentation_hasAllLocalDomains
    (S).fullRecognitionPresentation_hasAllLocalDomains
  rw [StrongHom.saturatedComp_assoc, reverse_comp_forward A σ hσ,
    StrongHom.saturatedComp_id, StrongHom.id_saturatedComp]

/-- An actual categorical isomorphism between the full recognition atlases
of an arbitrary local-domain subnet and of the original atlas. -/
def strongIso :
    SaturatedAtlasPresentation.ofFullRecognition (S) ≅
      SaturatedAtlasPresentation.ofFullRecognition A where
  hom := forward A σ hσ
  inv := reverse A σ hσ
  hom_inv_id := forward_comp_reverse A σ hσ
  inv_hom_id := reverse_comp_forward A σ hσ

@[simp]
theorem strongIso_hom_baseMap :
    (strongIso A σ hσ).hom.baseMap = ContinuousMap.id A.space := rfl

@[simp]
theorem strongIso_inv_baseMap :
    (strongIso A σ hσ).inv.baseMap = ContinuousMap.id A.space := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.LocalDomainSubnet
