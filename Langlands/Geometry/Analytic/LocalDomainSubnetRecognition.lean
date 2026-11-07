import Langlands.Geometry.Analytic.SubnetRecognitionEquivalence
import Langlands.Geometry.Analytic.RecognizedAtlasExtension

/-! # Recognition invariance for arbitrary local-domain subnets -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A literal net contained in the original local-domain enlargement.
Neither local refinement nor recognition invariance is part of this law. -/
def IsLocalDomainSubnet (σ : Set (Set X)) : Prop :=
  AtlasTopology.IsNet σ ∧ σ ⊆ a.localDomainFamily

/-- Selecting the members of a subnet from the constructed local-domain
atlas recovers exactly the supplied literal family. -/
theorem localDomainSubnet_selectedChartFamily (σ : Set (Set X))
    (hσ : σ ⊆ a.localDomainFamily) :
    a.saturatedAtlas.selectedChartFamily (fun S => S.val ∈ σ) = σ := by
  ext U
  constructor
  · rintro ⟨S, rfl⟩
    change {S : a.localDomainFamily // S.val ∈ σ} at S
    change Set.range (a.saturatedChart S.val) ∈ σ
    rw [a.range_saturatedChart]
    exact S.property
  · intro hU
    exact ⟨⟨⟨U, hσ hU⟩, hU⟩, a.range_saturatedChart ⟨U, hσ hU⟩⟩

theorem IsLocalDomainSubnet.isNetSelection {σ : Set (Set X)}
    (hσ : a.IsLocalDomainSubnet σ) :
    a.saturatedAtlas.IsNetSelection (fun S => S.val ∈ σ) := by
  change AtlasTopology.IsNet _
  rw [a.localDomainSubnet_selectedChartFamily σ hσ.2]
  exact hσ.1

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The same-space atlas of an arbitrary literal net of original local
domains, retaining the constructed enlargement's actual presentations. -/
def localDomainSubnetPresentation (σ : Set (Set A.space))
    (hσ : A.atlas.IsLocalDomainSubnet σ) : AffinoidAtlasPresentation.{u, v, v} K :=
  A.saturatedPresentation.netSubpresentation (fun S => S.val ∈ σ) hσ.isNetSelection

theorem localDomainSubnetPresentation_chartFamily (σ : Set (Set A.space))
    (hσ : A.atlas.IsLocalDomainSubnet σ) :
    Set.range (fun i => Set.range ((A.localDomainSubnetPresentation σ hσ).atlas.chart i)) =
      σ :=
  A.atlas.localDomainSubnet_selectedChartFamily σ hσ.2

@[simp]
theorem localDomainSubnetPresentation_algebra (σ : Set (Set A.space))
    (hσ : A.atlas.IsLocalDomainSubnet σ)
    (S : {S : A.atlas.localDomainFamily // S.val ∈ σ}) :
    (A.localDomainSubnetPresentation σ hσ).atlas.algebra S =
      (A.atlas.saturatedRepresentative S.val).algebra := rfl

@[simp]
theorem localDomainSubnetPresentation_chart (σ : Set (Set A.space))
    (hσ : A.atlas.IsLocalDomainSubnet σ)
    (S : {S : A.atlas.localDomainFamily // S.val ∈ σ}) :
    (A.localDomainSubnetPresentation σ hσ).atlas.chart S =
      A.atlas.saturatedChart S.val := rfl

/-- The actual local-domain atlas maps into full recognition by all
canonical original-chart restrictions, on the identity ambient space. -/
def localDomainToFullRecognition :
    StrongHom A.saturatedPresentation A.fullRecognitionPresentation where
  baseMap := ContinuousMap.id A.space
  target_exists S := by
    change A.atlas.saturatedAtlas.Index at S
    refine ⟨A.atlas.saturatedAtlas.originalRecognitionIndex S, ?_⟩
    change id '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range (A.atlas.saturatedAtlas.recognitionAtlas.chart
        (A.atlas.saturatedAtlas.originalRecognitionIndex S))
    rw [Set.image_id, A.atlas.saturatedAtlas.recognitionAtlas_original_range]
  pullback S V h := V.originalRestriction S (by
    rw [← V.range_chart]
    exact fun x hx => h ⟨x, hx, rfl⟩)
  chart_comm S V h x := V.chart_originalRestriction S _ x
  restriction_comm S T U V hST hUV hSU hTV := by
    change A.atlas.saturatedAtlas.RecognizedSubset at U V
    have hUV' : U.locus ⊆ V.locus := by
      rw [← U.range_chart, ← V.range_chart]
      exact hUV
    have hSU' : Set.range (A.atlas.saturatedAtlas.chart S) ⊆ U.locus := by
      rw [← U.range_chart]
      exact fun x hx => hSU ⟨x, hx, rfl⟩
    have hTV' : Set.range (A.atlas.saturatedAtlas.chart T) ⊆ V.locus := by
      rw [← V.range_chart]
      exact fun x hx => hTV ⟨x, hx, rfl⟩
    exact (V.originalRestriction_naturality T S hTV' (hSU'.trans hUV') hST).trans
      (U.originalRestriction_comp_restriction V hUV' S hSU').symm

@[simp]
theorem localDomainToFullRecognition_baseMap :
    A.localDomainToFullRecognition.baseMap = ContinuousMap.id A.space := rfl

theorem localDomainToFullRecognition_isQuasiIso :
    A.localDomainToFullRecognition.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro S V h
  change A.atlas.saturatedAtlas.RecognizedSubset at V
  have hSV : Set.range (A.atlas.saturatedAtlas.chart S) ⊆ V.locus := by
    rw [← V.range_chart]
    exact fun x hx => h ⟨x, hx, rfl⟩
  change Represents K (V.originalRestriction S hSV)
    (V.chart ⁻¹' (id '' Set.range (A.atlas.saturatedAtlas.chart S)))
  rw [Set.image_id, ← V.range_comap_originalRestriction S hSV]
  exact V.originalRestriction_represents S hSV

/-- This is a consequence of the proved closure of the constructed source
local-domain atlas, rather than an input about the selected net. -/
theorem localDomainToFullRecognition_hasCoherentPullbacks :
    A.localDomainToFullRecognition.HasCoherentPullbacks :=
  A.localDomainToFullRecognition.hasCoherentPullbacks_of_saturated
    A.atlas.saturatedAtlas_hasAllLocalDomains

variable (σ : Set (Set A.space)) (hσ : A.atlas.IsLocalDomainSubnet σ)

/-- Restrict the constructed local-domain inclusion to the supplied net.
Every admissible bounded pullback is retained, including unselected targets. -/
def localDomainSubnetToFullRecognition :
    StrongHom (A.localDomainSubnetPresentation σ hσ) A.fullRecognitionPresentation :=
  A.localDomainToFullRecognition.restrictNetSubatlasSource
    (fun S => S.val ∈ σ) hσ.isNetSelection

@[simp]
theorem localDomainSubnetToFullRecognition_baseMap :
    (A.localDomainSubnetToFullRecognition σ hσ).baseMap =
      ContinuousMap.id A.space := rfl

theorem localDomainSubnetToFullRecognition_isQuasiIso :
    (A.localDomainSubnetToFullRecognition σ hσ).IsQuasiIso :=
  A.localDomainToFullRecognition_isQuasiIso.restrictNetSubatlasSource
    (fun S => S.val ∈ σ) hσ.isNetSelection

theorem localDomainSubnetToFullRecognition_hasCoherentPullbacks :
    (A.localDomainSubnetToFullRecognition σ hσ).HasCoherentPullbacks :=
  A.localDomainToFullRecognition.restrictNetSubatlasSource_hasCoherentPullbacks
    A.localDomainToFullRecognition_hasCoherentPullbacks
    (fun S => S.val ∈ σ) hσ.isNetSelection

/-- Recognition of the subnet first compares with recognition of the
full atlas, then the constructed idempotence equivalence removes iteration. -/
def localDomainSubnetRecognitionEquivalence :
    (A.localDomainSubnetPresentation σ hσ).atlas.saturatedAtlas.RecognizedSubset ≌
      A.atlas.saturatedAtlas.RecognizedSubset :=
  ((A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ).generalRecognizedImageEquivalence
    (A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ)).trans
      A.atlas.fullRecognitionIdempotenceEquivalence

@[simp]
theorem localDomainSubnetRecognitionEquivalence_functor_locus
    (V : (A.localDomainSubnetPresentation σ hσ).atlas.saturatedAtlas.RecognizedSubset) :
    ((A.localDomainSubnetRecognitionEquivalence σ hσ).functor.obj V).locus = V.locus := by
  have hl := (A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ).recognizedImage_locus
    (A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ) V
  change _ = id '' V.locus at hl
  exact hl.trans (Set.image_id _)

@[simp]
theorem localDomainSubnetRecognitionEquivalence_inverse_locus
    (W : A.atlas.saturatedAtlas.RecognizedSubset) :
    ((A.localDomainSubnetRecognitionEquivalence σ hσ).inverse.obj W).locus = W.locus := by
  have hl := (A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ).generalReverseRecognizedImage_locus
      (A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ)
      (A.atlas.fullRecognitionIterationIndex W)
  exact hl.trans (A.atlas.fullRecognitionIterationIndex_locus W)

/-- The source's full local-domain subnet convention preserves the entire
literal family of recognized affinoid subsets. -/
theorem localDomainSubnet_recognizedAffinoidFamily :
    (A.localDomainSubnetPresentation σ hσ).atlas.recognizedAffinoidFamily =
      A.atlas.recognizedAffinoidFamily := by
  apply Set.Subset.antisymm
  · rintro S ⟨V, rfl⟩
    exact ⟨(A.localDomainSubnetRecognitionEquivalence σ hσ).functor.obj V,
      A.localDomainSubnetRecognitionEquivalence_functor_locus σ hσ V⟩
  · rintro S ⟨W, rfl⟩
    exact ⟨(A.localDomainSubnetRecognitionEquivalence σ hσ).inverse.obj W,
      A.localDomainSubnetRecognitionEquivalence_inverse_locus σ hσ W⟩

/-- Compose the complete bounded affine comparison with full-recognition
idempotence. The naturality concerns actual bounded maps. -/
def localDomainSubnetRecognitionAffinoidNatIso :
    (A.localDomainSubnetRecognitionEquivalence σ hσ).functor ⋙
        RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace
        (A.localDomainSubnetPresentation σ hσ).atlas.saturatedAtlas :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ).recognizedImageFunctor
        (A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ))
      A.atlas.fullRecognitionIdempotenceAffinoidNatIso ≪≫
    (A.localDomainSubnetToFullRecognition_isQuasiIso σ hσ).recognizedImageAffinoidNatIso
      (A.localDomainSubnetToFullRecognition_hasCoherentPullbacks σ hσ)

/-- The inverse forward comparison and the actual equivalence counit give
the reverse bounded comparison and all of its naturality. -/
def localDomainSubnetReverseRecognitionAffinoidNatIso :
    (A.localDomainSubnetRecognitionEquivalence σ hσ).inverse ⋙
        RecognizedSubset.toAffinoidSpace
          (A.localDomainSubnetPresentation σ hσ).atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas :=
  Functor.isoWhiskerLeft (A.localDomainSubnetRecognitionEquivalence σ hσ).inverse
      (A.localDomainSubnetRecognitionAffinoidNatIso σ hσ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (A.localDomainSubnetRecognitionEquivalence σ hσ).counitIso
      (RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas) ≪≫
    (RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas).leftUnitor

end AffinoidAtlasPresentation

end Langlands.Analytic
