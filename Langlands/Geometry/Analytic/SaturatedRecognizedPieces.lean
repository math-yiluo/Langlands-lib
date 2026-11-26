import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition
import Langlands.Geometry.Analytic.SaturatedStrongCategory

/-! # Étaleness over all recognized pieces, stated on saturated presentations -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

/-- The canonical strong map from an atlas presentation to its recognition
atlas, on the identity of the ambient space; every bounded pullback is the
original-chart restriction of a recognized subset. Applied to a constructed
saturation, this is `localDomainToFullRecognition`. -/
def recognitionInclusion (T : AffinoidAtlasPresentation.{u, v, v} K) :
    StrongHom T T.recognitionPresentation where
  baseMap := ContinuousMap.id T.space
  target_exists S := by
    refine ⟨T.atlas.originalRecognitionIndex S, ?_⟩
    change id '' Set.range (T.atlas.chart S) ⊆
      Set.range (T.atlas.recognitionAtlas.chart (T.atlas.originalRecognitionIndex S))
    rw [Set.image_id, T.atlas.recognitionAtlas_original_range]
  pullback S V h := V.originalRestriction S (by
    rw [← V.range_chart]
    exact fun x hx => h ⟨x, hx, rfl⟩)
  chart_comm S V h x := V.chart_originalRestriction S _ x
  restriction_comm S T' U V hST hUV hSU hTV := by
    change T.atlas.RecognizedSubset at U V
    have hUV' : U.locus ⊆ V.locus := by
      rw [← U.range_chart, ← V.range_chart]
      exact hUV
    have hSU' : Set.range (T.atlas.chart S) ⊆ U.locus := by
      rw [← U.range_chart]
      exact fun x hx => hSU ⟨x, hx, rfl⟩
    have hTV' : Set.range (T.atlas.chart T') ⊆ V.locus := by
      rw [← V.range_chart]
      exact fun x hx => hTV ⟨x, hx, rfl⟩
    exact (V.originalRestriction_naturality T' S hTV' (hSU'.trans hUV') hST).trans
      (U.originalRestriction_comp_restriction V hUV' S hSU').symm

end AffinoidAtlasPresentation

namespace SaturatedAtlasPresentation

open AffinoidAtlasPresentation

variable {A B : SaturatedAtlasPresentation.{u, v, v} K}

/-- A strong map of saturated presentations followed by the canonical map of
the target into its recognition atlas. -/
def toRecognitionTarget (g : StrongHom A.presentation B.presentation) :
    StrongHom A.presentation B.presentation.recognitionPresentation :=
  g.saturatedComp B.presentation.recognitionInclusion A.hasAllLocalDomains
    B.hasAllLocalDomains

/-- The extension of a strong map of saturated presentations to all pairs of
recognized affinoid subsets of the source and target atlases. -/
def recognitionPairs (g : StrongHom A.presentation B.presentation) :
    AdmissiblePairSystem A.presentation.recognitionPresentation
      B.presentation.recognitionPresentation :=
  (toRecognitionTarget g).recognizedSourceExtension

/-- `g` induces a finite morphism from `V` to `U`, tested on the recognized
subsets of the atlases of the saturated presentations themselves. -/
def IsFiniteOverPieces (g : StrongHom A.presentation B.presentation)
    (V : Set A.presentation.space) (U : Set B.presentation.space) : Prop :=
  g.baseMap '' V ⊆ U ∧
    ∀ W : B.presentation.atlas.RecognizedSubset, W.locus ⊆ U →
      ∃ (V' : A.presentation.atlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
          ((recognitionPairs g).pullback V' W h).IsFiniteBanach

/-- Berkovich's Proposition 3.2.3(b) for a pointwise property `Q` of finite
affinoid maps, stated on the atlases of the saturated presentations. -/
def HasRecognizedPiecesAt
    (Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop)
    (g : StrongHom A.presentation B.presentation) (y : A.presentation.space) : Prop :=
  ∃ (V : Set A.presentation.space) (U : Set B.presentation.space),
    IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ IsFiniteOverPieces g V U ∧
    ∀ W : B.presentation.atlas.RecognizedSubset, W.locus ⊆ U → g.baseMap y ∈ W.locus →
      ∀ (V' : A.presentation.atlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, V'.chart s = y →
            Q ((recognitionPairs g).pullback V' W h) s

/-- Flatness at a point over all recognized pieces. -/
def IsFlatOnRecognizedPiecesAt (g : StrongHom A.presentation B.presentation)
    (y : A.presentation.space) : Prop :=
  HasRecognizedPiecesAt (fun _ _ f s => f.IsFlatAtPoint s) g y

/-- Unramifiedness at a point over all recognized pieces. -/
def IsUnramifiedOnRecognizedPiecesAt (g : StrongHom A.presentation B.presentation)
    (y : A.presentation.space) : Prop :=
  HasRecognizedPiecesAt (fun _ _ f s => f.IsUnramifiedAtPoint s) g y

/-- Étaleness at a point over all recognized pieces: an open neighbourhood of
unramified and flat points. -/
def IsEtaleOnRecognizedPiecesAt (g : StrongHom A.presentation B.presentation)
    (y : A.presentation.space) : Prop :=
  ∃ V : Set A.presentation.space, IsOpen V ∧ y ∈ V ∧
    ∀ y' ∈ V, IsUnramifiedOnRecognizedPiecesAt g y' ∧ IsFlatOnRecognizedPiecesAt g y'

/-- Étale morphisms of saturated presentations over all recognized pieces of
their own atlases. -/
def IsEtaleOnRecognizedPieces (g : StrongHom A.presentation B.presentation) : Prop :=
  ∀ y, IsEtaleOnRecognizedPiecesAt g y

end SaturatedAtlasPresentation

namespace AffinoidAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- On a constructed saturation, the recognition inclusion is literally the
canonical map into the full recognition atlas. -/
theorem recognitionInclusion_saturatedPresentation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    A.saturatedPresentation.recognitionInclusion = A.localDomainToFullRecognition :=
  rfl

/-- On constructed saturations, the intrinsic pair system is literally the
full-recognition pair system. -/
theorem StrongHom.recognitionPairs_ofSaturation
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    SaturatedAtlasPresentation.recognitionPairs
      (A := SaturatedAtlasPresentation.ofSaturation A)
      (B := SaturatedAtlasPresentation.ofSaturation B) g = g.fullRecognitionPairs :=
  rfl

namespace StrongHom

/-- The all-pieces predicate of a map between constructed saturations is,
by definition, the intrinsic predicate of the two saturated presentations. The
original presentations enter only through their saturations. -/
theorem isEtaleAllPieces_iff_isEtaleOnRecognizedPieces
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    g.IsEtaleAllPieces ↔ SaturatedAtlasPresentation.IsEtaleOnRecognizedPieces
      (A := SaturatedAtlasPresentation.ofSaturation A)
      (B := SaturatedAtlasPresentation.ofSaturation B) g :=
  Iff.rfl

end StrongHom
end AffinoidAtlasPresentation

end Langlands.Analytic
