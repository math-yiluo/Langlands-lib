import Langlands.Geometry.Analytic.FullRecognitionStrongInverse
import Langlands.Geometry.Analytic.AdmissibleRecognitionSubatlas
import Langlands.Geometry.Analytic.FullRecognitionControlledFinitePairs
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # Saturated recognition cospans with literal finite pointed chart pairs -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The full recognition of an actual saturated presentation, on the same
literal ambient space and with its proved full-domain closure. -/
abbrev recognitionBase (A : SaturatedAtlasPresentation.{u, v, v} K) :
    SaturatedAtlasPresentation.{u, v, v} K :=
  SaturatedAtlasPresentation.ofFullRecognition A.presentation

variable {A B C : SaturatedAtlasPresentation.{u, v, v} K}

/-- The recognized source charts of the canonical extension that admit a
recognized target. -/
def recognitionSource (f : A ⟶ B) : SaturatedAtlasPresentation.{u, v, v} K where
  presentation := ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f).recognitionSource
  hasAllLocalDomains :=
    ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f).recognitionSource_hasAllLocalDomains

/-- All original chart algebras and bounded pullbacks of the full-recognition
pair system are retained in the actual saturated category. -/
def recognitionMap (f : A ⟶ B) : recognitionSource f ⟶ recognitionBase B :=
  ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f).recognitionMap

/-- Forward full-domain comparison from an original saturated source. -/
def recognitionSourceComparison (f : A ⟶ B) : A ⟶ recognitionSource f :=
  A.saturationIso.inv ≫
    (show ofSaturation A.presentation ⟶ recognitionSource f from
      ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f).recognitionSourceComparison)

/-- Forward full-domain comparison from the original base to its full
recognition. -/
def recognitionBaseComparison (A : SaturatedAtlasPresentation.{u, v, v} K) :
    A ⟶ recognitionBase A :=
  A.saturationIso.inv ≫
    (show ofSaturation A.presentation ⟶ recognitionBase A from
      A.presentation.localDomainToFullRecognition)

theorem recognitionSourceComparison_isQuasiIso (f : A ⟶ B) :
    (recognitionSourceComparison f).IsQuasiIso :=
  A.presentation.isQuasiIso_directToSaturation.saturatedComp
    (((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f).recognitionSourceComparison_isQuasiIso)
    A.hasAllLocalDomains A.presentation.atlas.saturatedAtlas_hasAllLocalDomains

theorem recognitionBaseComparison_isQuasiIso (A : SaturatedAtlasPresentation.{u, v, v} K) :
    (recognitionBaseComparison A).IsQuasiIso :=
  A.presentation.isQuasiIso_directToSaturation.saturatedComp
    A.presentation.localDomainToFullRecognition_isQuasiIso
    A.hasAllLocalDomains A.presentation.atlas.saturatedAtlas_hasAllLocalDomains

@[simp]
theorem recognitionMap_baseMap (f : A ⟶ B) :
    (recognitionMap f).baseMap = f.baseMap := rfl

@[simp]
theorem recognitionSourceComparison_baseMap (f : A ⟶ B) :
    (recognitionSourceComparison f).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem recognitionBaseComparison_baseMap (A : SaturatedAtlasPresentation.{u, v, v} K) :
    (recognitionBaseComparison A).baseMap = ContinuousMap.id A.presentation.space := rfl

/-- The whole original map is recovered by the recognition comparison
square, using complete bounded-map naturality of canonical saturation. -/
theorem recognitionMap_square (f : A ⟶ B) :
    recognitionSourceComparison f ≫ recognitionMap f = f ≫ recognitionBaseComparison B := by
  let F : ofSaturation A.presentation ⟶ ofSaturation B.presentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  have hF :
      (show ofSaturation A.presentation ⟶ recognitionSource f from F.recognitionSourceComparison) ≫
        recognitionMap f =
      F ≫ (show ofSaturation B.presentation ⟶ recognitionBase B from
        B.presentation.localDomainToFullRecognition) :=
    F.recognitionSourceComparison_comp
  have hc : A.saturationIso.inv ≫ F = f ≫ B.saturationIso.inv := by
    dsimp only [F]
    rw [saturationExtension_eq_conjugate f]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let J : ofSaturation B.presentation ⟶ recognitionBase B :=
    B.presentation.localDomainToFullRecognition
  calc
    recognitionSourceComparison f ≫ recognitionMap f =
        A.saturationIso.inv ≫
          ((show ofSaturation A.presentation ⟶ recognitionSource f from
            F.recognitionSourceComparison) ≫ recognitionMap f) :=
      Category.assoc _ _ _
    _ = A.saturationIso.inv ≫ (F ≫ J) :=
      congrArg (fun t : ofSaturation A.presentation ⟶ recognitionBase B =>
        A.saturationIso.inv ≫ t) hF
    _ = (A.saturationIso.inv ≫ F) ≫ J := (Category.assoc _ _ _).symm
    _ = (f ≫ B.saturationIso.inv) ≫ J :=
      congrArg (fun t : A ⟶ ofSaturation B.presentation => t ≫ J) hc
    _ = f ≫ recognitionBaseComparison B := Category.assoc _ _ _

/-- Full quasi-isomorphism comparisons preserve and reflect the canonical
strong etale predicate of the entire original map. -/
theorem recognitionMap_strongEtale_iff (f : A ⟶ B) :
    strongEtale (recognitionMap f) ↔ strongEtale f := by
  calc
    strongEtale (recognitionMap f) ↔
        strongEtale (recognitionSourceComparison f ≫ recognitionMap f) :=
      (strongEtale_precomp_quasiIso_iff (recognitionSourceComparison_isQuasiIso f)).symm
    _ ↔ strongEtale (f ≫ recognitionBaseComparison B) := by rw [recognitionMap_square]
    _ ↔ strongEtale f :=
      strongEtale_postcomp_quasiIso_iff (recognitionBaseComparison_isQuasiIso B)

/-- Actual localization isomorphisms from the original source and base. -/
def recognitionSourceIso (f : A ⟶ B) :
    localizationFunctor.obj A ≅ localizationFunctor.obj (recognitionSource f) :=
  localizedQuasiIso (recognitionSourceComparison f) (recognitionSourceComparison_isQuasiIso f)

def recognitionBaseIso (A : SaturatedAtlasPresentation.{u, v, v} K) :
    localizationFunctor.obj A ≅ localizationFunctor.obj (recognitionBase A) :=
  localizedQuasiIso (recognitionBaseComparison A) (recognitionBaseComparison_isQuasiIso A)

theorem recognitionMap_localized_square (f : A ⟶ B) :
    (recognitionSourceIso f).hom ≫ localizationFunctor.map (recognitionMap f) =
      localizationFunctor.map f ≫ (recognitionBaseIso B).hom := by
  change localizationFunctor.map (recognitionSourceComparison f) ≫ _ =
    _ ≫ localizationFunctor.map (recognitionBaseComparison B)
  rw [← Functor.map_comp, ← Functor.map_comp, recognitionMap_square]

/-- Literal original chart pairs through every compatible ambient pair,
with a finite Banach first bounded map etale at its chosen spectrum point.
The equality of chosen image points is in the actual common base spectrum. -/
def HasPointedFiniteEtalePairs (f : A ⟶ C) (g : B ⟶ C) : Prop :=
  ∀ (y : A.presentation.space) (z : B.presentation.space), f.baseMap y = g.baseMap z →
    ∃ (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
      (k : C.presentation.atlas.Index)
      (hi : f.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (C.presentation.atlas.chart k))
      (hj : g.baseMap '' range (B.presentation.atlas.chart j) ⊆ range (C.presentation.atlas.chart k))
      (s : BanachSpectrum (A.presentation.atlas.algebra i))
      (r : BanachSpectrum (B.presentation.atlas.algebra j)),
      A.presentation.atlas.chart i s = y ∧ B.presentation.atlas.chart j r = z ∧
      (f.pullback i k hi).IsFiniteBanach ∧ (f.pullback i k hi).IsEtaleAtPoint s ∧
      BanachSpectrum.comap (f.pullback i k hi).toBoundedRingHom s =
        BanachSpectrum.comap (g.pullback j k hj).toBoundedRingHom r

/-- Canonical strong etaleness supplies actual finite original chart pairs
for the recognition-selected cospan, without a separate chart-size adapter. -/
theorem recognitionMaps_hasPointedFiniteEtalePairs
    (f : A ⟶ C) (g : B ⟶ C) (hf : strongEtale f) :
    HasPointedFiniteEtalePairs (recognitionMap f) (recognitionMap g) := by
  intro y z hyz
  let F : StrongHom A.presentation.saturatedPresentation C.presentation.saturatedPresentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  let G : StrongHom B.presentation.saturatedPresentation C.presentation.saturatedPresentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map g
  have hF : F.IsEtaleAllPieces := hf
  obtain ⟨t, ht⟩ := C.presentation.atlas.exists_mem_range_chart (F.baseMap y)
  obtain ⟨j, hzj⟩ := B.presentation.atlas.saturatedAtlas.exists_mem_range_chart z
  obtain ⟨P, R, W, h, h', s, r, hs, hr, hfinite, hetale, -, -, -, -, hsr⟩ :=
    AffinoidAtlasPresentation.StrongHom.controlledFiniteEtalePairs
      A.presentation C.presentation B.presentation F G y z (hF y) hyz
      univ (Filter.univ_mem) t ht univ (Filter.univ_mem) j hzj
  exact ⟨F.recognitionSourceIndex P W h, G.recognitionSourceIndex R W h', W,
    h, h', s, r, hs, hr, hfinite, hetale, hsr⟩

end Langlands.Analytic.SaturatedAtlasPresentation
