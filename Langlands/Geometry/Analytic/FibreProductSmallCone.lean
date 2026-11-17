import Langlands.Geometry.Analytic.FibreProductSmallSquare
import Langlands.Geometry.Analytic.StrongSourceRestriction
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Strict uniqueness for the actual small fibre-product cone -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

variable {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- The exact pair-chart image criterion survives the canonical shrinking. -/
theorem mem_range_small_chart_iff (J : (smallPresentation f g hA hB hC).atlas.Index)
    (z : (smallPresentation f g hA hB hC).space) :
    z ∈ range ((smallPresentation f g hA hB hC).atlas.chart J) ↔
      smallFstBase f g hA hB hC z ∈ range (A.atlas.chart (smallRep f g hA hB hC J).val.1) ∧
      smallSndBase f g hA hB hC z ∈ range (B.atlas.chart (smallRep f g hA hB hC J).val.2) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(smallFstBase_chart f g hA hB hC J x).symm ▸ ⟨_, rfl⟩,
      (smallSndBase_chart f g hA hB hC J x).symm ▸ ⟨_, rfl⟩⟩
  · intro hz
    obtain ⟨x, hx⟩ := (mem_range_chart_iff f g (smallRep f g hA hB hC J)
      ((smallSpaceHomeomorph f g hA hB hC).symm z)).mpr hz
    exact ⟨x, (congrArg (smallSpaceHomeomorph f g hA hB hC) hx).trans
      ((smallSpaceHomeomorph f g hA hB hC).apply_symm_apply z)⟩

/-- Complete strong maps into the actual small atlas are jointly determined
by the two complete projections, including all algebraic coefficients. -/
theorem smallHom_ext {T : AffinoidAtlasPresentation.{u, v, v} K}
    (a b : CompatibleStrongHom T (smallPresentation f g hA hB hC))
    (hfst : a.comp (smallFstHom f g hA hB hC) = b.comp (smallFstHom f g hA hB hC))
    (hsnd : a.comp (smallSndHom f g hA hB hC) = b.comp (smallSndHom f g hA hB hC)) : a = b := by
  have hex : ∀ i : T.atlas.Index, ∃ (J : (smallPresentation f g hA hB hC).atlas.Index)
      (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range ((smallPresentation f g hA hB hC).atlas.chart J))
      (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range ((smallPresentation f g hA hB hC).atlas.chart J)),
      a.pullback i J ha = b.pullback i J hb := by
    intro i
    obtain ⟨J, ha⟩ := a.target_exists i
    let p := smallRep f g hA hB hC J
    have hb : b.baseMap '' range (T.atlas.chart i) ⊆
        range ((smallPresentation f g hA hB hC).atlas.chart J) := by
      rintro _ ⟨x, hx, rfl⟩
      have hax := (mem_range_small_chart_iff f g hA hB hC J (a.baseMap x)).mp (ha ⟨x, hx, rfl⟩)
      have hfx : smallFstBase f g hA hB hC (a.baseMap x) =
          smallFstBase f g hA hB hC (b.baseMap x) :=
        congrArg (fun h => h.baseMap x) hfst
      have hsx : smallSndBase f g hA hB hC (a.baseMap x) =
          smallSndBase f g hA hB hC (b.baseMap x) :=
        congrArg (fun h => h.baseMap x) hsnd
      exact (mem_range_small_chart_iff f g hA hB hC J (b.baseMap x)).mpr
        ⟨hfx ▸ hax.1, hsx ▸ hax.2⟩
    refine ⟨J, ha, hb, ?_⟩
    have hF : (smallFstHom f g hA hB hC).baseMap ''
        range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (A.atlas.chart p.val.1) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (smallFstBase_chart f g hA hB hC J x).symm ▸ ⟨_, rfl⟩
    have hS : (smallSndHom f g hA hB hC).baseMap ''
        range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (B.atlas.chart p.val.2) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact (smallSndBase_chart f g hA hB hC J x).symm ▸ ⟨_, rfl⟩
    have hα := StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom hfst)
      i p.val.1 (a.toStrongHom.comp_admissible _ i J p.val.1 ha hF)
        (b.toStrongHom.comp_admissible _ i J p.val.1 hb hF)
    have hβ := StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom hsnd)
      i p.val.2 (a.toStrongHom.comp_admissible _ i J p.val.2 ha hS)
        (b.toStrongHom.comp_admissible _ i J p.val.2 hb hS)
    erw [CompatibleStrongHom.comp_pullback a _ i J p.val.1 ha hF,
      CompatibleStrongHom.comp_pullback b _ i J p.val.1 hb hF] at hα
    erw [CompatibleStrongHom.comp_pullback a _ i J p.val.2 ha hS,
      CompatibleStrongHom.comp_pullback b _ i J p.val.2 hb hS] at hβ
    change (a.pullback i J ha).comp (smallFstPullback f g hA hB hC J p.val.1 hF) =
      (b.pullback i J hb).comp (smallFstPullback f g hA hB hC J p.val.1 hF) at hα
    change (a.pullback i J ha).comp (smallSndPullback f g hA hB hC J p.val.2 hS) =
      (b.pullback i J hb).comp (smallSndPullback f g hA hB hC J p.val.2 hS) at hβ
    dsimp only [smallFstPullback] at hα
    dsimp only [smallSndPullback] at hβ
    rw [A.atlas.changeMapChart_self] at hα
    rw [B.atlas.changeMapChart_self] at hβ
    exact AffinoidPushout.hom_ext (leftBase f g p) (rightBase f g p) (T.atlas.algebra i) _ _ hα hβ
  have hb : a.baseMap = b.baseMap := by
    apply ContinuousMap.ext
    intro x
    have hx : x ∈ ⋃₀ range (fun i => range (T.atlas.chart i)) := by
      rw [T.atlas.isNet_chartFamily.1.covers]
      exact mem_univ x
    obtain ⟨_, ⟨i, rfl⟩, s, rfl⟩ := hx
    obtain ⟨J, ha, hb, he⟩ := hex i
    exact (a.chart_comm i J ha s).symm.trans
      ((congrArg (fun φ => (smallPresentation f g hA hB hC).atlas.chart J
        (BanachSpectrum.comap φ.toBoundedRingHom s)) he).trans (b.chart_comm i J hb s))
  refine CompatibleStrongHom.ext_of_pullback hb fun i => ?_
  obtain ⟨J, ha, hb, he⟩ := hex i
  exact ⟨J, ha, he⟩

end FibreProduct

namespace SaturatedAtlasPresentation

variable {X Y S : SaturatedAtlasPresentation.{u, v, v} K}
  (f : X ⟶ S) (g : Y ⟶ S)
  [Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap f) (geometricCompatibleMap g)).Space]

/-- The actual commutative cone; no limiting property is assumed. -/
def smallFibreProductCone : PullbackCone f g :=
  PullbackCone.mk (smallFibreProductFst f g) (smallFibreProductSnd f g) (smallFibreProduct_condition f g)

/-- The actual saturated projections are strictly jointly monic for arbitrary
saturated sources, as equality of entire strong maps. -/
theorem smallFibreProduct_hom_ext {T : SaturatedAtlasPresentation.{u, v, v} K}
    (a b : T ⟶ smallFibreProduct f g)
    (hfst : a ≫ smallFibreProductFst f g = b ≫ smallFibreProductFst f g)
    (hsnd : a ≫ smallFibreProductSnd f g = b ≫ smallFibreProductSnd f g) : a = b := by
  let a' := (T.saturationIso.hom ≫ a).originalRestriction
  let b' := (T.saturationIso.hom ≫ b).originalRestriction
  have ha' : a'.saturationExtension = (T.saturationIso.hom ≫ a) :=
    StrongHom.saturationExtension_originalRestriction _
  have hb' : b'.saturationExtension = (T.saturationIso.hom ≫ b) :=
    StrongHom.saturationExtension_originalRestriction _
  let pF : smallFibreProduct f g ⟶ ofSaturation X.presentation :=
    (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension
  let pS : smallFibreProduct f g ⟶ ofSaturation Y.presentation :=
    (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains).saturationExtension
  have hF : a'.comp (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains) =
      b'.comp (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains) := by
    apply CompatibleStrongHom.saturationExtensionEquiv.injective
    change (a'.comp (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)).saturationExtension =
      (b'.comp (FibreProduct.smallFstHom (geometricCompatibleMap f) (geometricCompatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)).saturationExtension
    rw [CompatibleStrongHom.saturationExtension_comp, CompatibleStrongHom.saturationExtension_comp]
    rw [ha', hb']
    change (T.saturationIso.hom ≫ a) ≫ pF = (T.saturationIso.hom ≫ b) ≫ pF
    apply (cancel_mono X.saturationIso.hom).mp
    have hproj : a ≫ (pF ≫ X.saturationIso.hom) = b ≫ (pF ≫ X.saturationIso.hom) := hfst
    simpa only [Category.assoc] using congrArg (fun h => T.saturationIso.hom ≫ h) hproj
  have hS : a'.comp (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains) =
      b'.comp (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains) := by
    apply CompatibleStrongHom.saturationExtensionEquiv.injective
    change (a'.comp (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)).saturationExtension =
      (b'.comp (FibreProduct.smallSndHom (geometricCompatibleMap f) (geometricCompatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains)).saturationExtension
    rw [CompatibleStrongHom.saturationExtension_comp, CompatibleStrongHom.saturationExtension_comp]
    rw [ha', hb']
    change (T.saturationIso.hom ≫ a) ≫ pS = (T.saturationIso.hom ≫ b) ≫ pS
    apply (cancel_mono Y.saturationIso.hom).mp
    have hproj : a ≫ (pS ≫ Y.saturationIso.hom) = b ≫ (pS ≫ Y.saturationIso.hom) := hsnd
    simpa only [Category.assoc] using congrArg (fun h => T.saturationIso.hom ≫ h) hproj
  have he := FibreProduct.smallHom_ext (geometricCompatibleMap f) (geometricCompatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains S.hasAllLocalDomains a' b' hF hS
  have he' := congrArg CompatibleStrongHom.saturationExtension he
  exact (cancel_epi T.saturationIso.hom).mp (ha'.symm.trans (he'.trans hb'))

end SaturatedAtlasPresentation

end Langlands.Analytic
