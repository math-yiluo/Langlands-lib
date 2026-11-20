import Langlands.Geometry.Analytic.AnalyticFibreProductStatement
import Langlands.Geometry.Analytic.FibreProductLocalizedLimit

/-! # Proof: the glued fibre product is a pullback of analytic spaces -/

noncomputable section

universe u

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

variable {A B C : AffinoidAtlasPresentation.{u, u, u} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [T2Space A.space] [T2Space B.space] [T2Space C.space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-! ## Strong maps into the glued presentation are determined by the projections -/

/-- Compatible strong maps into the glued fibre product presentation are jointly
determined by their composites with the two projections, including all bounded
pullbacks. -/
theorem presentationHom_ext {T : AffinoidAtlasPresentation.{u, u, u} K}
    (a b : CompatibleStrongHom T (presentation f g hA hB))
    (hfst : a.comp (fstHom f g hA hB) = b.comp (fstHom f g hA hB))
    (hsnd : a.comp (sndHom f g hA hB) = b.comp (sndHom f g hA hB)) : a = b := by
  have hex : ∀ i : T.atlas.Index, ∃ (J : (presentation f g hA hB).atlas.Index)
      (ha : a.baseMap '' range (T.atlas.chart i) ⊆
        range ((presentation f g hA hB).atlas.chart J))
      (hb : b.baseMap '' range (T.atlas.chart i) ⊆
        range ((presentation f g hA hB).atlas.chart J)),
      a.pullback i J ha = b.pullback i J hb := by
    intro i
    obtain ⟨J, ha⟩ := a.target_exists i
    let p := J.rep
    have hb : b.baseMap '' range (T.atlas.chart i) ⊆
        range ((presentation f g hA hB).atlas.chart J) := by
      rintro _ ⟨x, hx, rfl⟩
      have hax := (mem_range_chart_iff f g p (a.baseMap x)).mp (ha ⟨x, hx, rfl⟩)
      have hfx : fst f g (a.baseMap x) = fst f g (b.baseMap x) :=
        congrArg (fun h => h.baseMap x) hfst
      have hsx : snd f g (a.baseMap x) = snd f g (b.baseMap x) :=
        congrArg (fun h => h.baseMap x) hsnd
      exact (mem_range_chart_iff f g p (b.baseMap x)).mpr ⟨hfx ▸ hax.1, hsx ▸ hax.2⟩
    refine ⟨J, ha, hb, ?_⟩
    have hF : (fstHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart J) ⊆
        range (A.atlas.chart p.1.1) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, rfl⟩
    have hS : (sndHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart J) ⊆
        range (B.atlas.chart p.1.2) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, rfl⟩
    have hα := StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom hfst)
      i p.1.1 (a.toStrongHom.comp_admissible _ i J p.1.1 ha hF)
        (b.toStrongHom.comp_admissible _ i J p.1.1 hb hF)
    have hβ := StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom hsnd)
      i p.1.2 (a.toStrongHom.comp_admissible _ i J p.1.2 ha hS)
        (b.toStrongHom.comp_admissible _ i J p.1.2 hb hS)
    erw [CompatibleStrongHom.comp_pullback a _ i J p.1.1 ha hF,
      CompatibleStrongHom.comp_pullback b _ i J p.1.1 hb hF] at hα
    erw [CompatibleStrongHom.comp_pullback a _ i J p.1.2 ha hS,
      CompatibleStrongHom.comp_pullback b _ i J p.1.2 hb hS] at hβ
    change (a.pullback i J ha).comp (fstPullback f g J p.1.1 hF) =
      (b.pullback i J hb).comp (fstPullback f g J p.1.1 hF) at hα
    change (a.pullback i J ha).comp (sndPullback f g J p.1.2 hS) =
      (b.pullback i J hb).comp (sndPullback f g J p.1.2 hS) at hβ
    dsimp only [fstPullback] at hα
    dsimp only [sndPullback] at hβ
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
      ((congrArg (fun φ => (presentation f g hA hB).atlas.chart J
        (BanachSpectrum.comap φ.toBoundedRingHom s)) he).trans (b.chart_comm i J hb s))
  refine CompatibleStrongHom.ext_of_pullback hb fun i => ?_
  obtain ⟨J, ha, hb, he⟩ := hex i
  exact ⟨J, ha, he⟩

/-! ## The comparison map from the small presentation -/

/-- The good chart domain of an index of the small atlas, as an index of the
glued fibre product atlas (every good chart is a nonempty pair chart). -/
def smallToAtlasIndex (J : (smallPresentation f g hA hB hC).atlas.Index) : AtlasIndex f g :=
  ⟨((equivShrink (LocalAtlasIndex f g)).symm J).val,
    ((equivShrink (LocalAtlasIndex f g)).symm J).property.1,
    ((equivShrink (LocalAtlasIndex f g)).symm J).rep,
    ((equivShrink (LocalAtlasIndex f g)).symm J).range_rep⟩

omit [T2Space A.space] [T2Space B.space] [T2Space C.space] in
theorem range_smallToAtlasIndex_rep (J : (smallPresentation f g hA hB hC).atlas.Index) :
    range ((chartSystem f g).chart (smallToAtlasIndex f g hA hB hC J).rep) =
      range ((chartSystem f g).chart (smallRep f g hA hB hC J)) :=
  (AtlasIndex.range_rep _).trans ((equivShrink (LocalAtlasIndex f g)).symm J).range_rep.symm

/-- The continuous map underlying the comparison: the inverse of the canonical
homeomorphism onto the shrunk quotient. -/
def smallToSpace : C((smallPresentation f g hA hB hC).space, (presentation f g hA hB).space) :=
  ⟨(smallSpaceHomeomorph f g hA hB hC).symm, (smallSpaceHomeomorph f g hA hB hC).symm.continuous⟩

theorem smallToSpace_chart (J : (smallPresentation f g hA hB hC).atlas.Index)
    (x : BanachSpectrum (algebra f g (smallRep f g hA hB hC J))) :
    smallToSpace f g hA hB hC ((smallPresentation f g hA hB hC).atlas.chart J x) =
      (chartSystem f g).chart (smallRep f g hA hB hC J) x :=
  (smallSpaceHomeomorph f g hA hB hC).symm_apply_apply _

theorem smallToSpace_subset (J : (smallPresentation f g hA hB hC).atlas.Index)
    (T : AtlasIndex f g)
    (h : smallToSpace f g hA hB hC '' range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆
      range ((presentation f g hA hB).atlas.chart T)) :
    range ((chartSystem f g).chart (smallRep f g hA hB hC J)) ⊆
      range ((chartSystem f g).chart T.rep) := by
  rintro _ ⟨x, rfl⟩
  exact h ⟨_, ⟨x, rfl⟩, smallToSpace_chart f g hA hB hC J x⟩

theorem smallToSpace_subset_smallToAtlasIndex
    (J : (smallPresentation f g hA hB hC).atlas.Index) :
    smallToSpace f g hA hB hC '' range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆
      range ((presentation f g hA hB).atlas.chart (smallToAtlasIndex f g hA hB hC J)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  change smallToSpace f g hA hB hC ((smallPresentation f g hA hB hC).atlas.chart J x) ∈
    range ((chartSystem f g).chart (smallToAtlasIndex f g hA hB hC J).rep)
  rw [range_smallToAtlasIndex_rep]
  exact ⟨x, (smallToSpace_chart f g hA hB hC J x).symm⟩

/-- The comparison from the small local atlas to the glued fibre product atlas:
the identity of the quotient, with the range restrictions as bounded pullbacks. -/
def smallToPresentation :
    CompatibleStrongHom (smallPresentation f g hA hB hC) (presentation f g hA hB) where
  baseMap := smallToSpace f g hA hB hC
  target_exists J := ⟨smallToAtlasIndex f g hA hB hC J,
    smallToSpace_subset_smallToAtlasIndex f g hA hB hC J⟩
  pullback J T h := rangeRestriction f g (smallToSpace_subset f g hA hB hC J T h)
  chart_comm J T h x := by
    change BanachSpectrum (algebra f g (smallRep f g hA hB hC J)) at x
    exact (chart_rangeRestriction f g _ x).trans (smallToSpace_chart f g hA hB hC J x).symm
  restriction_comm J J' T T' hJ hT h h' := by
    have hJJ' := small_chart_subset f g hA hB hC J J' hJ
    change (rangeRestriction f g hJJ').comp
        (rangeRestriction f g (smallToSpace_subset f g hA hB hC J' T' h')) =
      (rangeRestriction f g (smallToSpace_subset f g hA hB hC J T h)).comp
        (rangeRestriction f g hT)
    exact (rangeRestriction_comp f g hJJ' (smallToSpace_subset f g hA hB hC J' T' h')).symm.trans
      (rangeRestriction_comp f g (smallToSpace_subset f g hA hB hC J T h) hT)
  compatible := by
    refine (StrongHom.hasLocallyCompatiblePullbacks_iff _).mpr ?_
    intro J T T' hT hT'
    let T₀ := smallToAtlasIndex f g hA hB hC J
    have h₀ : range ((chartSystem f g).chart (smallRep f g hA hB hC J)) ⊆
        range ((chartSystem f g).chart T₀.rep) :=
      (range_smallToAtlasIndex_rep f g hA hB hC J).symm.subset
    have hT₀ : range ((presentation f g hA hB).atlas.chart T₀) ⊆
        range ((presentation f g hA hB).atlas.chart T) := by
      change range ((chartSystem f g).chart T₀.rep) ⊆ range ((chartSystem f g).chart T.rep)
      rw [range_smallToAtlasIndex_rep]
      exact smallToSpace_subset f g hA hB hC J T hT
    have hT₀' : range ((presentation f g hA hB).atlas.chart T₀) ⊆
        range ((presentation f g hA hB).atlas.chart T') := by
      change range ((chartSystem f g).chart T₀.rep) ⊆ range ((chartSystem f g).chart T'.rep)
      rw [range_smallToAtlasIndex_rep]
      exact smallToSpace_subset f g hA hB hC J T' hT'
    have e₁ : rangeRestriction f g (smallToSpace_subset f g hA hB hC J T hT) =
        (rangeRestriction f g h₀).comp ((presentation f g hA hB).atlas.restriction T₀ T hT₀) :=
      rangeRestriction_comp f g h₀ hT₀
    have e₂ : rangeRestriction f g (smallToSpace_subset f g hA hB hC J T' hT') =
        (rangeRestriction f g h₀).comp ((presentation f g hA hB).atlas.restriction T₀ T' hT₀') :=
      rangeRestriction_comp f g h₀ hT₀'
    have key := (presentation f g hA hB).atlas.isMapChartChange_restriction T₀ T T' hT₀ hT₀' _
      (rangeRestriction f g h₀)
    change (presentation f g hA hB).atlas.IsMapChartChange T T'
      (algebra f g (smallRep f g hA hB hC J))
      (rangeRestriction f g (smallToSpace_subset f g hA hB hC J T hT))
      (rangeRestriction f g (smallToSpace_subset f g hA hB hC J T' hT'))
    rw [e₁, e₂]
    exact key

/-- The comparison commutes with the first projections. -/
theorem smallToPresentation_comp_fstHom :
    (smallToPresentation f g hA hB hC).comp (fstHom f g hA hB) = smallFstHom f g hA hB hC := by
  refine CompatibleStrongHom.ext_of_pullback (ContinuousMap.ext fun _ => rfl) fun J => ?_
  let p := smallRep f g hA hB hC J
  let T₀ := smallToAtlasIndex f g hA hB hC J
  have h₀ : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart T₀.rep) :=
    (range_smallToAtlasIndex_rep f g hA hB hC J).symm.subset
  have h₁ := smallToSpace_subset_smallToAtlasIndex f g hA hB hC J
  have hF : (fstHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart T₀) ⊆
      range (A.atlas.chart p.1.1) := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ range ((chartSystem f g).chart T₀.rep) at hz
    rw [range_smallToAtlasIndex_rep] at hz
    exact ((mem_range_chart_iff f g p z).mp hz).1
  have hk : ((smallToPresentation f g hA hB hC).comp (fstHom f g hA hB)).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (A.atlas.chart p.1.1) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hF ⟨_, h₁ ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨p.1.1, hk, ?_⟩
  rw [CompatibleStrongHom.comp_pullback (smallToPresentation f g hA hB hC) (fstHom f g hA hB)
    J T₀ p.1.1 h₁ hF hk]
  exact A.atlas.eq_changeMapChart _ _ _ _ _ _
    (isMapChartChange_rangeRestriction_left f g _ p.1.1 _)

/-- The comparison commutes with the second projections. -/
theorem smallToPresentation_comp_sndHom :
    (smallToPresentation f g hA hB hC).comp (sndHom f g hA hB) = smallSndHom f g hA hB hC := by
  refine CompatibleStrongHom.ext_of_pullback (ContinuousMap.ext fun _ => rfl) fun J => ?_
  let p := smallRep f g hA hB hC J
  let T₀ := smallToAtlasIndex f g hA hB hC J
  have h₁ := smallToSpace_subset_smallToAtlasIndex f g hA hB hC J
  have hS : (sndHom f g hA hB).baseMap '' range ((presentation f g hA hB).atlas.chart T₀) ⊆
      range (B.atlas.chart p.1.2) := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ range ((chartSystem f g).chart T₀.rep) at hz
    rw [range_smallToAtlasIndex_rep] at hz
    exact ((mem_range_chart_iff f g p z).mp hz).2
  have hk : ((smallToPresentation f g hA hB hC).comp (sndHom f g hA hB)).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (B.atlas.chart p.1.2) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hS ⟨_, h₁ ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨p.1.2, hk, ?_⟩
  rw [CompatibleStrongHom.comp_pullback (smallToPresentation f g hA hB hC) (sndHom f g hA hB)
    J T₀ p.1.2 h₁ hS hk]
  exact B.atlas.eq_changeMapChart _ _ _ _ _ _
    (isMapChartChange_rangeRestriction_right f g _ p.1.2 _)

end FibreProduct

namespace SaturatedAtlasPresentation

variable {X Y S : SaturatedAtlasPresentation.{u, u, u} K}

/-- The two constructions of the original compatible map of a saturated morphism
agree. -/
theorem compatibleMap_eq_geometricCompatibleMap (f : X ⟶ S) :
    compatibleMap f = geometricCompatibleMap f := by
  apply CompatibleStrongHom.saturationExtensionEquiv.injective
  change (compatibleMap f).saturationExtension = (geometricCompatibleMap f).saturationExtension
  let F : ofSaturation X.presentation ⟶ ofSaturation S.presentation :=
    (geometricCompatibleMap f).saturationExtension
  have hf : F ≫ S.saturationIso.hom = X.saturationIso.hom ≫ f :=
    (saturationComparisonNatIso (K := K)).hom.naturality f
  rw [saturationExtension_compatibleMap]
  change X.saturationIso.hom ≫ f ≫ S.saturationIso.inv = F
  rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [T2Space X.presentation.space] [T2Space Y.presentation.space]
  [T2Space S.presentation.space] (f : X ⟶ S) (g : Y ⟶ S)

/-- The glued projections are strictly jointly monic for arbitrary saturated
sources, as equality of entire strong maps. -/
theorem fibreProduct_hom_ext {T : SaturatedAtlasPresentation.{u, u, u} K}
    (a b : T ⟶ fibreProduct f g)
    (hfst : a ≫ fibreProductFst f g = b ≫ fibreProductFst f g)
    (hsnd : a ≫ fibreProductSnd f g = b ≫ fibreProductSnd f g) : a = b := by
  let a' := (T.saturationIso.hom ≫ a).originalRestriction
  let b' := (T.saturationIso.hom ≫ b).originalRestriction
  have ha' : a'.saturationExtension = (T.saturationIso.hom ≫ a) :=
    StrongHom.saturationExtension_originalRestriction _
  have hb' : b'.saturationExtension = (T.saturationIso.hom ≫ b) :=
    StrongHom.saturationExtension_originalRestriction _
  let pF : fibreProduct f g ⟶ ofSaturation X.presentation := fstSaturated f g
  let pS : fibreProduct f g ⟶ ofSaturation Y.presentation := sndSaturated f g
  have hF : a'.comp (FibreProduct.fstHom (compatibleMap f) (compatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains) =
      b'.comp (FibreProduct.fstHom (compatibleMap f) (compatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains) := by
    apply CompatibleStrongHom.saturationExtensionEquiv.injective
    change (a'.comp (FibreProduct.fstHom (compatibleMap f) (compatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains)).saturationExtension =
      (b'.comp (FibreProduct.fstHom (compatibleMap f) (compatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains)).saturationExtension
    rw [CompatibleStrongHom.saturationExtension_comp, CompatibleStrongHom.saturationExtension_comp]
    rw [ha', hb']
    change (T.saturationIso.hom ≫ a) ≫ pF = (T.saturationIso.hom ≫ b) ≫ pF
    apply (cancel_mono X.saturationIso.hom).mp
    have hproj : a ≫ (pF ≫ X.saturationIso.hom) = b ≫ (pF ≫ X.saturationIso.hom) := hfst
    simpa only [Category.assoc] using congrArg (fun h => T.saturationIso.hom ≫ h) hproj
  have hS : a'.comp (FibreProduct.sndHom (compatibleMap f) (compatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains) =
      b'.comp (FibreProduct.sndHom (compatibleMap f) (compatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains) := by
    apply CompatibleStrongHom.saturationExtensionEquiv.injective
    change (a'.comp (FibreProduct.sndHom (compatibleMap f) (compatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains)).saturationExtension =
      (b'.comp (FibreProduct.sndHom (compatibleMap f) (compatibleMap g)
        X.hasAllLocalDomains Y.hasAllLocalDomains)).saturationExtension
    rw [CompatibleStrongHom.saturationExtension_comp, CompatibleStrongHom.saturationExtension_comp]
    rw [ha', hb']
    change (T.saturationIso.hom ≫ a) ≫ pS = (T.saturationIso.hom ≫ b) ≫ pS
    apply (cancel_mono Y.saturationIso.hom).mp
    have hproj : a ≫ (pS ≫ Y.saturationIso.hom) = b ≫ (pS ≫ Y.saturationIso.hom) := hsnd
    simpa only [Category.assoc] using congrArg (fun h => T.saturationIso.hom ≫ h) hproj
  have he := FibreProduct.presentationHom_ext (compatibleMap f) (compatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains a' b' hF hS
  have he' := congrArg CompatibleStrongHom.saturationExtension he
  exact (cancel_epi T.saturationIso.hom).mp (ha'.symm.trans (he'.trans hb'))

/-- A strong comparison map from the small fibre product to the glued one,
compatible with both projections. -/
theorem exists_smallFibreProduct_comparison :
    ∃ β : smallFibreProduct f g ⟶ fibreProduct f g,
      β ≫ fibreProductFst f g = smallFibreProductFst f g ∧
        β ≫ fibreProductSnd f g = smallFibreProductSnd f g := by
  show ∃ β : smallFibreProduct f g ⟶ ofSaturation (FibreProduct.presentation (compatibleMap f)
      (compatibleMap g) X.hasAllLocalDomains Y.hasAllLocalDomains),
      β ≫ ((FibreProduct.fstHom (compatibleMap f) (compatibleMap g) X.hasAllLocalDomains
        Y.hasAllLocalDomains).saturationExtension ≫ X.saturationIso.hom) =
          smallFibreProductFst f g ∧
      β ≫ ((FibreProduct.sndHom (compatibleMap f) (compatibleMap g) X.hasAllLocalDomains
        Y.hasAllLocalDomains).saturationExtension ≫ Y.saturationIso.hom) =
          smallFibreProductSnd f g
  rw [compatibleMap_eq_geometricCompatibleMap f, compatibleMap_eq_geometricCompatibleMap g]
  let F := geometricCompatibleMap f
  let G := geometricCompatibleMap g
  let β : smallFibreProduct f g ⟶ ofSaturation (FibreProduct.presentation F G
      X.hasAllLocalDomains Y.hasAllLocalDomains) :=
    (FibreProduct.smallToPresentation F G X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains).saturationExtension
  let sF : smallFibreProduct f g ⟶ ofSaturation X.presentation :=
    (FibreProduct.smallFstHom F G X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains).saturationExtension
  let sS : smallFibreProduct f g ⟶ ofSaturation Y.presentation :=
    (FibreProduct.smallSndHom F G X.hasAllLocalDomains Y.hasAllLocalDomains
      S.hasAllLocalDomains).saturationExtension
  have h₁ : β ≫ (FibreProduct.fstHom F G X.hasAllLocalDomains
      Y.hasAllLocalDomains).saturationExtension = sF := by
    have h := congrArg CompatibleStrongHom.saturationExtension
      (FibreProduct.smallToPresentation_comp_fstHom F G X.hasAllLocalDomains
        Y.hasAllLocalDomains S.hasAllLocalDomains)
    rw [CompatibleStrongHom.saturationExtension_comp] at h
    exact h
  have h₂ : β ≫ (FibreProduct.sndHom F G X.hasAllLocalDomains
      Y.hasAllLocalDomains).saturationExtension = sS := by
    have h := congrArg CompatibleStrongHom.saturationExtension
      (FibreProduct.smallToPresentation_comp_sndHom F G X.hasAllLocalDomains
        Y.hasAllLocalDomains S.hasAllLocalDomains)
    rw [CompatibleStrongHom.saturationExtension_comp] at h
    exact h
  refine ⟨β, ?_, ?_⟩
  · refine (Category.assoc β _ X.saturationIso.hom).symm.trans ?_
    exact (congrArg (fun h => h ≫ X.saturationIso.hom) h₁).trans rfl
  · refine (Category.assoc β _ Y.saturationIso.hom).symm.trans ?_
    exact (congrArg (fun h => h ≫ Y.saturationIso.hom) h₂).trans rfl

/-- Every strong cone admits a strong lift into the glued fibre product after a
quasi-isomorphic source refinement. -/
theorem fibreProduct_exists_refinedLift {T : SaturatedAtlasPresentation.{u, u, u} K}
    (a : T ⟶ X) (b : T ⟶ Y) (hab : a ≫ f = b ≫ g) :
    ∃ (R : SaturatedAtlasPresentation.{u, u, u} K) (s : R ⟶ T), s.IsQuasiIso ∧
      ∃ l : R ⟶ fibreProduct f g,
        l ≫ fibreProductFst f g = s ≫ a ∧ l ≫ fibreProductSnd f g = s ≫ b := by
  obtain ⟨R, s, hs, l, hl₁, hl₂⟩ := smallFibreProduct_exists_refinedLift f g a b hab
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_smallFibreProduct_comparison f g
  exact ⟨R, s, hs, l ≫ β, by rw [Category.assoc, hβ₁, hl₁], by rw [Category.assoc, hβ₂, hl₂]⟩

/-- The glued fibre product square has all refined strong universal-property
data. -/
theorem fibreProduct_isRefinedStrongPullback :
    IsRefinedStrongPullback (fibreProductFst f g) (fibreProductSnd f g) f g :=
  ⟨fibreProduct_condition f g,
    fun _ a b hab => fibreProduct_exists_refinedLift f g a b hab,
    fun _ a b hp hq => fibreProduct_hom_ext f g a b hp hq⟩

/-- Berkovich 1993, Proposition 1.4.1: the glued fibre product is a pullback in the
localized category of analytic spaces. -/
theorem fibreProductPullback : FibreProductPullbackStatement.{u} := by
  intro K' _ _ _ X' Y' S' _ _ _ f' g'
  exact (fibreProduct_isRefinedStrongPullback f' g').isPullback

end SaturatedAtlasPresentation

end Langlands.Analytic
