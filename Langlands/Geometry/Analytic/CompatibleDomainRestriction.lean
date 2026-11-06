import Langlands.Geometry.Analytic.OriginalDomainStrongRestriction
import Langlands.Geometry.Analytic.CompatibleStrongCategory
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms

/-! # Compatible strong maps between actual original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Every contained original source chart admits a containing original
 target chart which is itself contained in the target domain. -/
def HasDomainTargets (f : StrongHom A B) (S : Set A.space) (T : Set B.space) : Prop :=
  ∀ c : A.atlas.SubspaceChart S, ∃ d : B.atlas.SubspaceChart T,
    f.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart d.val)

/-- Restrict the supplied continuous map to the actual induced subspaces. -/
def domainBaseMap (f : StrongHom A B) (S : Set A.space) (T : Set B.space)
    (hST : f.baseMap '' S ⊆ T) : C(S, T) :=
  ⟨fun x => ⟨f.baseMap x.val, hST ⟨x.val, x.property, rfl⟩⟩,
    (f.baseMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem domainBaseMap_admissible_iff (f : StrongHom A B)
    (S : Set A.space) (T : Set B.space) (hST : f.baseMap '' S ⊆ T)
    (c : A.atlas.SubspaceChart S) (d : B.atlas.SubspaceChart T) :
    f.domainBaseMap S T hST '' Set.range (A.atlas.subspaceChart S c) ⊆
        Set.range (B.atlas.subspaceChart T d) ↔
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart d.val) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, Subtype.ext hy⟩

/-- All bounded coefficient tests survive domain restriction, with each
 common target subchart lifted to its original index. -/
theorem HasCoherentPullbacks.restrictDomains {f : StrongHom A B}
    (hf : f.HasCoherentPullbacks)
    (S : Set A.space) (T : Set B.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : B.atlas.IsOriginalChartDomain T)
    (hST : f.baseMap '' S ⊆ T) (htarget : f.HasDomainTargets S T) :
    (f.restrictDomains ⟨S, hS⟩ ⟨T, hT⟩ htarget).HasCoherentPullbacks := by
  intro c d e hd he R η m hmd hme α hα
  exact hf c.val d.val e.val
    ((f.domainBaseMap_admissible_iff S T hST c d).mp hd)
    ((f.domainBaseMap_admissible_iff S T hST c e).mp he)
    R η m.val (B.atlas.chart_subset_of_subspaceSubset T m d hmd)
      (B.atlas.chart_subset_of_subspaceSubset T m e hme) α hα

end StrongHom

namespace CompatibleStrongHom

/-- Restrict a compatible map while retaining its full original bounded family. -/
def restrictDomains (f : CompatibleStrongHom A B)
    (S : Set A.space) (T : Set B.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : B.atlas.IsOriginalChartDomain T)
    (hST : f.baseMap '' S ⊆ T) (htarget : f.toStrongHom.HasDomainTargets S T) :
    CompatibleStrongHom (A.subspacePresentation S hS) (B.subspacePresentation T hT) where
  toStrongHom := f.toStrongHom.restrictDomains ⟨S, hS⟩ ⟨T, hT⟩ htarget
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    (f.coherent.restrictDomains S T hS hT hST htarget)

/-- Source-only restriction also retains every original compatible pullback. -/
def restrictSubspace (f : CompatibleStrongHom A B)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    CompatibleStrongHom (A.subspacePresentation S hS) B where
  toStrongHom := f.toStrongHom.restrictSubspace S hS
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr
    (fun c j k hj hk => f.coherent c.val j k
      ((f.toStrongHom.restrictSubspace_admissible_iff S hS c j).mp hj)
      ((f.toStrongHom.restrictSubspace_admissible_iff S hS c k).mp hk))

end CompatibleStrongHom

variable (A)

/-- The compatible inclusion uses all original bounded restrictions. -/
def subspaceCompatibleInclusion (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    CompatibleStrongHom (A.subspacePresentation S hS) A :=
  (CompatibleStrongHom.id A).restrictSubspace S hS

/-- Full compatible inclusion between nested actual domains. -/
def subspaceCompatibleMap (S T : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hST : S ⊆ T) :
    CompatibleStrongHom (A.subspacePresentation S hS) (A.subspacePresentation T hT) :=
  (CompatibleStrongHom.id A).restrictDomains S T hS hT
    (by simpa only [CompatibleStrongHom.id, StrongHom.id, ContinuousMap.coe_id,
      Set.image_id] using hST)
    (fun c => ⟨⟨c.val, c.property.trans hST⟩, by
      simp only [CompatibleStrongHom.id, StrongHom.id, ContinuousMap.coe_id,
        Set.image_id, Subset.rfl]⟩)

@[simp]
theorem subspaceCompatibleMap_id (S : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hSS : S ⊆ S) :
    A.subspaceCompatibleMap S S hS hS hSS =
      CompatibleStrongHom.id (A.subspacePresentation S hS) :=
  CompatibleStrongHom.ext (StrongHom.ext rfl
    (heq_of_eq (funext fun _ => funext fun _ => funext fun _ => rfl)))

/-- Composition recovers every original bounded map, rather than only
 the common ambient inclusion. -/
theorem subspaceCompatibleMap_comp (S T U : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hU : A.atlas.IsOriginalChartDomain U) (hST : S ⊆ T) (hTU : T ⊆ U)
    (hSU : S ⊆ U) :
    (A.subspaceCompatibleMap S T hS hT hST).comp
        (A.subspaceCompatibleMap T U hT hU hTU) =
      A.subspaceCompatibleMap S U hS hU hSU := by
  refine CompatibleStrongHom.ext_of_pullback rfl ?_
  intro c
  let d : A.atlas.SubspaceChart T := ⟨c.val, c.property.trans hST⟩
  let e : A.atlas.SubspaceChart U := ⟨c.val, c.property.trans hSU⟩
  have hcd : (A.subspaceCompatibleMap S T hS hT hST).baseMap ''
      Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
        Set.range ((A.subspacePresentation T hT).atlas.chart d) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hde : (A.subspaceCompatibleMap T U hT hU hTU).baseMap ''
      Set.range ((A.subspacePresentation T hT).atlas.chart d) ⊆
        Set.range ((A.subspacePresentation U hU).atlas.chart e) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hce := (A.subspaceCompatibleMap S T hS hT hST).toStrongHom.comp_admissible
    (A.subspaceCompatibleMap T U hT hU hTU).toStrongHom c d e hcd hde
  refine ⟨e, hce, ?_⟩
  rw [CompatibleStrongHom.comp_pullback
    (A.subspaceCompatibleMap S T hS hT hST)
    (A.subspaceCompatibleMap T U hT hU hTU) c d e hcd hde hce]
  change (A.atlas.restriction c.val c.val _).comp (A.atlas.restriction c.val c.val _) =
    A.atlas.restriction c.val c.val _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

@[simp]
theorem subspaceCompatibleMap_inclusion (S T : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hST : S ⊆ T) :
    (A.subspaceCompatibleMap S T hS hT hST).comp (A.subspaceCompatibleInclusion T hT) =
      A.subspaceCompatibleInclusion S hS := by
  refine CompatibleStrongHom.ext_of_pullback rfl ?_
  intro c
  let d : A.atlas.SubspaceChart T := ⟨c.val, c.property.trans hST⟩
  have hcd : (A.subspaceCompatibleMap S T hS hT hST).baseMap ''
      Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
        Set.range ((A.subspacePresentation T hT).atlas.chart d) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hd : (A.subspaceCompatibleInclusion T hT).baseMap ''
      Set.range ((A.subspacePresentation T hT).atlas.chart d) ⊆
        Set.range (A.atlas.chart c.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hc := (A.subspaceCompatibleMap S T hS hT hST).toStrongHom.comp_admissible
    (A.subspaceCompatibleInclusion T hT).toStrongHom c d c.val hcd hd
  refine ⟨c.val, hc, ?_⟩
  rw [CompatibleStrongHom.comp_pullback
    (A.subspaceCompatibleMap S T hS hT hST)
    (A.subspaceCompatibleInclusion T hT) c d c.val hcd hd hc]
  change (A.atlas.restriction c.val c.val _).comp (A.atlas.restriction c.val c.val _) =
    A.atlas.restriction c.val c.val _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- Each actual domain presentation is an object of the full compatible category. -/
def originalCompatibleDomainFunctor : A.atlas.OriginalChartDomain ⥤
    CompatibleAtlasPresentation.{u, v, w} K where
  obj S := ⟨A.originalDomainPresentation S⟩
  map {S T} h := A.subspaceCompatibleMap S.carrier T.carrier
    S.is_domain T.is_domain (leOfHom h)
  map_id S := A.subspaceCompatibleMap_id S.carrier S.is_domain _
  map_comp {S T U} f g := (A.subspaceCompatibleMap_comp S.carrier T.carrier U.carrier
    S.is_domain T.is_domain U.is_domain (leOfHom f) (leOfHom g) _).symm

/-- The actual full compatible domain inclusions form a cocone. -/
def originalCompatibleDomainCocone : CategoryTheory.Limits.Cocone
    A.originalCompatibleDomainFunctor where
  pt := ⟨A⟩
  ι :=
    { app S := A.subspaceCompatibleInclusion S.carrier S.is_domain
      naturality := fun S T h => by
        change (A.subspaceCompatibleMap S.carrier T.carrier S.is_domain T.is_domain
          (leOfHom h)).comp (A.subspaceCompatibleInclusion T.carrier T.is_domain) =
            (A.subspaceCompatibleInclusion S.carrier S.is_domain).comp
              (CompatibleStrongHom.id A)
        rw [CompatibleStrongHom.comp_id]
        exact A.subspaceCompatibleMap_inclusion _ _ _ _ _ }

variable {A}

namespace CompatibleStrongHom

/-- Every rectangle of nested source and target domains commutes as a full
 compatible morphism, with no extra equality assumption on bounded maps. -/
theorem restrictDomains_naturality (f : CompatibleStrongHom A B)
    (S S' : Set A.space) (T T' : Set B.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hS' : A.atlas.IsOriginalChartDomain S')
    (hT : B.atlas.IsOriginalChartDomain T) (hT' : B.atlas.IsOriginalChartDomain T')
    (hSS' : S ⊆ S') (hTT' : T ⊆ T')
    (hST : f.baseMap '' S ⊆ T) (hS'T' : f.baseMap '' S' ⊆ T')
    (htarget : f.toStrongHom.HasDomainTargets S T)
    (htarget' : f.toStrongHom.HasDomainTargets S' T') :
    (A.subspaceCompatibleMap S S' hS hS' hSS').comp
        (f.restrictDomains S' T' hS' hT' hS'T' htarget') =
      (f.restrictDomains S T hS hT hST htarget).comp
        (B.subspaceCompatibleMap T T' hT hT' hTT') := by
  refine ext_of_pullback rfl ?_
  intro c
  obtain ⟨d, hd⟩ := htarget c
  let c' : A.atlas.SubspaceChart S' := ⟨c.val, c.property.trans hSS'⟩
  let d' : B.atlas.SubspaceChart T' := ⟨d.val, d.property.trans hTT'⟩
  have hcc' : (A.subspaceCompatibleMap S S' hS hS' hSS').baseMap ''
      Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
        Set.range ((A.subspacePresentation S' hS').atlas.chart c') := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hfd' : (f.restrictDomains S' T' hS' hT' hS'T' htarget').baseMap ''
      Set.range ((A.subspacePresentation S' hS').atlas.chart c') ⊆
        Set.range ((B.subspacePresentation T' hT').atlas.chart d') :=
    (f.toStrongHom.domainBaseMap_admissible_iff S' T' hS'T' c' d').mpr hd
  have hfd : (f.restrictDomains S T hS hT hST htarget).baseMap ''
      Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
        Set.range ((B.subspacePresentation T hT).atlas.chart d) :=
    (f.toStrongHom.domainBaseMap_admissible_iff S T hST c d).mpr hd
  have hdd' : (B.subspaceCompatibleMap T T' hT hT' hTT').baseMap ''
      Set.range ((B.subspacePresentation T hT).atlas.chart d) ⊆
        Set.range ((B.subspacePresentation T' hT').atlas.chart d') := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hfinal := (A.subspaceCompatibleMap S S' hS hS' hSS').toStrongHom.comp_admissible
    (f.restrictDomains S' T' hS' hT' hS'T' htarget').toStrongHom c c' d' hcc' hfd'
  refine ⟨d', hfinal, ?_⟩
  rw [comp_pullback
      (A.subspaceCompatibleMap S S' hS hS' hSS')
      (f.restrictDomains S' T' hS' hT' hS'T' htarget') c c' d' hcc' hfd' hfinal,
    comp_pullback
      (f.restrictDomains S T hS hT hST htarget)
      (B.subspaceCompatibleMap T T' hT hT' hTT') c d d' hfd hdd']
  change (A.atlas.restriction c.val c.val _).comp (f.pullback c.val d.val _) =
    (f.pullback c.val d.val _).comp (B.atlas.restriction d.val d.val _)
  rw [A.atlas.restriction_id, B.atlas.restriction_id,
    BoundedAlgHom.id_comp, BoundedAlgHom.comp_id]

end CompatibleStrongHom
end Langlands.Analytic.AffinoidAtlasPresentation
