import Langlands.Geometry.Analytic.OriginalDomainNested
import Langlands.Geometry.Analytic.OriginalDomainStrongPresheaf

/-! # Full strong maps under localization of original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- The inverse actual nested-domain comparison preserves admissibility at
the corresponding original source chart. -/
theorem toNestedOriginalDomain_admissible_iff
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B)
    (c : ((A.originalDomainPresentation S).originalDomainPresentation U).atlas.Index)
    (j : B.atlas.Index) :
    (f.baseMap.comp (A.originalDomainNestedInverse S U).baseMap) ''
        Set.range (((A.originalDomainPresentation S).originalDomainPresentation U).atlas.chart c)
          ⊆ Set.range (B.atlas.chart j) ↔
      f.baseMap '' Set.range ((A.originalDomainPresentation (S.subspaceExtend U)).atlas.chart
        ((S.subspaceExtendChartEquiv U).symm c)) ⊆ Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Move a full strong map from the ambient-image presentation to the actual
nested presentation, retaining every bounded pullback. -/
def toNestedOriginalDomain
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B) :
    StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B where
  baseMap := f.baseMap.comp (A.originalDomainNestedInverse S U).baseMap
  target_exists c := by
    obtain ⟨j, hj⟩ := f.target_exists ((S.subspaceExtendChartEquiv U).symm c)
    exact ⟨j, (toNestedOriginalDomain_admissible_iff S U f c j).mpr hj⟩
  pullback c j h := f.pullback ((S.subspaceExtendChartEquiv U).symm c) j
    ((toNestedOriginalDomain_admissible_iff S U f c j).mp h)
  chart_comm c j h x := f.chart_comm ((S.subspaceExtendChartEquiv U).symm c) j _ x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm ((S.subspaceExtendChartEquiv U).symm c)
      ((S.subspaceExtendChartEquiv U).symm c') j j'
      ((A.originalDomainNestedInverse S U).index_mono c c' hc) hj
      ((toNestedOriginalDomain_admissible_iff S U f c j).mp h)
      ((toNestedOriginalDomain_admissible_iff S U f c' j').mp h')

/-- The forward actual nested-domain comparison preserves admissibility at
the corresponding original source chart. -/
theorem fromNestedOriginalDomain_admissible_iff
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B)
    (c : (A.originalDomainPresentation (S.subspaceExtend U)).atlas.Index)
    (j : B.atlas.Index) :
    (f.baseMap.comp (A.originalDomainNestedMap S U).baseMap) ''
        Set.range ((A.originalDomainPresentation (S.subspaceExtend U)).atlas.chart c)
          ⊆ Set.range (B.atlas.chart j) ↔
      f.baseMap ''
        Set.range (((A.originalDomainPresentation S).originalDomainPresentation U).atlas.chart
          ((S.subspaceExtendChartEquiv U) c)) ⊆ Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Forget intermediate membership in a full strong source map, retaining
all original bounded pullbacks on the ambient-image presentation. -/
def fromNestedOriginalDomain
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B) :
    StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B where
  baseMap := f.baseMap.comp (A.originalDomainNestedMap S U).baseMap
  target_exists c := by
    obtain ⟨j, hj⟩ := f.target_exists ((S.subspaceExtendChartEquiv U) c)
    exact ⟨j, (fromNestedOriginalDomain_admissible_iff S U f c j).mpr hj⟩
  pullback c j h := f.pullback ((S.subspaceExtendChartEquiv U) c) j
    ((fromNestedOriginalDomain_admissible_iff S U f c j).mp h)
  chart_comm c j h x := f.chart_comm ((S.subspaceExtendChartEquiv U) c) j _ x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm ((S.subspaceExtendChartEquiv U) c)
      ((S.subspaceExtendChartEquiv U) c') j j'
      ((A.originalDomainNestedMap S U).index_mono c c' hc) hj
      ((fromNestedOriginalDomain_admissible_iff S U f c j).mp h)
      ((fromNestedOriginalDomain_admissible_iff S U f c' j').mp h')

@[simp]
theorem toNestedOriginalDomain_apply
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B) (x : U) :
    (toNestedOriginalDomain S U f).baseMap x =
      f.baseMap ((S.subspaceExtendHomeomorph U).symm x) := rfl

@[simp]
theorem fromNestedOriginalDomain_apply
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B)
    (x : S.subspaceExtend U) :
    (fromNestedOriginalDomain S U f).baseMap x =
      f.baseMap ((S.subspaceExtendHomeomorph U) x) := rfl

/-- Exact equality of the entire transported bounded map. -/
theorem toNestedOriginalDomain_pullback
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B)
    (c : ((A.originalDomainPresentation S).originalDomainPresentation U).atlas.Index)
    (j : B.atlas.Index)
    (h : (toNestedOriginalDomain S U f).baseMap ''
      Set.range (((A.originalDomainPresentation S).originalDomainPresentation U).atlas.chart c)
        ⊆ Set.range (B.atlas.chart j)) :
    (toNestedOriginalDomain S U f).pullback c j h =
      f.pullback ((S.subspaceExtendChartEquiv U).symm c) j
        ((toNestedOriginalDomain_admissible_iff S U f c j).mp h) := rfl

/-- Exact equality of the entire bounded map after forgetting nesting. -/
theorem fromNestedOriginalDomain_pullback
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B)
    (c : (A.originalDomainPresentation (S.subspaceExtend U)).atlas.Index)
    (j : B.atlas.Index)
    (h : (fromNestedOriginalDomain S U f).baseMap ''
      Set.range ((A.originalDomainPresentation (S.subspaceExtend U)).atlas.chart c)
        ⊆ Set.range (B.atlas.chart j)) :
    (fromNestedOriginalDomain S U f).pullback c j h =
      f.pullback ((S.subspaceExtendChartEquiv U) c) j
        ((fromNestedOriginalDomain_admissible_iff S U f c j).mp h) := rfl

@[simp]
theorem fromNestedOriginalDomain_toNestedOriginalDomain
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B) :
    fromNestedOriginalDomain S U (toNestedOriginalDomain S U f) = f := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

@[simp]
theorem toNestedOriginalDomain_fromNestedOriginalDomain
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B) :
    toNestedOriginalDomain S U (fromNestedOriginalDomain S U f) = f := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Moving to the nested presentation commutes with every domain restriction
as an equality of full strong maps. -/
theorem toNestedOriginalDomain_restrict
    (S : A.atlas.OriginalChartDomain)
    {U V : (A.originalDomainPresentation S).atlas.OriginalChartDomain} (hUV : U ≤ V)
    (f : StrongHom (A.originalDomainPresentation (S.subspaceExtend V)) B) :
    toNestedOriginalDomain S U (f.restrictOriginalDomain (S.subspaceExtend_mono hUV)) =
      (toNestedOriginalDomain S V f).restrictOriginalDomain hUV := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Forgetting nesting also commutes with every full domain restriction. -/
theorem fromNestedOriginalDomain_restrict
    (S : A.atlas.OriginalChartDomain)
    {U V : (A.originalDomainPresentation S).atlas.OriginalChartDomain} (hUV : U ≤ V)
    (f : StrongHom ((A.originalDomainPresentation S).originalDomainPresentation V) B) :
    fromNestedOriginalDomain S U (f.restrictOriginalDomain hUV) =
      (fromNestedOriginalDomain S V f).restrictOriginalDomain
        (S.subspaceExtend_mono hUV) := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Restriction to the ambient image, followed by presentation transport,
equals the actual two-step subspace restriction, including all bounded maps. -/
theorem toNestedOriginalDomain_restrictSubspace
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom A B) :
    toNestedOriginalDomain S U
        (f.restrictSubspace (S.subspaceExtend U).carrier (S.subspaceExtend U).is_domain) =
      (f.restrictSubspace S.carrier S.is_domain).restrictSubspace U.carrier U.is_domain := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

end StrongHom

/-- Full strong maps on the two actual presentations of a nested domain
correspond, with every original bounded map preserved. -/
def originalDomainStrongEquiv (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    StrongHom (A.originalDomainPresentation (S.subspaceExtend U)) B ≃
      StrongHom ((A.originalDomainPresentation S).originalDomainPresentation U) B where
  toFun := StrongHom.toNestedOriginalDomain S U
  invFun := StrongHom.fromNestedOriginalDomain S U
  left_inv := StrongHom.fromNestedOriginalDomain_toNestedOriginalDomain S U
  right_inv := StrongHom.toNestedOriginalDomain_fromNestedOriginalDomain S U

/-- The strong-map presheaf on the actual subspace domain category is naturally
isomorphic to the ambient strong-map presheaf pulled back by ambient image. -/
def originalDomainStrongLocalization (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (S : A.atlas.OriginalChartDomain) :
    S.subspaceExtensionFunctor.op ⋙ A.originalDomainStrongPresheaf B ≅
      (A.originalDomainPresentation S).originalDomainStrongPresheaf B :=
  NatIso.ofComponents (fun U => (A.originalDomainStrongEquiv B S U.unop).toIso)
    (fun h => by
      apply ConcreteCategory.hom_ext
      intro f
      exact StrongHom.toNestedOriginalDomain_restrict S (leOfHom h.unop) f)

end Langlands.Analytic.AffinoidAtlasPresentation
