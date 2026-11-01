import Langlands.Geometry.Analytic.OriginalDomainLocalization

/-! # The actual presentation of a domain inside an original-chart domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set CategoryTheory

namespace IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

@[simp]
theorem mem_subspaceExtend_iff (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) (x : S.carrier) :
    x.val ∈ S.subspaceExtend U ↔ x ∈ U := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have h : y = x := Subtype.ext heq
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The ambient image of a subspace domain has the same actual topology as
the nested domain. The maps insert and forget the intermediate membership. -/
def subspaceExtendHomeomorph (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    (S.subspaceExtend U).carrier ≃ₜ U.carrier where
  toFun x := ⟨⟨x.val, S.subspaceExtend_le U x.property⟩,
    (S.mem_subspaceExtend_iff U ⟨x.val, S.subspaceExtend_le U x.property⟩).mp x.property⟩
  invFun y := ⟨y.val.val, ⟨y.val, y.property, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The original charts contained in the ambient image are exactly the
charts retained by restriction first to `S` and then to `U`. -/
def subspaceExtendChartEquiv (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    a.SubspaceChart (S.subspaceExtend U).carrier ≃
      (a.subspaceAtlas S.carrier S.is_domain).SubspaceChart U.carrier where
  toFun c :=
    ⟨⟨c.val, c.property.trans (S.subspaceExtend_le U)⟩, by
      rintro _ ⟨x, rfl⟩
      exact (S.mem_subspaceExtend_iff U
        (a.subspaceChart S.carrier
          ⟨c.val, c.property.trans (S.subspaceExtend_le U)⟩ x)).mp (c.property ⟨x, rfl⟩)⟩
  invFun c := ⟨c.val.val, by
    rintro _ ⟨x, rfl⟩
    exact ⟨a.subspaceChart S.carrier c.val x, c.property ⟨x, rfl⟩, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end IndexedAffinoidAtlas.OriginalChartDomain

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Regard the ambient presentation of a subspace domain as the nested
presentation, retaining its original charts and bounded identity pullbacks. -/
def originalDomainNestedMap (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    A.originalDomainPresentation (S.subspaceExtend U) ⟶
      (A.originalDomainPresentation S).originalDomainPresentation U where
  baseMap := ⟨S.subspaceExtendHomeomorph U, (S.subspaceExtendHomeomorph U).continuous⟩
  indexMap := S.subspaceExtendChartEquiv U
  index_mono c d h :=
    (A.atlas.subspaceAtlas S.carrier S.is_domain).subspaceChart_subset U.carrier _ _
      (A.atlas.subspaceChart_subset S.carrier _ _
        (A.atlas.chart_subset_of_subspaceSubset (S.subspaceExtend U).carrier c d h))
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Forget the intermediate subspace in the presentation of a nested domain.
All original chart algebras and bounded identity pullbacks are retained. -/
def originalDomainNestedInverse (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    (A.originalDomainPresentation S).originalDomainPresentation U ⟶
      A.originalDomainPresentation (S.subspaceExtend U) where
  baseMap := ⟨(S.subspaceExtendHomeomorph U).symm,
    (S.subspaceExtendHomeomorph U).symm.continuous⟩
  indexMap := (S.subspaceExtendChartEquiv U).symm
  index_mono c d h :=
    A.atlas.subspaceChart_subset (S.subspaceExtend U).carrier _ _
      (A.atlas.chart_subset_of_subspaceSubset S.carrier c.val d.val
        ((A.atlas.subspaceAtlas S.carrier S.is_domain).chart_subset_of_subspaceSubset
          U.carrier c d h))
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Realization commutes with taking a domain inside an original-chart domain.
The inverse laws are equalities of complete chosen bounded atlas arrows. -/
def originalDomainNestedIso (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    A.originalDomainPresentation (S.subspaceExtend U) ≅
      (A.originalDomainPresentation S).originalDomainPresentation U where
  hom := A.originalDomainNestedMap S U
  inv := A.originalDomainNestedInverse S U
  hom_inv_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))
  inv_hom_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The comparison commutes with the actual chosen inclusion into `S`. -/
@[simp]
theorem originalDomainNestedMap_inclusion (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    A.originalDomainNestedMap S U ≫
        (A.originalDomainPresentation S).originalDomainInclusion U =
      A.originalDomainMap (S.subspaceExtend_le U) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The comparison commutes with the actual chosen inclusion into `A`. -/
theorem originalDomainNestedMap_ambientInclusion (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain) :
    A.originalDomainNestedMap S U ≫
        (A.originalDomainPresentation S).originalDomainInclusion U ≫
        A.originalDomainInclusion S =
      A.originalDomainInclusion (S.subspaceExtend U) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The chosen comparison is natural for all inclusions of subspace domains. -/
theorem originalDomainNestedMap_naturality (S : A.atlas.OriginalChartDomain)
    {U V : (A.originalDomainPresentation S).atlas.OriginalChartDomain}
    (h : U ≤ V) :
    A.originalDomainMap (S.subspaceExtend_mono h) ≫ A.originalDomainNestedMap S V =
      A.originalDomainNestedMap S U ≫ (A.originalDomainPresentation S).originalDomainMap h :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The ambient-image realization and nested realization are naturally
isomorphic as functors to complete chosen bounded atlas presentations. -/
def originalDomainNestedNatIso (S : A.atlas.OriginalChartDomain) :
    S.subspaceExtensionFunctor ⋙ A.originalDomainFunctor ≅
      (A.originalDomainPresentation S).originalDomainFunctor :=
  NatIso.ofComponents (A.originalDomainNestedIso S)
    (fun f => A.originalDomainNestedMap_naturality S (leOfHom f))

@[simp]
theorem originalDomainNestedMap_pullback (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (c : (A.originalDomainPresentation (S.subspaceExtend U)).atlas.Index) :
    (A.originalDomainNestedMap S U).pullback c =
      BoundedAlgHom.id K (A.atlas.algebra c.val) := rfl

@[simp]
theorem originalDomainNestedInverse_pullback (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (c : ((A.originalDomainPresentation S).originalDomainPresentation U).atlas.Index) :
    (A.originalDomainNestedInverse S U).pullback c =
      BoundedAlgHom.id K (A.atlas.algebra c.val.val) := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
