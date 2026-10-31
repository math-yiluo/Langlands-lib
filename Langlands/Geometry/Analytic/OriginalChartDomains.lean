import Langlands.Geometry.Analytic.AtlasSubspaceRestriction
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones

/-! # The order and actual presentations of original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Filter Topology CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

theorem isOriginalChartDomain_univ : a.IsOriginalChartDomain Set.univ := by
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  intro U hU x _
  have hUeq : U = Set.univ := mem_singleton_iff.mp hU
  subst U
  obtain ⟨σ, hf, hs, hm, hn⟩ := a.isNet_chartFamily.1 x
  refine ⟨σ, hf, hs, fun V hV => ⟨subset_univ _, hm V hV⟩, ?_⟩
  simpa only [nhdsWithin_univ] using hn

theorem IsOriginalChartDomain.inter {S T : Set X}
    (hS : a.IsOriginalChartDomain S) (hT : a.IsOriginalChartDomain T) :
    a.IsOriginalChartDomain (S ∩ T) :=
  a.isNet_chartFamily.isQuasinet_restrictedFamily_inter hS hT

/-- An actual subset locally covered by contained original charts. The bundle
contains the finite relative neighborhood condition, not an output atlas. -/
structure OriginalChartDomain where
  carrier : Set X
  is_domain : a.IsOriginalChartDomain carrier

namespace OriginalChartDomain

variable {a}

instance : SetLike (OriginalChartDomain a) X where
  coe := carrier
  coe_injective := by
    rintro ⟨S, hS⟩ ⟨T, hT⟩ h
    cases h
    rfl

@[ext]
theorem ext {S T : OriginalChartDomain a} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

instance : SemilatticeInf (OriginalChartDomain a) where
  __ := PartialOrder.ofSetLike (OriginalChartDomain a) X
  inf S T := ⟨S.carrier ∩ T.carrier, S.is_domain.inter a T.is_domain⟩
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf _ _ _ hS hT _ hx := ⟨hS hx, hT hx⟩

instance : BoundedOrder (OriginalChartDomain a) where
  top := ⟨Set.univ, a.isOriginalChartDomain_univ⟩
  le_top _ _ _ := trivial
  bot := ⟨∅, a.isOriginalChartDomain_empty⟩
  bot_le _ _ h := False.elim h

@[simp]
theorem coe_inf (S T : OriginalChartDomain a) :
    ((S ⊓ T : OriginalChartDomain a) : Set X) = (S : Set X) ∩ T := rfl

@[simp]
theorem mem_inf (S T : OriginalChartDomain a) (x : X) :
    x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

@[simp]
theorem coe_top : ((⊤ : OriginalChartDomain a) : Set X) = Set.univ := rfl

@[simp]
theorem coe_bot : ((⊥ : OriginalChartDomain a) : Set X) = ∅ := rfl

/-- Every original spectrum range supplies a bundled domain. -/
def ofChart (i : a.Index) : OriginalChartDomain a :=
  ⟨Set.range (a.chart i), a.isOriginalChartDomain_chart i⟩

@[simp]
theorem coe_ofChart (i : a.Index) :
    (ofChart i : Set X) = Set.range (a.chart i) := rfl

end OriginalChartDomain

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Realize a bundled original-chart domain by its constructed subspace atlas. -/
def originalDomainPresentation (S : A.atlas.OriginalChartDomain) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  A.subspacePresentation S.carrier S.is_domain

/-- Inclusion retains original chart indices and bounded identities. -/
def originalDomainMap {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    A.originalDomainPresentation S ⟶ A.originalDomainPresentation T :=
  A.subspaceMap S.carrier T.carrier S.is_domain T.is_domain h

@[simp]
theorem originalDomainMap_id (S : A.atlas.OriginalChartDomain) :
    A.originalDomainMap (le_refl S) = 𝟙 (A.originalDomainPresentation S) :=
  A.subspaceMap_id S.carrier S.is_domain _

theorem originalDomainMap_comp {S T U : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) (hTU : T ≤ U) :
    A.originalDomainMap hST ≫ A.originalDomainMap hTU =
      A.originalDomainMap (hST.trans hTU) :=
  A.subspaceMap_comp _ _ _ _ _ _ _ _ _

/-- The domain order is realized by actual chosen bounded atlas maps. -/
def originalDomainFunctor : A.atlas.OriginalChartDomain ⥤
    AffinoidAtlasPresentation.{u, v, w} K where
  obj := A.originalDomainPresentation
  map h := A.originalDomainMap (leOfHom h)
  map_id S := A.originalDomainMap_id S
  map_comp f g := (A.originalDomainMap_comp (leOfHom f) (leOfHom g)).symm

/-- Each domain has its actual chosen inclusion into the original atlas. -/
def originalDomainInclusion (S : A.atlas.OriginalChartDomain) :
    A.originalDomainPresentation S ⟶ A :=
  A.subspaceInclusion S.carrier S.is_domain

@[simp]
theorem originalDomainMap_inclusion {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) :
    A.originalDomainMap h ≫ A.originalDomainInclusion T =
      A.originalDomainInclusion S :=
  A.subspaceMap_subspaceInclusion _ _ _ _ h

/-- The inclusions form a cocone of complete chosen atlas arrows. -/
def originalDomainCocone : Cocone A.originalDomainFunctor where
  pt := A
  ι :=
    { app := A.originalDomainInclusion
      naturality := fun S T h => by
        change A.originalDomainMap (leOfHom h) ≫ A.originalDomainInclusion T =
          A.originalDomainInclusion S ≫ 𝟙 A
        rw [Category.comp_id]
        exact A.originalDomainMap_inclusion (leOfHom h) }

@[simp]
theorem originalDomainMap_apply {S T : A.atlas.OriginalChartDomain} (h : S ≤ T) (x : S) :
    (A.originalDomainMap h).baseMap x = Set.inclusion h x := rfl

@[simp]
theorem originalDomainMap_pullback {S T : A.atlas.OriginalChartDomain} (h : S ≤ T)
    (c : (A.originalDomainPresentation S).atlas.Index) :
    (A.originalDomainMap h).pullback c =
      BoundedAlgHom.id K (A.atlas.algebra c.val) := rfl

/-- Realizing an original chart recovers its previously constructed presentation. -/
theorem originalDomainPresentation_ofChart (i : A.atlas.Index) :
    A.originalDomainPresentation (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i) =
      A.chartPresentation i := rfl

/-- The whole-space presentation has an actual bounded inverse to its inclusion. -/
def originalDomainTopInverse :
    A ⟶ A.originalDomainPresentation ⊤ where
  baseMap := ⟨fun x => ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
  indexMap i := ⟨i, subset_univ _⟩
  index_mono _ _ h := A.atlas.subspaceChart_subset Set.univ _ _ h
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- The top domain realizes the original presentation, including all bounded data. -/
def originalDomainTopIso : A.originalDomainPresentation ⊤ ≅ A where
  hom := A.originalDomainInclusion ⊤
  inv := A.originalDomainTopInverse
  hom_inv_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))
  inv_hom_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Both actual intersection inclusions agree after inclusion into the ambient atlas. -/
theorem originalDomain_intersection_diamond (S T : A.atlas.OriginalChartDomain) :
    A.originalDomainMap (inf_le_left : S ⊓ T ≤ S) ≫ A.originalDomainInclusion S =
      A.originalDomainMap (inf_le_right : S ⊓ T ≤ T) ≫ A.originalDomainInclusion T :=
  (A.originalDomainMap_inclusion inf_le_left).trans
    (A.originalDomainMap_inclusion inf_le_right).symm

end AffinoidAtlasPresentation

end Langlands.Analytic
