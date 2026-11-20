import Langlands.Geometry.Analytic.AnalyticOpenImmersionBaseChange
import Langlands.Geometry.Analytic.DomainEtaleFactorizations
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.LocalActionLifts
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Restriction to distinguished opens -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Filter Set Topology
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

private theorem IsOriginalChartDomain.exists_refinement_at_isClosed {S : Set X}
    (hS : a.IsOriginalChartDomain S) (hclosed : IsClosed S) (x : X) :
    ∃ σ : Set (Set X), σ.Finite ∧ σ ⊆ Set.range (fun i => Set.range (a.chart i)) ∧
      (∀ V ∈ σ, V ⊆ S ∧ x ∈ V) ∧ ⋃₀ σ ∈ 𝓝[S] x := by
  by_cases hx : x ∈ S
  · exact (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hS S (mem_singleton S) x hx
  · have hb : 𝓝[S] x = ⊥ := notMem_closure_iff_nhdsWithin_eq_bot.mp (by
      rwa [hclosed.closure_eq])
    exact ⟨∅, finite_empty, empty_subset _, by simp, by simp [hb]⟩

/-- A union of two closed analytic domains is an analytic domain. -/
theorem IsOriginalChartDomain.union_of_isClosed {S T : Set X}
    (hS : a.IsOriginalChartDomain S) (hT : a.IsOriginalChartDomain T)
    (hSc : IsClosed S) (hTc : IsClosed T) : a.IsOriginalChartDomain (S ∪ T) := by
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  rintro _ ⟨rfl⟩ x _
  obtain ⟨σ, hσ, hs, hm, hn⟩ := hS.exists_refinement_at_isClosed hSc x
  obtain ⟨τ, hτ, ht, hm', hn'⟩ := hT.exists_refinement_at_isClosed hTc x
  refine ⟨σ ∪ τ, hσ.union hτ, union_subset hs ht, ?_, ?_⟩
  · rintro V (hV | hV)
    · exact ⟨(hm V hV).1.trans subset_union_left, (hm V hV).2⟩
    · exact ⟨(hm' V hV).1.trans subset_union_right, (hm' V hV).2⟩
  · rw [sUnion_union, nhdsWithin_union]
    exact Filter.union_mem_sup hn hn'

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A distinguished open is an open subset whose complement is an analytic domain. -/
def IsDistinguishedOpen (X : LocalizedCategory.{u, v, w} (K := K))
    (U : Set (localizedSpaceFunctor.obj X)) : Prop :=
  IsOpen U ∧ (presentationOf X).presentation.atlas.IsOriginalChartDomain Uᶜ

theorem IsDistinguishedOpen.inter {X : LocalizedCategory.{u, v, w} (K := K)}
    {U V : Set (localizedSpaceFunctor.obj X)} (hU : IsDistinguishedOpen X U)
    (hV : IsDistinguishedOpen X V) : IsDistinguishedOpen X (U ∩ V) := by
  refine ⟨hU.1.inter hV.1, ?_⟩
  have h : (U ∩ V)ᶜ = Uᶜ ∪ Vᶜ := compl_inter U V
  exact (congrArg (fun W : Set (localizedSpaceFunctor.obj X) =>
    (presentationOf X).presentation.atlas.IsOriginalChartDomain W) h).mpr
    (hU.2.union_of_isClosed hV.2 hU.1.isClosed_compl hV.1.isClosed_compl)

/-- Restricting a distinguished étale morphism to the inverse image of a
distinguished open of the base gives a distinguished étale morphism over the base. -/
theorem IsDistinguishedEtale.restrictToDistinguishedOpen
    {Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Y ⟶ X}
    (hf : IsDistinguishedEtale f) {U : Set (localizedSpaceFunctor.obj X)}
    (hU : IsDistinguishedOpen X U) :
    IsDistinguishedEtale (domainι Y (preimageOpenDomain f U hU.1) ≫ f) := by
  obtain ⟨het, Q, φ, hφ, hQ, O, C, hO, hC, e, he⟩ := hf
  let D := preimageOpenDomain f U hU.1
  let E := domainPreimage e.inv D
  let P := O.subspaceExtend E
  let E₀ := domainPreimage φ (⟨Uᶜ, hU.2⟩ : (presentationOf X).AnalyticDomain)
  have hCc : IsClosed C.carrier := hC ▸ hO.isClosed_compl
  have hEc : IsClosed E₀.carrier := hU.1.isClosed_compl.preimage
    (localizedSpaceFunctor.map φ).hom.continuous
  let C' : (presentationOf Q).AnalyticDomain :=
    ⟨C.carrier ∪ E₀.carrier, C.is_domain.union_of_isClosed E₀.is_domain hCc hEc⟩
  have hcomp : e.inv ≫ f = domainι Q O ≫ φ := by
    rw [he, Iso.inv_hom_id_assoc]
    rfl
  have hmem (x : localizedSpaceFunctor.obj (domainObj Q O)) :
      x ∈ E.carrier ↔ localizedSpaceFunctor.map φ x.val ∈ U := by
    have h := congrArg (fun a : domainObj Q O ⟶ X => localizedSpaceFunctor.map a x) hcomp
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
    change localizedSpaceFunctor.map f (localizedSpaceFunctor.map e.inv x) ∈ U ↔ _
    rw [h]
  have hP : P.carrier = O.carrier ∩ (localizedSpaceFunctor.map φ ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, (hmem y).mp hy⟩
    · rintro ⟨hx, hxU⟩
      exact ⟨⟨x, hx⟩, (hmem ⟨x, hx⟩).mpr hxU, rfl⟩
  have hPo : IsOpen P.carrier := by
    rw [hP]
    exact hO.inter (hU.1.preimage (localizedSpaceFunctor.map φ).hom.continuous)
  have hC' : C'.carrier = P.carrierᶜ := by
    change C.carrier ∪ (localizedSpaceFunctor.map φ ⁻¹' Uᶜ) = P.carrierᶜ
    rw [hC, hP, compl_inter]
    rfl
  let j : domainObj Y D ≅ domainObj (domainObj Q O) E := domainImageIso e D
  let k : domainObj (domainObj Q O) E ≅ domainObj Q P :=
    domainNestedLocalizationIso (presentationOf Q) O E
  let i := j ≪≫ k
  refine ⟨etale_comp (etaleOpenDomainStatement Y _ _) het,
    Q, φ, hφ, hQ, P, C', hPo, hC', i, ?_⟩
  have hk : k.hom ≫ domainι Q P = domainι (domainObj Q O) E ≫ domainι Q O :=
    domainNestedLocalizationIso_hom_inclusion (presentationOf Q) O E
  have hi : i.hom ≫ domainι Q P = domainι Y D ≫ e.hom ≫ domainι Q O := calc
    _ = j.hom ≫ k.hom ≫ domainι Q P := Category.assoc _ _ _
    _ = j.hom ≫ domainι (domainObj Q O) E ≫ domainι Q O := congrArg (j.hom ≫ ·) hk
    _ = _ := domainImageIso_hom_inclusion_assoc e D _
  refine (congrArg (domainι Y D ≫ ·) he).trans ?_
  change domainι Y D ≫ e.hom ≫ domainι Q O ≫ φ = i.hom ≫ domainι Q P ≫ φ
  simpa only [Category.assoc] using congrArg (· ≫ φ) hi.symm

end SaturatedAtlasPresentation
end Langlands.Analytic
