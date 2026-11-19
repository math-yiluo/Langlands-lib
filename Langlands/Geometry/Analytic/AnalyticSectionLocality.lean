import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.SaturatedDomainHomPresheaf

/-! # Open analytic sections from local equalities -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem eq_on_domain_of_cover {P : SaturatedAtlasPresentation.{u, v, w} K}
    {ι : Type v} (D : P.AnalyticDomain) (C : ι → P.AnalyticDomain)
    (hCD : ∀ i, C i ≤ D)
    (hc : AtlasTopology.LocallyRefines (range fun i => (C i).carrier) {D.carrier})
    {f g : localizationFunctor.obj (P.domain D) ⟶ localizationFunctor.obj P}
    (h : ∀ i, P.localizedDomainInclusion (C i) =
      domainOrderMap (U := localizationFunctor.obj P) (hCD i) ≫ f)
    (hg : g = P.localizedDomainInclusion D) : f = g := by
  subst g
  let F := SourceCategory.comparisonFunctor (K := K)
  let f₀ : SourceCategory.ofPresentation (P.originalDomain D) ⟶
      SourceCategory.ofPresentation P := F.preimage f
  have hf₀ : F.map f₀ = f := F.map_preimage f
  have he : f₀ = SourceCategory.domainInclusion P D := by
    apply SourceCategory.eq_of_relativeDomainCover D C hCD hc
    intro i
    apply F.map_injective
    have hi := congrArg F.map (SourceCategory.domainMap_inclusion (hCD i))
    rw [Functor.map_comp] at hi
    change F.map (SourceCategory.domainMap (hCD i)) ≫
      SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion P D) =
        SourceCategory.comparisonFunctor.map (SourceCategory.domainInclusion P (C i)) at hi
    rw [P.comparisonFunctor_map_domainInclusion, P.comparisonFunctor_map_domainInclusion] at hi
    have hm : F.map (SourceCategory.domainMap (hCD i)) =
        domainOrderMap (U := localizationFunctor.obj P) (hCD i) := by
      apply (cancel_mono (P.localizedDomainInclusion D)).1
      exact hi.trans (domainOrderMap_comp_inclusion (U := localizationFunctor.obj P) (hCD i)).symm
    have hinc : F.map (SourceCategory.domainInclusion P D) = P.localizedDomainInclusion D :=
      P.comparisonFunctor_map_domainInclusion D
    rw [Functor.map_comp, Functor.map_comp, hf₀, hm, hinc]
    exact (h i).symm.trans (domainOrderMap_comp_inclusion
      (U := localizationFunctor.obj P) (hCD i)).symm
  exact hf₀.symm.trans ((congrArg F.map he).trans (P.comparisonFunctor_map_domainInclusion D))

set_option linter.defProp false in
/-- Sourcewise local equality of the retraction followed by its section
gives an open analytic identification with the image of the section. -/
def openImmersion_of_section_locallyFixed
    {A B : LocalizedCategory.{u, v, w} (K := K)} {s : A ⟶ B} {p : B ⟶ A}
    (hsp : s ≫ p = 𝟙 A)
    (hloc : ∀ y : localizedSpaceFunctor.obj B, y ∈ range (localizedSpaceFunctor.map s) →
      ∃ (W : Set (localizedSpaceFunctor.obj B)) (hW : IsOpen W), y ∈ W ∧
        domainι B ((presentationOf B).openDomain W hW) ≫ (p ≫ s) =
          domainι B ((presentationOf B).openDomain W hW)) :
    openImmersion s := by
  classical
  obtain ⟨P, hP⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj P = B at hP
  subst B
  let Y : Set P.presentation.space := range (localizedSpaceFunctor.map s)
  have hlocal (y : Y) : ∃ (W : Set P.presentation.space) (hW : IsOpen W),
      y.val ∈ W ∧ W ⊆ Y ∧
        P.localizedDomainInclusion (P.openDomain W hW) ≫ (p ≫ s) =
          P.localizedDomainInclusion (P.openDomain W hW) := by
    obtain ⟨W, hW, hy, he⟩ := hloc y.val y.property
    let D := P.openDomain W hW
    let j := P.localizedDomainInclusion D
    change j ≫ (p ≫ s) = j at he
    refine ⟨W, hW, hy, ?_, he⟩
    intro z hz
    let zD : localizedSpaceFunctor.obj (localizationFunctor.obj (P.domain D)) := ⟨z, hz⟩
    have h := congrArg (fun k : _ ⟶ localizationFunctor.obj P =>
      localizedSpaceFunctor.map k zD) he
    rw [Functor.map_comp, Functor.map_comp] at h
    change localizedSpaceFunctor.map s
      (localizedSpaceFunctor.map p (localizedSpaceFunctor.map j zD)) =
        localizedSpaceFunctor.map j zD at h
    have hzD : localizedSpaceFunctor.map j zD = z :=
      P.localizedSpaceFunctor_map_localizedDomainInclusion D zD
    exact ⟨localizedSpaceFunctor.map p z, (congrArg
      (fun q => localizedSpaceFunctor.map s (localizedSpaceFunctor.map p q)) hzD).symm.trans
        (h.trans hzD)⟩
  choose W hW hy hWY hfix using hlocal
  have hY : IsOpen Y := isOpen_iff_mem_nhds.mpr (by
    intro y hy'
    exact Filter.mem_of_superset ((hW ⟨y, hy'⟩).mem_nhds (hy ⟨y, hy'⟩)) (hWY ⟨y, hy'⟩))
  let D := P.openDomain Y hY
  let j := domainι (localizationFunctor.obj P) D
  let C (y : Y) := P.openDomain (W y) (hW y)
  have hCD (y : Y) : C y ≤ D := hWY y
  have hcov : AtlasTopology.LocallyRefines (range fun y => (C y).carrier) {D.carrier} := by
    intro T hT y hyT
    obtain rfl := mem_singleton_iff.mp hT
    let y' : Y := ⟨y, hyT⟩
    refine ⟨{(C y').carrier}, finite_singleton _, ?_, ?_, ?_⟩
    · exact singleton_subset_iff.mpr ⟨y', rfl⟩
    · intro U hU
      obtain rfl := mem_singleton_iff.mp hU
      exact ⟨hWY y', hy y'⟩
    · rw [sUnion_singleton]
      exact mem_nhdsWithin_of_mem_nhds ((hW y').mem_nhds (hy y'))
  have hj : j ≫ (p ≫ s) = j := by
    apply eq_on_domain_of_cover D C hCD hcov ?_ rfl
    intro i
    have hinc := domainOrderMap_comp_inclusion (U := localizationFunctor.obj P) (hCD i)
    exact (hfix i).symm.trans ((congrArg (· ≫ (p ≫ s)) hinc).symm.trans (Category.assoc _ _ _))
  let a := domainLift (X := localizationFunctor.obj P) D s (fun x => mem_range_self x)
  have ha : a ≫ j = s := domainLift_comp (X := localizationFunctor.obj P) D s _
  let e : A ≅ domainObj (localizationFunctor.obj P) D :=
    ⟨a, j ≫ p, by rw [← Category.assoc, ha, hsp], by
      let : Mono j := domainι_mono (X := localizationFunctor.obj P) D
      apply (cancel_mono j).1
      rw [Category.assoc, ha, Category.assoc, hj, Category.id_comp]⟩
  exact ⟨Y, hY, e, ha⟩

end Langlands.Analytic.SaturatedAtlasPresentation
