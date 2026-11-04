import Langlands.Geometry.Analytic.AtlasDomainRestrictionNaturality

/-! # Coherent reexpression of local full domains in original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Extending a domain along an original contained chart does not change its
constructed bounded restriction from any other containing original chart. -/
theorem domainChartRestriction_extendDomain (i j k : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart k))
    (hext : a.chart j '' (a.extendDomain i j hij U).locus ⊆ Set.range (a.chart k)) :
    a.domainChartRestriction j k (a.extendDomain i j hij U) hext =
      a.domainChartRestriction i k U h := by
  let c := a.domainImageChartCover i k U h
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  let V := a.extendDomain i j hij (c.domainCover.obj t)
  let p : V ⟶ a.extendDomain i j hij U :=
    (a.extendDomainFunctor i j hij).map (c.domainCover.map t)
  let g : V ⟶ a.restrictionDomain (c.index t) j ((c.left_subset t).trans hij) :=
    ⟨(c.domainCoverToChart t).restriction, by
      change (c.domainCoverToChart t).restriction.comp
          (a.restriction (c.index t) j ((c.left_subset t).trans hij)) =
        (c.domainCover.obj t).baseMap.comp (a.restriction i j hij)
      erw [a.restriction_comp (c.index t) i j (c.left_subset t) hij
        ((c.left_subset t).trans hij), ← BoundedAlgHom.comp_assoc,
        (c.domainCoverToChart t).comp_baseMap]⟩
  have hlocal := a.domainChartRestriction_test j k (a.extendDomain i j hij U) hext
    V p (c.index t) ((c.left_subset t).trans hij) (c.right_subset t) g
  exact congrArg (fun q : BoundedAlgHom K (a.algebra k)
    (c.domainCover.obj t).algebra => q b)
    (hlocal.trans (c.restriction_comp_glueChartRestriction t).symm)

/-- Original full-domain inclusions retain their entire bounded maps after
reexpression in any common containing original chart. -/
def domainInChartInclusion (i j : a.Index)
    {U V : Domain K (a.algebra i)} (f : V ⟶ U)
    (hU : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hV : a.chart i '' V.locus ⊆ Set.range (a.chart j)) :
    a.domainInChart i j V hV ⟶ a.domainInChart i j U hU :=
  ⟨f.restriction, a.domainChartRestriction_naturality i j f hU hV⟩

@[simp]
theorem domainInChartInclusion_restriction (i j : a.Index)
    {U V : Domain K (a.algebra i)} (f : V ⟶ U)
    (hU : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hV : a.chart i '' V.locus ⊆ Set.range (a.chart j)) :
    (a.domainInChartInclusion i j f hU hV).restriction = f.restriction := rfl

/-- Reexpression through an unrelated intermediate original chart gives
exactly the direct bounded map on the unchanged original domain algebra. -/
theorem domainChartRestriction_reexpression (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k))
    (hjk : a.chart j '' (a.domainInChart i j U hj).locus ⊆ Set.range (a.chart k)) :
    a.domainChartRestriction j k (a.domainInChart i j U hj) hjk =
      a.domainChartRestriction i k U hk := by
  let c := a.domainImageChartCover i j U hj
  have hi (t : Fin c.size) :
      a.chart i '' (c.domainCover.obj t).locus ⊆ Set.range (a.chart k) :=
    (Set.image_mono (c.domainCover.map t).subset).trans hk
  have hm (t : Fin c.size) :
      a.chart (c.index t) '' (c.domainOverChart t).locus ⊆ Set.range (a.chart k) := by
    rw [c.chart_image_domainOverChart t]
    exact hi t
  have hjt (t : Fin c.size) :
      a.chart j '' (c.domainOverRightChart t).locus ⊆ Set.range (a.chart k) := by
    rw [c.chart_image_domainOverRightChart t]
    exact hi t
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  let f : c.domainOverRightChart t ⟶ a.domainInChart i j U hj :=
    ⟨(c.domainCover.map t).restriction, c.restriction_comp_glueChartRestriction t⟩
  have hleft₁ := a.domainChartRestriction_naturality j k f hjk (hjt t)
  have hleft₂ := a.domainChartRestriction_extendDomain (c.index t) j k
    (c.right_subset t) (c.domainOverChart t) (hm t) (hjt t)
  let E := a.extendDomain (c.index t) i (c.left_subset t) (c.domainOverChart t)
  have hE : a.chart i '' E.locus ⊆ Set.range (a.chart k) := by
    rw [a.chart_image_extendDomain_locus]
    exact hm t
  let e : E ≅ c.domainCover.obj t :=
    a.extendRestrictDomainIso (c.index t) i (c.left_subset t)
      (c.domainCover.obj t) (c.domainCoverToChart t)
  have hright₁ := a.domainChartRestriction_naturality i k (c.domainCover.map t) hk (hi t)
  have hright₂ := a.domainChartRestriction_naturality i k e.hom (hi t) hE
  have hright₃ := a.domainChartRestriction_extendDomain (c.index t) i k
    (c.left_subset t) (c.domainOverChart t) (hm t) hE
  have hright :
      (c.domainCover.map t).restriction.comp (a.domainChartRestriction i k U hk) =
        a.domainChartRestriction (c.index t) k (c.domainOverChart t) (hm t) :=
    hright₁.trans (hright₂.trans hright₃)
  have hleft :
      (c.domainCover.map t).restriction.comp
          (a.domainChartRestriction j k (a.domainInChart i j U hj) hjk) =
        a.domainChartRestriction (c.index t) k (c.domainOverChart t) (hm t) :=
    hleft₁.trans hleft₂
  exact congrArg (fun q : BoundedAlgHom K (a.algebra k)
    (c.domainCover.obj t).algebra => q b) (hleft.trans hright.symm)

/-- The self reexpression comparison uses bounded identities on the
original stored domain algebra. -/
def domainInChartSelfIso (i : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart i)) :
    a.domainInChart i i U h ≅ U where
  hom := ⟨BoundedAlgHom.id K U.algebra, (a.domainChartRestriction_self i U h).symm⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, a.domainChartRestriction_self i U h⟩
  hom_inv_id := @Subsingleton.elim (Domain.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (Domain.Inclusion _ _) inferInstance _ _

/-- The transitive comparison also has identity bounded maps; its structural
equations are the proved complete bounded-map coherence. -/
def domainInChartTransIso (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k))
    (hjk : a.chart j '' (a.domainInChart i j U hj).locus ⊆ Set.range (a.chart k)) :
    a.domainInChart j k (a.domainInChart i j U hj) hjk ≅ a.domainInChart i k U hk where
  hom := ⟨BoundedAlgHom.id K U.algebra,
    (a.domainChartRestriction_reexpression i j k U hj hk hjk).symm⟩
  inv := ⟨BoundedAlgHom.id K U.algebra,
    a.domainChartRestriction_reexpression i j k U hj hk hjk⟩
  hom_inv_id := @Subsingleton.elim (Domain.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (Domain.Inclusion _ _) inferInstance _ _

end Langlands.Analytic.IndexedAffinoidAtlas
