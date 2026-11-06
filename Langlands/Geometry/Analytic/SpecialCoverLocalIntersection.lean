import Langlands.Geometry.Analytic.SpecialCoverDomainIntersection

/-! # Unchanged-algebra local intersections subordinate to a special cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace LocalDomain

/-- Reexpress a full local domain in any containing original chart, keeping
exactly the original algebra. -/
def reexpress (U : LocalDomain a) (i : a.Index)
    (h : U.locus ⊆ Set.range (a.chart i)) : LocalDomain a :=
  ⟨i, a.domainInChart U.index i U.domain h⟩

theorem reexpress_locus (U : LocalDomain a) (i : a.Index)
    (h : U.locus ⊆ Set.range (a.chart i)) :
    (U.reexpress i h).locus = U.locus :=
  a.chart_image_domainInChart U.index i U.domain h

/-- Reexpression is an actual local-domain isomorphism whose restrictions
in both directions are bounded identities on the original algebra. -/
def reexpressIso (U : LocalDomain a) (i : a.Index)
    (h : U.locus ⊆ Set.range (a.chart i)) : U ≅ U.reexpress i h where
  hom :=
    { subset := fun _ hx => (U.reexpress_locus i h).symm ▸ hx
      restriction := BoundedAlgHom.id K U.algebra
      comp_chart q hU hV :=
        a.domainChartRestriction_reexpression U.index i q U.domain h hU hV }
  inv :=
    { subset := fun _ hx => U.reexpress_locus i h ▸ hx
      restriction := BoundedAlgHom.id K U.algebra
      comp_chart q hU hV :=
        (a.domainChartRestriction_reexpression U.index i q U.domain h hV hU).symm }
  hom_inv_id := Inclusion.ext rfl
  inv_hom_id := Inclusion.ext rfl

end LocalDomain

namespace FiniteChartGluingData

variable (d : FiniteChartGluingData a) (i j : Fin d.size)
  (U V : LocalDomain a)
  (hU : U.locus ⊆ Set.range (a.chart (d.index i)))
  (hV : V.locus ⊆ Set.range (a.chart (d.index j)))

/-- The local intersection for arbitrary original presentations subordinate
to two members of the given finite cover. -/
def localIntersection : LocalDomain a :=
  d.domainIntersection i j
    (a.domainInChart U.index (d.index i) U.domain hU)
    (a.domainInChart V.index (d.index j) V.domain hV)

theorem localIntersection_locus :
    (d.localIntersection i j U V hU hV).locus = U.locus ∩ V.locus := by
  exact (d.domainIntersection_locus i j _ _).trans
    (congrArg₂ (fun S T : Set X => S ∩ T)
      (U.reexpress_locus (d.index i) hU) (V.reexpress_locus (d.index j) hV))

def localIntersectionLeft : d.localIntersection i j U V hU hV ⟶ U :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [localIntersection_locus]
    exact Set.inter_subset_left)

def localIntersectionRight : d.localIntersection i j U V hU hV ⟶ V :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [localIntersection_locus]
    exact Set.inter_subset_right)

/-- The canonical original-algebra restriction is unchanged by reexpression. -/
theorem localIntersectionLeft_restriction :
    (d.localIntersectionLeft i j U V hU hV).restriction =
      (d.domainIntersectionLeft i j
        (a.domainInChart U.index (d.index i) U.domain hU)
        (a.domainInChart V.index (d.index j) V.domain hV)).restriction := by
  have heq :
      d.localIntersectionLeft i j U V hU hV =
        d.domainIntersectionLeft i j
          (a.domainInChart U.index (d.index i) U.domain hU)
          (a.domainInChart V.index (d.index j) V.domain hV) ≫
          (U.reexpressIso (d.index i) hU).inv :=
    @Subsingleton.elim (LocalDomain.Inclusion (d.localIntersection i j U V hU hV) U)
      inferInstance _ _
  exact congrArg LocalDomain.Inclusion.restriction heq

theorem localIntersectionRight_restriction :
    (d.localIntersectionRight i j U V hU hV).restriction =
      (d.domainIntersectionRight i j
        (a.domainInChart U.index (d.index i) U.domain hU)
        (a.domainInChart V.index (d.index j) V.domain hV)).restriction := by
  have heq :
      d.localIntersectionRight i j U V hU hV =
        d.domainIntersectionRight i j
          (a.domainInChart U.index (d.index i) U.domain hU)
          (a.domainInChart V.index (d.index j) V.domain hV) ≫
          (V.reexpressIso (d.index j) hV).inv :=
    @Subsingleton.elim (LocalDomain.Inclusion (d.localIntersection i j U V hU hV) V)
      inferInstance _ _
  exact congrArg LocalDomain.Inclusion.restriction heq

/-- The genuine tensor map uses the two unchanged original local-domain
algebras and their canonical bounded inclusion restrictions. -/
theorem localIntersection_tensor_isAdmissibleEpi
    (h : (d.overlapTensorMap i j).IsAdmissibleEpi) :
    (CompletedTensorAlgebra.lift
      (d.localIntersectionLeft i j U V hU hV).restriction
      (d.localIntersectionRight i j U V hU hV).restriction).IsAdmissibleEpi := by
  rw [localIntersectionLeft_restriction, localIntersectionRight_restriction]
  exact d.domainIntersection_tensor_isAdmissibleEpi i j _ _ h

end FiniteChartGluingData
end Langlands.Analytic.IndexedAffinoidAtlas
