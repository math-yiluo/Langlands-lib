import Langlands.Geometry.Analytic.AtlasDomainCategory
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutAdmissibility

/-! # Tensor-admissible intersections inside one full local domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- A local inclusion is itself a full domain over the unchanged containing
algebra, with the original input algebra and actual bounded restriction. -/
def Inclusion.relativeDomain {U Z : LocalDomain a} (f : U ⟶ Z) :
    Domain K Z.algebra where
  algebra := U.algebra
  baseMap := f.restriction
  locus := Z.ambientMap ⁻¹' U.locus
  represents := f.represents

/-- The inclusion of an extended domain retains exactly the inner base map. -/
def extendInclusion (Z : LocalDomain a) (D : Domain K Z.algebra) :
    Z.extend D ⟶ Z :=
  (sameChartFunctor a Z.index).map (Z.domain.extendInclusion D)

@[simp]
theorem extendInclusion_restriction (Z : LocalDomain a) (D : Domain K Z.algebra) :
    (Z.extendInclusion D).restriction = D.baseMap := rfl

variable {U V Z : LocalDomain a} (f : U ⟶ Z) (g : V ⟶ Z)

/-- The actual relative affinoid pushout, extended into the original atlas. -/
def interOver : LocalDomain a :=
  Z.extend (f.relativeDomain.inter g.relativeDomain)

theorem interOver_locus : (interOver f g).locus = U.locus ∩ V.locus := by
  rw [interOver, extend_locus]
  change Z.ambientMap '' (Z.ambientMap ⁻¹' U.locus ∩ Z.ambientMap ⁻¹' V.locus) = _
  ext x
  constructor
  · rintro ⟨z, ⟨hzU, hzV⟩, rfl⟩
    exact ⟨hzU, hzV⟩
  · rintro ⟨hxU, hxV⟩
    have hxZ : x ∈ Set.range Z.ambientMap := Z.range_ambientMap.symm ▸ f.subset hxU
    obtain ⟨z, rfl⟩ := hxZ
    exact ⟨z, ⟨hxU, hxV⟩, rfl⟩

/-- The actual map to the containing domain is the composite pushout leg. -/
def interOverToBase : interOver f g ⟶ Z :=
  Z.extendInclusion (f.relativeDomain.inter g.relativeDomain)

/-- Canonical full-domain restriction to the first unchanged input domain. -/
def interOverLeft : interOver f g ⟶ U :=
  Inclusion.ofSubset _ _ (by
    rw [interOver_locus]
    exact Set.inter_subset_left)

/-- Canonical full-domain restriction to the second unchanged input domain. -/
def interOverRight : interOver f g ⟶ V :=
  Inclusion.ofSubset _ _ (by
    rw [interOver_locus]
    exact Set.inter_subset_right)

theorem interOverLeft_restriction :
    (interOverLeft f g).restriction =
      AffinoidPushout.leftMap f.restriction g.restriction := by
  apply f.represents.hom_ext (interOver f g).algebra
  have h : interOverLeft f g ≫ f = interOverToBase f g :=
    @Subsingleton.elim (Inclusion (interOver f g) Z) inferInstance _ _
  exact congrArg Inclusion.restriction h

theorem interOverRight_restriction :
    (interOverRight f g).restriction =
      AffinoidPushout.rightMap f.restriction g.restriction := by
  apply g.represents.hom_ext (interOver f g).algebra
  have h : interOverRight f g ≫ g = interOverToBase f g :=
    @Subsingleton.elim (Inclusion (interOver f g) Z) inferInstance _ _
  exact (congrArg Inclusion.restriction h).trans
    (AffinoidPushout.condition f.restriction g.restriction)

/-- The genuine tensor map of the actual full-domain inclusion restrictions
is admissible, including its positive quotient-seminorm comparison. -/
theorem interOver_tensor_isAdmissibleEpi :
    (CompletedTensorAlgebra.lift
      (interOverLeft f g).restriction (interOverRight f g).restriction).IsAdmissibleEpi := by
  rw [interOverLeft_restriction, interOverRight_restriction]
  exact AffinoidPushout.tensorMap_isAdmissibleEpi f.restriction g.restriction

include f g in
/-- The full local-domain conclusion whenever the two inputs have one full
local-domain container. The input algebras are unchanged. -/
theorem exists_tensorAdmissible_intersection_of_common_container :
    ∃ R : LocalDomain a, ∃ hR : R.locus = U.locus ∩ V.locus,
      (CompletedTensorAlgebra.lift
        (Inclusion.ofSubset R U (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.1)).restriction
        (Inclusion.ofSubset R V (by
          intro x hx
          have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
          exact hx'.2)).restriction).IsAdmissibleEpi := by
  refine ⟨interOver f g, interOver_locus f g, ?_⟩
  exact interOver_tensor_isAdmissibleEpi f g

end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
