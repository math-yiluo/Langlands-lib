import Langlands.Representation.Plancherel.StandardIntertwiningSourceQuotients
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant

/-! # Source-normalized quotients for actual dynamic radicals -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.StandardIntertwining.DynamicSource

open Aubert.General QuotientIntegration Haar
open BruhatTits.DynamicUnipotentContainment
open OrderedSubgroupFactorization

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
local instance : T2Space k := BruhatTits.localField_t2Space k
local instance : IsTopologicalGroup (RationalPoint k G.X) :=
  rationalPoint_isTopologicalGroup k G
local instance : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
local instance : LocallyCompactSpace (RationalPoint k G.X) :=
  rationalPoint_locallyCompactSpace k G

private theorem dynamicCover
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (u : unipotentPoints χ) :
    ∃ C : OpenSubgroup (unipotentPoints χ),
      IsCompact (C : Set (unipotentPoints χ)) ∧ u ∈ C := by
  obtain ⟨C, hC, hu⟩ := exists_compactOpenSubgroup χ {u} isCompact_singleton
  exact ⟨C, hC, hu (Set.mem_singleton u)⟩

private theorem closedSubgroupCover
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (H : Subgroup (RationalPoint k G.X))
    (hH : IsClosed (H : Set (RationalPoint k G.X))) (hHU : H ≤ unipotentPoints χ)
    (h : H) : ∃ C : OpenSubgroup H, IsCompact (C : Set H) ∧ h ∈ C := by
  let inclMap : H →* unipotentPoints χ := Subgroup.inclusion hHU
  have hIncl : Topology.IsClosedEmbedding (inclMap : H → unipotentPoints χ) := by
    apply Topology.IsClosedEmbedding.of_comp
      (g := (Subtype.val : unipotentPoints χ → RationalPoint k G.X))
      Topology.IsEmbedding.subtypeVal
    exact hH.isClosedEmbedding_subtypeVal
  obtain ⟨C, hC, hh⟩ := dynamicCover χ (inclMap h)
  exact ⟨C.comap inclMap hIncl.continuous, hIncl.isCompact_preimage hC, hh⟩

variable (Q : OpenSubgroup (RationalPoint k G.X))
  (hQ : IsCompact (Q : Set (RationalPoint k G.X)))

section Ordinary

variable (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  [MeasurableSpace (unipotentPoints ψ)] [BorelSpace (unipotentPoints ψ)]
  [MeasurableSpace ((unipotentPoints χ).subgroupOf (unipotentPoints ψ))]
  [BorelSpace ((unipotentPoints χ).subgroupOf (unipotentPoints ψ))]
  [MeasurableSpace (QuotientSpace (U := unipotentPoints χ) (unipotentPoints ψ))]
  [BorelSpace (QuotientSpace (U := unipotentPoints χ) (unipotentPoints ψ))]

/-- The exact source quotient on two literal dynamic radicals. Closedness,
compact-open covers and compatibility existence are proved, not supplied. -/
def quotientMeasure :
    Measure (QuotientSpace (U := unipotentPoints χ) (unipotentPoints ψ)) :=
  sourceQuotientMeasure Q hQ (unipotentPoints χ) (unipotentPoints ψ)
    (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ)
    (dynamicCover χ) (dynamicCover ψ)

/-- Full complex Weil compatibility at the common ambient source scale. -/
theorem quotientMeasure_isCompatible :
    letI := sourceIntersectionHaar_rightInvariant_of_cover Q hQ
      (unipotentPoints χ) (unipotentPoints ψ)
      (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ) (dynamicCover χ)
    IsCompatible ((unipotentPoints χ).subgroupOf (unipotentPoints ψ))
      (subgroupCompactOpenHaar Q hQ (unipotentPoints ψ) (isClosed_unipotentPoints ψ))
      (sourceIntersectionHaar Q hQ (unipotentPoints χ) (unipotentPoints ψ)
        (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ))
      (quotientMeasure Q hQ χ ψ) :=
  sourceQuotientMeasure_isCompatible Q hQ (unipotentPoints χ) (unipotentPoints ψ)
    (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ)
    (dynamicCover χ) (dynamicCover ψ)

instance quotientMeasure_regular : (quotientMeasure Q hQ χ ψ).Regular :=
  sourceQuotientMeasure_regular Q hQ (unipotentPoints χ) (unipotentPoints ψ)
    (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ)
    (dynamicCover χ) (dynamicCover ψ)

theorem quotientMeasure_ne_zero : quotientMeasure Q hQ χ ψ ≠ 0 :=
  sourceQuotientMeasure_ne_zero Q hQ (unipotentPoints χ) (unipotentPoints ψ)
    (isClosed_unipotentPoints χ) (isClosed_unipotentPoints ψ)
    (dynamicCover χ) (dynamicCover ψ)

end Ordinary

section Nested

variable (χ₀ χ₁ χ₂ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {V W : Subgroup (RationalPoint k G.X)}
  (D : OrderedSubgroupFactorization
    (unipotentPoints χ₀) (unipotentPoints χ₁) (unipotentPoints χ₂) V W)
  [MeasurableSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂))]
  [BorelSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂))]
  [MeasurableSpace ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))]
  [BorelSpace ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))]
  [MeasurableSpace (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [BorelSpace (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
      ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
      ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))]

/-- The actual nested quotient at the exact source scale, with radical
closedness and compact-open covers discharged by published dynamic results. -/
def nestedQuotientMeasure :
    Measure (QuotientIntegration.LeftQuotient
      (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
        ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))) :=
  D.sourceNestedQuotientMeasure Q hQ
    (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₁)
    (isClosed_unipotentPoints χ₂) (dynamicCover χ₀) (dynamicCover χ₁)

/-- Full Weil compatibility of the exact nested quotient. -/
theorem nestedQuotientMeasure_isCompatible :
    letI := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ
      (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₂) (dynamicCover χ₀)
    IsCompatible
      (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
        ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))
      (sourceIntersectionHaar Q hQ (unipotentPoints χ₁) (unipotentPoints χ₂)
        (isClosed_unipotentPoints χ₁) (isClosed_unipotentPoints χ₂))
      (D.sourceNestedKernelHaar Q hQ
        (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₂))
      (nestedQuotientMeasure Q hQ χ₀ χ₁ χ₂ D) :=
  D.sourceNestedQuotientMeasure_isCompatible Q hQ
    (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₁)
    (isClosed_unipotentPoints χ₂) (dynamicCover χ₀) (dynamicCover χ₁)

instance nestedQuotientMeasure_regular :
    (nestedQuotientMeasure Q hQ χ₀ χ₁ χ₂ D).Regular :=
  D.sourceNestedQuotientMeasure_regular Q hQ
    (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₁)
    (isClosed_unipotentPoints χ₂) (dynamicCover χ₀) (dynamicCover χ₁)

theorem nestedQuotientMeasure_ne_zero :
    nestedQuotientMeasure Q hQ χ₀ χ₁ χ₂ D ≠ 0 :=
  D.sourceNestedQuotientMeasure_ne_zero Q hQ
    (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₁)
    (isClosed_unipotentPoints χ₂) (dynamicCover χ₀) (dynamicCover χ₁)

end Nested

local instance : NonarchimedeanGroup (RationalPoint k G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance : SecondCountableTopology k := localField_secondCountableTopology k
local instance : SecondCountableTopology (RationalPoint k G.X) :=
  rationalPoint_secondCountableTopology k G

section Integral

open Induction

variable (χ₀ χ₁ χ₂ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {V W : Subgroup (RationalPoint k G.X)}
  (D : OrderedSubgroupFactorization
    (unipotentPoints χ₀) (unipotentPoints χ₁) (unipotentPoints χ₂) V W)
  (hV : IsClosed (V : Set (RationalPoint k G.X))) (hW : IsClosed (W : Set (RationalPoint k G.X)))
  [MeasurableSpace (unipotentPoints χ₁)] [BorelSpace (unipotentPoints χ₁)]
  [MeasurableSpace (unipotentPoints χ₂)] [BorelSpace (unipotentPoints χ₂)]
  [MeasurableSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₁))]
  [BorelSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₁))]
  [MeasurableSpace ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))]
  [BorelSpace ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))]
  [MeasurableSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂))]
  [BorelSpace ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂))]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace (V.subgroupOf (unipotentPoints χ₁))]
  [BorelSpace (V.subgroupOf (unipotentPoints χ₁))]
  [MeasurableSpace (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [BorelSpace (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [MeasurableSpace ((V.subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [BorelSpace ((V.subgroupOf (unipotentPoints χ₂)).subgroupOf
    ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)))]
  [MeasurableSpace (W.subgroupOf (unipotentPoints χ₂))]
  [BorelSpace (W.subgroupOf (unipotentPoints χ₂))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    (((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))]
  [MeasurableSpace (QuotientSpace (U := (unipotentPoints χ₀)) (unipotentPoints χ₁))]
  [BorelSpace (QuotientSpace (U := (unipotentPoints χ₀)) (unipotentPoints χ₁))]
  [MeasurableSpace (QuotientSpace (U := (unipotentPoints χ₁)) (unipotentPoints χ₂))]
  [BorelSpace (QuotientSpace (U := (unipotentPoints χ₁)) (unipotentPoints χ₂))]
  [MeasurableSpace (QuotientSpace (U := (unipotentPoints χ₀)) (unipotentPoints χ₂))]
  [BorelSpace (QuotientSpace (U := (unipotentPoints χ₀)) (unipotentPoints χ₂))]
  (hlocal₀ : D.firstSubgroupProduct ''
    ({h : (unipotentPoints χ₀).subgroupOf (unipotentPoints χ₁) | h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints χ₁)} ×ˢ
      (D.sourceFirstCompactOpen Q hV : Set (V.subgroupOf (unipotentPoints χ₁)))) =
        (sourceTargetCompactOpen Q (isClosed_unipotentPoints χ₁) : Set (unipotentPoints χ₁)))
  (hlocal₁ : D.intersectionSubgroupProduct ''
    ({h : ((unipotentPoints χ₀).subgroupOf (unipotentPoints χ₂)).subgroupOf ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂)) |
        h.val ∈ sourceMiddleCompactOpen Q (isClosed_unipotentPoints χ₁) (isClosed_unipotentPoints χ₂)} ×ˢ
      (D.sourceNestedComplementCompactOpen Q hV :
        Set ((V.subgroupOf (unipotentPoints χ₂)).subgroupOf ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))) =
      (sourceMiddleCompactOpen Q (isClosed_unipotentPoints χ₁) (isClosed_unipotentPoints χ₂) : Set ((unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂))))
  (hlocal₂ : D.secondSubgroupProduct ''
    ({h : (unipotentPoints χ₁).subgroupOf (unipotentPoints χ₂) | h.val ∈ sourceTargetCompactOpen Q (isClosed_unipotentPoints χ₂)} ×ˢ
      (D.sourceSecondComplementCompactOpen Q hW : Set (W.subgroupOf (unipotentPoints χ₂)))) =
      (sourceTargetCompactOpen Q (isClosed_unipotentPoints χ₂) : Set (unipotentPoints χ₂)))
  {P₀ P₁ M : Subgroup (RationalPoint k G.X)}
  (h₀ : IsSemidirectDecomposition P₀ M (unipotentPoints χ₀))
  (h₁ : IsSemidirectDecomposition P₁ M (unipotentPoints χ₁))
  (A : Langlands.SmoothRep.{0, u, uV} ℂ M)

include hlocal₀ hlocal₁ hlocal₂ in
/-- Actual dynamic-radical composition with all original covers and radical
closedness proved. Quotients are fixed before the unchanged integral witnesses. -/
theorem comp_hasIntegral
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ (isClosed_unipotentPoints χ₀)).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ (isClosed_unipotentPoints χ₁)).obj A}
    {J : RationalPoint k G.X → A}
    (hf : HasIntegral h₀ (isClosed_unipotentPoints χ₀) (unipotentPoints χ₁) A
      (quotientMeasure Q hQ χ₀ χ₁) f
      (eval P₁ (leviInflatedInducingRepresentation h₁ (isClosed_unipotentPoints χ₁) A) F))
    (hF : HasIntegral h₁ (isClosed_unipotentPoints χ₁) (unipotentPoints χ₂) A
      (quotientMeasure Q hQ χ₁ χ₂) F J)
    (ha : OrderedScalarIntegrable h₀ (isClosed_unipotentPoints χ₀) A
      (subgroupCompactOpenHaar Q hQ V hV)
      (subgroupCompactOpenHaar Q hQ W hW) f) :
    HasIntegral h₀ (isClosed_unipotentPoints χ₀) (unipotentPoints χ₂) A
      (quotientMeasure Q hQ χ₀ χ₂) f J := by
  exact D.comp_hasIntegral_at_sourceQuotients Q hQ
    (isClosed_unipotentPoints χ₀) (isClosed_unipotentPoints χ₁)
    (isClosed_unipotentPoints χ₂) hV hW
    (dynamicCover χ₀) (dynamicCover χ₁) (dynamicCover χ₂)
    (closedSubgroupCover χ₁ V hV D.first_le)
    (closedSubgroupCover χ₂ W hW D.second_le)
    hlocal₀ hlocal₁ hlocal₂ h₀ h₁ A hf hF ha

end Integral

end Langlands.Plancherel.StandardIntertwining.DynamicSource
