import Langlands.Representation.Plancherel.DynamicCommonLeviCompositionLocalProducts

/-! # Composition of standard integrals with a common Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open Aubert.General StandardIntertwining DynamicOppositeStandardIntertwining
open BruhatTits.DynamicUnipotentContainment
open OrderedSubgroupFactorization QuotientIntegration Haar Induction

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance : SecondCountableTopology F := localField_secondCountableTopology F
local instance : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G

local instance subgroupMeasurableSpace {H : Type*} [Group H] [TopologicalSpace H]
    (S : Subgroup H) : MeasurableSpace S := borel _
local instance subgroupBorelSpace {H : Type*} [Group H] [TopologicalSpace H]
    (S : Subgroup H) : BorelSpace S := ⟨rfl⟩
local instance subgroupSecondCountable {H : Type*} [Group H] [TopologicalSpace H]
    [SecondCountableTopology H] (S : Subgroup H) : SecondCountableTopology S :=
  TopologicalSpace.Subtype.secondCountableTopology (S : Set H)
local instance quotientMeasurableSpace {H : Type*} [Group H] [TopologicalSpace H]
    (S : Subgroup H) : MeasurableSpace (QuotientIntegration.LeftQuotient S) := borel _
local instance quotientBorelSpace {H : Type*} [Group H] [TopologicalSpace H]
    (S : Subgroup H) : BorelSpace (QuotientIntegration.LeftQuotient S) := ⟨rfl⟩

private theorem radicalCover (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (x : radical ψ) :
    ∃ C : OpenSubgroup (radical ψ), IsCompact (C : Set (radical ψ)) ∧ x ∈ C := by
  obtain ⟨C, hC, hx⟩ := exists_compactOpenSubgroup ψ {x} isCompact_singleton
  exact ⟨C, hC, hx (Set.mem_singleton x)⟩

private theorem closedSubgroupCover
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (H : Subgroup (RationalPoint F G.X))
    (hH : IsClosed (H : Set (RationalPoint F G.X))) (hHU : H ≤ radical ψ)
    (x : H) : ∃ C : OpenSubgroup H, IsCompact (C : Set H) ∧ x ∈ C := by
  let inclMap : H →* radical ψ := Subgroup.inclusion hHU
  have hIncl : Topology.IsClosedEmbedding (inclMap : H → radical ψ) := by
    apply Topology.IsClosedEmbedding.of_comp
      (g := (Subtype.val : radical ψ → RationalPoint F G.X))
      Topology.IsEmbedding.subtypeVal
    exact hH.isClosedEmbedding_subtypeVal
  obtain ⟨C, hC, hx⟩ := radicalCover ψ (inclMap x)
  exact ⟨C.comap inclMap hIncl.continuous, hIncl.isCompact_preimage hC, hx⟩

section CompositeMeasure

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  {V W : Subgroup (RationalPoint F G.X)}
  (D : OrderedSubgroupFactorization (radical ψ₀) (radical ψ₁) (radical ψ₂) V W)
  (hV : IsClosed (V : Set (RationalPoint F G.X)))
  (hW : IsClosed (W : Set (RationalPoint F G.X)))

set_option maxHeartbeats 800000 in
private theorem composite_measurePreserving
    (hlocal₁ : D.intersectionSubgroupProduct ''
      ({h : ((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
          ((radical ψ₁).subgroupOf (radical ψ₂)) |
          h.val ∈ sourceMiddleCompactOpen K (radical_isClosed ψ₁) (radical_isClosed ψ₂)} ×ˢ
        (D.sourceNestedComplementCompactOpen K hV :
          Set ((V.subgroupOf (radical ψ₂)).subgroupOf
            ((radical ψ₁).subgroupOf (radical ψ₂))))) =
      (sourceMiddleCompactOpen K (radical_isClosed ψ₁) (radical_isClosed ψ₂) :
        Set ((radical ψ₁).subgroupOf (radical ψ₂))))
    (hlocal₂ : D.secondSubgroupProduct ''
      ({h : (radical ψ₁).subgroupOf (radical ψ₂) |
          h.val ∈ sourceTargetCompactOpen K (radical_isClosed ψ₂)} ×ˢ
        (D.sourceSecondComplementCompactOpen K hW :
          Set (W.subgroupOf (radical ψ₂)))) =
      (sourceTargetCompactOpen K (radical_isClosed ψ₂) : Set (radical ψ₂))) :
    MeasurePreserving D.quotientCoordinates.composite
      ((subgroupCompactOpenHaar K hK V hV).prod (subgroupCompactOpenHaar K hK W hW))
      (pairQuotientMeasure K hK ψ₀ ψ₂) := by
  let : LocallyCompactSpace (radical ψ₂) := (radical_isClosed ψ₂).locallyCompactSpace
  have hI₂₁ : IsClosed ((radical ψ₁).subgroupOf (radical ψ₂) : Set (radical ψ₂)) :=
    (radical_isClosed ψ₁).preimage continuous_subtype_val
  let : LocallyCompactSpace ((radical ψ₁).subgroupOf (radical ψ₂)) :=
    hI₂₁.locallyCompactSpace
  have hI₂₀ : IsClosed ((radical ψ₀).subgroupOf (radical ψ₂) : Set (radical ψ₂)) :=
    (radical_isClosed ψ₀).preimage continuous_subtype_val
  let : LocallyCompactSpace ((radical ψ₀).subgroupOf (radical ψ₂)) :=
    hI₂₀.locallyCompactSpace
  have hH : IsClosed
      (((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
        ((radical ψ₁).subgroupOf (radical ψ₂)) :
          Set ((radical ψ₁).subgroupOf (radical ψ₂))) :=
    (radical_isClosed ψ₀).preimage (continuous_subtype_val.comp continuous_subtype_val)
  let : LocallyCompactSpace
      (((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
        ((radical ψ₁).subgroupOf (radical ψ₂))) := hH.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : LocallyCompactSpace W := hW.locallyCompactSpace
  let : LocallyCompactSpace
      ((V.subgroupOf (radical ψ₂)).subgroupOf
        ((radical ψ₁).subgroupOf (radical ψ₂))) :=
    D.intersectionComplementEquiv.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace (W.subgroupOf (radical ψ₂)) :=
    D.secondComplementEquiv.isClosedEmbedding.locallyCompactSpace
  let := pairIntersectionHaar_rightInvariant K hK ψ₁ ψ₂
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover K hK
    (radical_isClosed ψ₀) (radical_isClosed ψ₂) (radicalCover ψ₀)
  let := D.sourceNestedComplementHaar_rightInvariant_of_cover K hK hV
    (closedSubgroupCover ψ₁ V hV D.first_le)
  let := D.sourceSecondComplementHaar_rightInvariant_of_cover K hK hW
    (closedSubgroupCover ψ₂ W hW D.second_le)
  have : PseudoMetrizableSpace
      ((((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
        ((radical ψ₁).subgroupOf (radical ψ₂))) ×
        ((V.subgroupOf (radical ψ₂)).subgroupOf
          ((radical ψ₁).subgroupOf (radical ψ₂)))) := inferInstance
  have : SigmaCompactSpace
      ((((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
        ((radical ψ₁).subgroupOf (radical ψ₂))) ×
        ((V.subgroupOf (radical ψ₂)).subgroupOf
          ((radical ψ₁).subgroupOf (radical ψ₂)))) := inferInstance
  have : IsLocallyFiniteMeasure
      ((D.sourceNestedKernelHaar K hK (radical_isClosed ψ₀) (radical_isClosed ψ₂)).prod
        (D.sourceNestedComplementHaar K hK hV)) := inferInstance
  have : PseudoMetrizableSpace (((radical ψ₁).subgroupOf (radical ψ₂)) ×
      (W.subgroupOf (radical ψ₂))) := inferInstance
  have : SigmaCompactSpace (((radical ψ₁).subgroupOf (radical ψ₂)) ×
      (W.subgroupOf (radical ψ₂))) := inferInstance
  have : IsLocallyFiniteMeasure
      ((sourceIntersectionHaar K hK (radical ψ₁) (radical ψ₂)
        (radical_isClosed ψ₁) (radical_isClosed ψ₂)).prod
        (D.sourceSecondComplementHaar K hK hW)) := inferInstance
  have : PseudoMetrizableSpace (V × W) := inferInstance
  have : SigmaCompactSpace (V × W) := inferInstance
  have : IsLocallyFiniteMeasure
      ((subgroupCompactOpenHaar K hK V hV).prod
        (subgroupCompactOpenHaar K hK W hW)) := inferInstance
  have hp := D.measurePreserving_normalizedProducts
    (radical_isClosed ψ₀) (radical_isClosed ψ₁) (radical_isClosed ψ₂)
    (subgroupCompactOpenHaar K hK (radical ψ₂) (radical_isClosed ψ₂))
    (sourceIntersectionHaar K hK (radical ψ₁) (radical ψ₂)
      (radical_isClosed ψ₁) (radical_isClosed ψ₂))
    (D.sourceNestedKernelHaar K hK (radical_isClosed ψ₀) (radical_isClosed ψ₂))
    (D.sourceNestedComplementHaar K hK hV)
    (D.sourceSecondComplementHaar K hK hW)
    (sourceMiddleCompactOpen K (radical_isClosed ψ₁) (radical_isClosed ψ₂))
    (D.sourceNestedComplementCompactOpen K hV)
    (sourceTargetCompactOpen K (radical_isClosed ψ₂))
    (D.sourceSecondComplementCompactOpen K hW)
    (DynamicSource.nestedQuotientMeasure K hK ψ₀ ψ₁ ψ₂ D)
    (pairQuotientMeasure K hK ψ₁ ψ₂)
    (DynamicSource.nestedQuotientMeasure_isCompatible K hK ψ₀ ψ₁ ψ₂ D)
    (pairQuotientMeasure_isCompatible K hK ψ₁ ψ₂)
    (compactOpenPreimage_isCompact K hK _ _)
    (compactOpenPreimage_isCompact K hK _ _) hlocal₁
    (compactOpenPreimage_isCompact K hK _ _)
    (compactOpenPreimage_isCompact K hK _ _) hlocal₂
  have hkernel := D.intersectionKernelMeasure_source K hK
    (radical_isClosed ψ₀) (radical_isClosed ψ₂)
  have hfirst := D.intersectionNormalizedFactor_source K hK hV
    (radical_isClosed ψ₀) (radical_isClosed ψ₁) (radical_isClosed ψ₂)
  have hsecond := D.secondNormalizedFactor_source K hK hW
    (radical_isClosed ψ₁) (radical_isClosed ψ₂)
  have hc := hp.2
  simp only [hkernel, hfirst, hsecond] at hc
  exact (pairQuotientMeasure_isCompatible K hK ψ₀ ψ₂).measurePreserving_factorQuotientHomeomorph
    ((radical ψ₀).subgroupOf (radical ψ₂))
    (fun p : V × W =>
      Subgroup.inclusion D.first_le_target p.1 * Subgroup.inclusion D.second_le p.2)
    D.composite D.composite_eq hI₂₀ hc

end CompositeMeasure

/-- Waldspurger IV.1 (12) on the full common convergence domain, conditional
only on the structural factorization premise of the published statement. -/
theorem conditionalDynamicCommonLeviComposition :
    ConditionalDynamicCommonLeviCompositionStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ _ hfac hG χ K hK ψ₀ ψ₁ ψ₂ h₀ h₁ h₂ hd
    hK₁₀ hK₂₁ hδ₁₀ hδ₂₁ hδ₂₀ A z hz₁₀ hz₂₁ hz₂₀ f
  obtain ⟨D⟩ := hfac hG ψ₀ ψ₁ ψ₂ (h₁.trans h₀.symm) (h₂.trans h₀.symm) hd
  have hV := LocalProducts.firstComplement_isClosed ψ₀ ψ₁
  have hW := LocalProducts.secondComplement_isClosed ψ₁ ψ₂
  have hlocal₀ := LocalProducts.first_localProduct_of_splitsAlong ψ₀ ψ₁ ψ₂ D K hK₁₀
  have hlocal₁ := LocalProducts.middle_localProduct_of_splitsAlong ψ₀ ψ₁ ψ₂ D K hK₁₀
  have hlocal₂ := LocalProducts.second_localProduct_of_splitsAlong ψ₀ ψ₁ ψ₂ D K hK₂₁
  let B := A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))
  have hf := pairFamily_spec χ K hK ψ₀ h₀ ψ₁ h₁ hδ₁₀ A ⟨z, hz₁₀⟩ f
  have hF := pairFamily_spec χ K hK ψ₁ h₁ ψ₂ h₂ hδ₂₁ A ⟨z, hz₂₁⟩
    (pairFamily χ K hK ψ₀ h₀ ψ₁ h₁ hδ₁₀ A ⟨z, hz₁₀⟩ f)
  have hdirect := pairFamily_spec χ K hK ψ₀ h₀ ψ₂ h₂ hδ₂₀ A ⟨z, hz₂₀⟩ f
  have hm := composite_measurePreserving K hK ψ₀ ψ₁ ψ₂ D hV hW hlocal₁ hlocal₂
  have ha : OrderedScalarIntegrable (commonDecomposition χ ψ₀ h₀) (radical_isClosed ψ₀) B
      (subgroupCompactOpenHaar K hK (radical ψ₁ ⊓ oppositeRadical ψ₀) hV)
      (subgroupCompactOpenHaar K hK (radical ψ₂ ⊓ oppositeRadical ψ₁) hW) f := by
    intro g ℓ
    have hi := hm.integrable_comp_of_integrable ((hdirect g ℓ).1)
    simpa only [Function.comp_def, OrderedQuotientCoordinates.composite_eq, integrand_mk,
      Subgroup.coe_mul, Subgroup.coe_inclusion] using hi
  have hcomp := DynamicSource.comp_hasIntegral K hK ψ₀ ψ₁ ψ₂ D hV hW
    hlocal₀ hlocal₁ hlocal₂
    (commonDecomposition χ ψ₀ h₀) (commonDecomposition χ ψ₁ h₁) B hf hF ha
  have heq (g : RationalPoint F G.X) :=
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique (ρ := B.representation)
      (compactCofinal (levi_isClosed χ)) B.property (hdirect g) (hcomp g)
  exact Subtype.ext (Subtype.ext (funext heq))

end Langlands.Plancherel.DynamicCommonLeviComposition
