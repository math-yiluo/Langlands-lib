import Langlands.Representation.Plancherel.DynamicCommonLeviComposition

/-! # Compact-open products for distance-additive common-Levi charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCommonLeviComposition.LocalProducts

open Aubert.General StandardIntertwining DynamicOppositeStandardIntertwining
open OrderedSubgroupFactorization

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

omit [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The first ordered complement is a closed intersection of actual radicals. -/
theorem firstComplement_isClosed
    (ψ₀ ψ₁ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    IsClosed ((radical ψ₁ ⊓ oppositeRadical ψ₀ :
      Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) :=
  (radical_isClosed ψ₁).inter (radical_isClosed (Dynamic.inverseCocharacter ψ₀))

omit [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The second ordered complement is a closed intersection of actual radicals. -/
theorem secondComplement_isClosed
    (ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    IsClosed ((radical ψ₂ ⊓ oppositeRadical ψ₁ :
      Subgroup (RationalPoint F G.X)) : Set (RationalPoint F G.X)) :=
  (radical_isClosed ψ₂).inter (radical_isClosed (Dynamic.inverseCocharacter ψ₁))

variable (ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (D : OrderedSubgroupFactorization (radical ψ₀) (radical ψ₁) (radical ψ₂)
    (radical ψ₁ ⊓ oppositeRadical ψ₀) (radical ψ₂ ⊓ oppositeRadical ψ₁))
  (Q : OpenSubgroup (RationalPoint F G.X))

omit [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The first splitting gives the exact local product in any supplied first chart. -/
theorem first_localProduct_of_splitsAlong (hs : CommonLeviSplitting.SplitsAlong Q ψ₀ ψ₁) :
    D.firstSubgroupProduct ''
      ({h : (radical ψ₀).subgroupOf (radical ψ₁) |
          h.val ∈ sourceTargetCompactOpen Q (radical_isClosed ψ₁)} ×ˢ
        (D.sourceFirstCompactOpen Q (firstComplement_isClosed ψ₀ ψ₁) :
          Set ((radical ψ₁ ⊓ oppositeRadical ψ₀ :
            Subgroup (RationalPoint F G.X)).subgroupOf (radical ψ₁)))) =
      (sourceTargetCompactOpen Q (radical_isClosed ψ₁) : Set (radical ψ₁)) := by
  have hfac : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (radical ψ₀ ⊓ radical ψ₁) (radical ψ₁ ⊓ oppositeRadical ψ₀) (radical ψ₁) :=
    hs.second.mono le_rfl (inf_comm _ _).le
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [firstSubgroupProduct_eq]
    exact (sourceTargetCompactOpen Q (radical_isClosed ψ₁)).mul_mem hh hk
  · intro hx
    obtain ⟨a, ha, haQ, b, hb, hbQ, hab⟩ := hfac x.val x.property hx
    refine ⟨⟨⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1⟩,
      ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.mpr hb⟩⟩, ⟨haQ, hbQ⟩, ?_⟩
    rw [firstSubgroupProduct_eq]
    exact Subtype.ext hab.symm

omit [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The second splitting gives the exact local product in any supplied second chart. -/
theorem second_localProduct_of_splitsAlong (hs : CommonLeviSplitting.SplitsAlong Q ψ₁ ψ₂) :
    D.secondSubgroupProduct ''
      ({h : (radical ψ₁).subgroupOf (radical ψ₂) |
          h.val ∈ sourceTargetCompactOpen Q (radical_isClosed ψ₂)} ×ˢ
        (D.sourceSecondComplementCompactOpen Q (secondComplement_isClosed ψ₁ ψ₂) :
          Set ((radical ψ₂ ⊓ oppositeRadical ψ₁ :
            Subgroup (RationalPoint F G.X)).subgroupOf (radical ψ₂)))) =
      (sourceTargetCompactOpen Q (radical_isClosed ψ₂) : Set (radical ψ₂)) := by
  have hfac : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (radical ψ₁ ⊓ radical ψ₂) (radical ψ₂ ⊓ oppositeRadical ψ₁) (radical ψ₂) :=
    hs.second.mono le_rfl (inf_comm _ _).le
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [secondSubgroupProduct_eq]
    exact (sourceTargetCompactOpen Q (radical_isClosed ψ₂)).mul_mem hh hk
  · intro hx
    obtain ⟨a, ha, haQ, b, hb, hbQ, hab⟩ := hfac x.val x.property hx
    refine ⟨⟨⟨⟨a, ha.2⟩, Subgroup.mem_subgroupOf.mpr ha.1⟩,
      ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.mpr hb⟩⟩, ⟨haQ, hbQ⟩, ?_⟩
    rw [secondSubgroupProduct_eq]
    exact Subtype.ext hab.symm

omit [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- Restrict the first compact-open product to the middle intersection, using
the supplied factorization's inclusion of the first complement in the target. -/
theorem middle_localProduct_of_splitsAlong (hs : CommonLeviSplitting.SplitsAlong Q ψ₀ ψ₁) :
    D.intersectionSubgroupProduct ''
      ({h : ((radical ψ₀).subgroupOf (radical ψ₂)).subgroupOf
          ((radical ψ₁).subgroupOf (radical ψ₂)) |
          h.val ∈ sourceMiddleCompactOpen Q (radical_isClosed ψ₁) (radical_isClosed ψ₂)} ×ˢ
        (D.sourceNestedComplementCompactOpen Q (firstComplement_isClosed ψ₀ ψ₁) :
          Set (((radical ψ₁ ⊓ oppositeRadical ψ₀ :
            Subgroup (RationalPoint F G.X)).subgroupOf (radical ψ₂)).subgroupOf
              ((radical ψ₁).subgroupOf (radical ψ₂))))) =
      (sourceMiddleCompactOpen Q (radical_isClosed ψ₁) (radical_isClosed ψ₂) :
        Set ((radical ψ₁).subgroupOf (radical ψ₂))) := by
  have hfac : HasCompactOpenProduct (Q : Set (RationalPoint F G.X))
      (radical ψ₀ ⊓ radical ψ₁) (radical ψ₁ ⊓ oppositeRadical ψ₀) (radical ψ₁) :=
    hs.second.mono le_rfl (inf_comm _ _).le
  ext x
  constructor
  · rintro ⟨⟨h, k⟩, ⟨hh, hk⟩, rfl⟩
    rw [intersectionSubgroupProduct_eq]
    exact (sourceMiddleCompactOpen Q (radical_isClosed ψ₁)
      (radical_isClosed ψ₂)).mul_mem hh hk
  · intro hx
    obtain ⟨a, ha, haQ, b, hb, hbQ, hab⟩ :=
      hfac x.val.val (Subgroup.mem_subgroupOf.mp x.property) hx
    have hb₂ : b ∈ radical ψ₂ := D.first_le_target hb
    have ha₂ : a ∈ radical ψ₂ := by
      have heq : a = x.val.val * b⁻¹ := by rw [hab, mul_inv_cancel_right]
      rw [heq]
      exact (radical ψ₂).mul_mem x.val.property ((radical ψ₂).inv_mem hb₂)
    refine ⟨⟨⟨⟨⟨a, ha₂⟩, Subgroup.mem_subgroupOf.mpr ha.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ha.1)⟩,
      ⟨⟨⟨b, hb₂⟩, Subgroup.mem_subgroupOf.mpr hb.1⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hb)⟩⟩,
      ⟨haQ, hbQ⟩, ?_⟩
    rw [intersectionSubgroupProduct_eq]
    exact Subtype.ext (Subtype.ext hab.symm)

end Langlands.Plancherel.DynamicCommonLeviComposition.LocalProducts
