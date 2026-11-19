import Langlands.Representation.Plancherel.DynamicRepresentedInductionEvaluation
import Langlands.Representation.Intertwining.PQBoundaryVanishingCompactSupportProof
import Langlands.Representation.Plancherel.DynamicCommonLeviComplementProduct
import Langlands.Representation.Intertwining.PQCompositionHaarReduction

/-! # Integral-normalized composition for represented dynamic common-Levi triples -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition
open DynamicCommonLeviStructuralComparison

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  equalitySubgroupMeasurable equalitySubgroupBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ ψ₀ ψ₁ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G)
  (d₀ : ParabolicData χ ψ₀ T a) (d₁ : ParabolicData χ ψ₁ T a) (d₂ : ParabolicData χ ψ₂ T a)
  (b₀ : ParabolicData χ (Dynamic.inverseCocharacter ψ₀) T a)
  (b₁ : ParabolicData χ (Dynamic.inverseCocharacter ψ₁) T a)

/-- Represented induction from the original intrinsic Levi at a gallery vertex. -/
abbrev representedInduction (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) :=
  (leviInductionFunctor d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.radical
    d₀.r.isCompatible.levi (multiplication_isIso hG d₀)).obj σ

/-- Renard's complement for a pair of represented common-Levi parabolics. -/
abbrev representedComplement (sourceOpposite : ParabolicData χ ψ₀ T a)
    (target : ParabolicData χ ψ₁ T a) : Subgroup (rationalPoints G) :=
  pointImage (sourceOpposite.n ≫ sourceOpposite.p) ⊓ pointImage (target.n ≫ target.p)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem representedComplement_eq (sourceOpposite : ParabolicData χ ψ₀ T a)
    (target : ParabolicData χ ψ₁ T a) :
    representedComplement sourceOpposite target = radical ψ₀ ⊓ radical ψ₁ :=
  congrArg₂ (· ⊓ ·) (pointImage_radical sourceOpposite) (pointImage_radical target)

omit [LocallyOfFiniteType G.X.hom] in
theorem representedComplement_isClosed (sourceOpposite : ParabolicData χ ψ₀ T a)
    (target : ParabolicData χ ψ₁ T a) :
    IsClosed (representedComplement sourceOpposite target : Set (rationalPoints G)) :=
  (isClosed_pointImage_comp _ _ sourceOpposite.r.isCompatible.parabolic.isClosedSubgroup
    sourceOpposite.radical.1.isClosedSubgroup).inter
    (isClosed_pointImage_comp _ _ target.r.isCompatible.parabolic.isClosedSubgroup
      target.radical.1.isClosedSubgroup)

/-- Integral normalization at the chosen represented complement measure. -/
abbrev representedIsIntegralIntertwiner (measure : Measure (representedComplement b₀ d₁))
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (J : (representedInduction hG d₀ σ).representation.IntertwiningMap
      (representedInduction hG d₁ σ).representation) : Prop :=
  IsIntegralIntertwiner d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.radical
    d₀.r.isCompatible.levi (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.radical
    d₁.r.isCompatible.levi (multiplication_isIso hG d₁)
    (representedComplement b₀ d₁) measure σ J

/-- `PQ`-regularity for the two original represented vertices. -/
abbrev representedIsPQRegular (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) : Prop :=
  IsPQRegular d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.radical
    d₀.r.isCompatible.levi (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.radical
    d₁.r.isCompatible.levi (multiplication_isIso hG d₁) a σ

/-- The boundary condition at the identity double coset. -/
abbrev representedBoundaryVanishing
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) :
    Set (representedInduction hG d₀ σ) :=
  {f | f ∈ (boundaryVanishingSubfunctor d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.radical
      d₀.r.isCompatible.levi (multiplication_isIso hG d₀) d₁.p
      (identityParabolicDoubleCoset d₀.p d₁.p)).obj σ }

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The represented opposite parabolics intersect in the actual embedded Levi. -/
theorem pointImage_inter_dynamicOpposite (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ) :
    pointImage d₀.p ⊓ pointImage b₀.p = pointImage (d₀.l ≫ d₀.p) := by
  calc
    _ = parabolic ψ₀ ⊓ oppositeParabolic ψ₀ :=
      congrArg₂ (· ⊓ ·) (pointImage_parabolic d₀) (pointImage_parabolic b₀)
    _ = levi χ := congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      ((Dynamic.parabolic_inf_opposite_eq_centralizer ψ₀).trans h₀)
    _ = _ := (pointImage_levi d₀).symm

set_option maxHeartbeats 600000 in
/-- The represented boundary condition is compact support on the complement. -/
theorem representedBoundaryVanishing_iff
    (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ)
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (f : representedInduction hG d₀ σ) :
    f ∈ representedBoundaryVanishing hG d₀ d₁ σ ↔
      ∃ C : Set (representedComplement b₀ d₁), IsCompact C ∧
        ∀ x : representedComplement b₀ d₁, x ∉ C → eval _ _ f x.val = 0 :=
  pqBoundaryVanishingCompactSupport.{u, uV} F G hG
    d₀.P (parameterScheme χ) d₀.U d₁.P d₁.U b₀.P b₀.U
    d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.r.isCompatible.levi d₀.radical
    (multiplication_isIso hG d₀)
    d₁.p d₁.l d₁.n d₁.r.isCompatible.parabolic d₁.r.isCompatible.levi d₁.radical
    (multiplication_isIso hG d₁)
    b₀.p b₀.l b₀.n b₀.r.isCompatible.parabolic b₀.r.isCompatible.levi b₀.radical
    (multiplication_isIso hG b₀) (d₀.levi_comp.trans d₁.levi_comp.symm)
    (b₀.levi_comp.trans d₀.levi_comp.symm) (pointImage_inter_dynamicOpposite d₀ b₀ h₀) σ f

section Composition

variable (h₀ : Dynamic.centralizer ψ₀ = Dynamic.centralizer χ)
  (h₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer χ)
  (h₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer χ)
  (hd : IsDistanceAdditive ψ₀ ψ₁ ψ₂) (ha : IsSplitComponent a)

local notation "V₀₁" => representedComplement b₀ d₁
local notation "V₁₂" => representedComplement b₁ d₂
local notation "V₀₂" => representedComplement b₀ d₂

variable (μ₀₁ : Measure (representedComplement b₀ d₁))
  (μ₁₂ : Measure (representedComplement b₁ d₂)) (μ₀₂ : Measure (representedComplement b₀ d₂))
  [μ₀₁.IsHaarMeasure] [μ₁₂.IsHaarMeasure] [μ₀₂.IsHaarMeasure]

include h₀ h₁ h₂ hd ha in
set_option maxHeartbeats 1200000 in
/-- At fixed Haar measures, integral-normalized composition on a
distance-additive triple agrees with the direct map up to a positive
parameter-independent factor. -/
theorem exists_representedIntegralIntertwiner_comp_smul :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
        (J₀₁ : (representedInduction hG d₀ σ).representation.IntertwiningMap
          (representedInduction hG d₁ σ).representation)
        (J₁₂ : (representedInduction hG d₁ σ).representation.IntertwiningMap
          (representedInduction hG d₂ σ).representation)
        (J₀₂ : (representedInduction hG d₀ σ).representation.IntertwiningMap
          (representedInduction hG d₂ σ).representation),
        representedIsPQRegular hG d₀ d₂ σ →
        representedIsIntegralIntertwiner hG d₀ d₁ b₀ μ₀₁ σ J₀₁ →
        representedIsIntegralIntertwiner hG d₁ d₂ b₁ μ₁₂ σ J₁₂ →
        representedIsIntegralIntertwiner hG d₀ d₂ b₀ μ₀₂ σ J₀₂ →
        J₁₂.comp J₀₁ = (c : ℂ) • J₀₂ := by
  let : Smooth G.X.hom := hG.smooth
  let e := subgroupProductChartOfEq (representedComplement_eq b₀ d₁)
    (representedComplement_eq b₁ d₂) (representedComplement_eq b₀ d₂)
    (oppositeComplementProduct ψ₀ ψ₁ ψ₂ (h₁.trans h₀.symm) (h₂.trans h₀.symm) hd)
    (oppositeComplementProduct_apply ψ₀ ψ₁ ψ₂ (h₁.trans h₀.symm) (h₂.trans h₀.symm) hd)
  have hClosed₀₁ := representedComplement_isClosed b₀ d₁
  have hClosed₁₂ := representedComplement_isClosed b₁ d₂
  have hClosed₀₂ := representedComplement_isClosed b₀ d₂
  have hRadical := isLimitOfCompactSubgroups_pointImage_radical d₂.p d₂.n
    d₂.r.isCompatible.parabolic.isClosedSubgroup d₂.radical.1
  obtain ⟨compatibleMeasure, hHaar, hCompatible⟩ := exists_compatible_haar_of_mul_homeomorph
    hClosed₀₁ hClosed₁₂ hClosed₀₂
    (forall_isCompact_subgroup_of_le hRadical inf_le_right hClosed₁₂)
    (forall_isCompact_subgroup_of_le hRadical inf_le_right hClosed₀₂)
    e.val e.property μ₀₁ μ₁₂
  let : LocallyCompactSpace V₀₂ := hClosed₀₂.locallyCompactSpace
  let : SecondCountableTopology V₀₂ :=
    TopologicalSpace.Subtype.secondCountableTopology (V₀₂ : Set (rationalPoints G))
  let c := Measure.haarScalarFactor compatibleMeasure μ₀₂
  have hμ : compatibleMeasure = c • μ₀₂ := Measure.isMulLeftInvariant_eq_smul compatibleMeasure μ₀₂
  refine ⟨c, Measure.haarScalarFactor_pos_of_isHaarMeasure compatibleMeasure μ₀₂, ?_⟩
  intro σ J₀₁ J₁₂ J₀₂ hreg hJ₀₁ hJ₁₂ hJ₀₂
  let I₀ := representedInduction hG d₀ σ
  let I₁ := representedInduction hG d₁ σ
  let I₂ := representedInduction hG d₂ σ
  let E₀ : I₀ → rationalPoints G → σ := eval _ _
  let E₁ : I₁ → rationalPoints G → σ := eval _ _
  let E₂ : I₂ → rationalPoints G → σ := eval _ _
  let F₀₁ := representedBoundaryVanishing hG d₀ d₁ σ
  let F₁₂ := representedBoundaryVanishing hG d₁ d₂ σ
  let F₀₂ := representedBoundaryVanishing hG d₀ d₂ σ
  apply pqIntertwiner_eq_of_eval_one.{u, uV} F G hG
    d₀.P (parameterScheme χ) d₀.U d₂.P d₂.U
    d₀.p d₀.l d₀.n d₀.r.isCompatible.parabolic d₀.r.isCompatible.levi d₀.radical
    (multiplication_isIso hG d₀)
    d₂.p d₂.l d₂.n d₂.r.isCompatible.parabolic d₂.r.isCompatible.levi d₂.radical
    (multiplication_isIso hG d₂) T a ha σ hreg
  refine @eval_one_comp_eq_of_integral_formulas (rationalPoints G) _ _ _ _
    σ I₀ I₁ I₂ σ.obj.hV1 σ.obj.hV2 I₀.obj.hV1 I₀.obj.hV2 I₁.obj.hV1 I₁.obj.hV2
    I₂.obj.hV1 I₂.obj.hV2 I₀.representation I₁.representation I₂.representation E₀ E₁ E₂ (fun _ _ _ => rfl) (fun _ _ _ => rfl) I₀.property
    V₀₁ V₁₂ V₀₂ _ _ _ μ₀₁ μ₁₂ compatibleMeasure F₀₁ F₀₂ F₁₂
    (fun f => (representedBoundaryVanishing_iff hG d₀ d₁ b₀ h₀ σ f).mpr)
    (fun f => (representedBoundaryVanishing_iff hG d₁ d₂ b₁ h₁ σ f).mpr)
    (fun f => (representedBoundaryVanishing_iff hG d₀ d₂ b₀ h₀ σ f).mp)
    e.val e.property hCompatible J₀₁ J₁₂ ((c : ℂ) • J₀₂)
    (fun f hf ℓ => (hJ₀₁ f hf ℓ).2) (fun f hf ℓ => (hJ₁₂ f hf ℓ).2) ?_
  intro f hf ℓ
  calc
    ℓ (E₂ (((c : ℂ) • J₀₂) f) 1) = (c : ℂ) • ℓ (E₂ (J₀₂ f) 1) := map_smul ℓ _ _
    _ = (c : ℂ) • (∫ x : V₀₂, ℓ (E₀ f x.val) ∂μ₀₂) :=
      congrArg ((c : ℂ) • ·) (hJ₀₂ f hf ℓ).2
    _ = ∫ x : V₀₂, ℓ (E₀ f x.val) ∂compatibleMeasure := by
      rw [hμ, integral_smul_nnreal_measure]
      rfl

end Composition

end Langlands.Plancherel.DynamicCommonLeviPresentations
