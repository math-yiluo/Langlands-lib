import Langlands.Automorphic.GroupSchemeConstantTerm

/-! # Convergence, invariance and vanishing spaces for actual subgroup constant terms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (U : GroupScheme.SubgroupFunctor G)

/-- Multiplication on the left of the ambient argument is positive right translation
of the variable on the actual subgroup rational quotient. -/
theorem constantTermIntegrand_subgroup_mul (f : ContinuousRationalFunctions F G)
    (n : AdelicSubgroupPoints.adelicPoints F G U) (g : AdelicGroupPoints F G) :
    constantTermIntegrand F G U f ((n : AdelicGroupPoints F G) * g) =
      constantTermIntegrand F G U f g ∘
        LeftCosetSpace.rightTranslate (AdelicSubgroupPoints.rationalSubgroup F G U) n := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x => exact congrArg (evaluate F G f) (mul_assoc _ _ _).symm

variable [MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
  (mu : Measure (AdelicSubgroupPoints.RationalQuotient F G U))

/-- For a Borel quotient, preservation of the supplied measure by the actual quotient
translation implies left invariance under that subgroup element. -/
theorem constantTerm_subgroup_mul
    [BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    (f : ContinuousRationalFunctions F G)
    (n : AdelicSubgroupPoints.adelicPoints F G U)
    (hn : MeasurePreserving
      (LeftCosetSpace.rightTranslate (AdelicSubgroupPoints.rationalSubgroup F G U) n) mu mu)
    (g : AdelicGroupPoints F G) :
    constantTerm F G U mu f ((n : AdelicGroupPoints F G) * g) =
      constantTerm F G U mu f g := by
  unfold constantTerm
  rw [constantTermIntegrand_subgroup_mul]
  exact hn.integral_comp
    (LeftCosetSpace.rightTranslateHomeomorph
      (AdelicSubgroupPoints.rationalSubgroup F G U) n).measurableEmbedding _

/-- Convergence together with vanishing at every actual ambient adelic argument. -/
def HasVanishingConstantTerm (f : ContinuousRationalFunctions F G) : Prop :=
  HasConvergentConstantTerm F G U mu f ∧
    ∀ g : AdelicGroupPoints F G, constantTerm F G U mu f g = 0

/-- The actual convergent zero-constant-term functions inside the original continuous
representation, without a parabolic-enumeration or compactness assertion. -/
def vanishingConstantTermSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule :=
    { carrier := {f | HasVanishingConstantTerm F G U mu f}
      zero_mem' := by
        exact ⟨(convergentConstantTermSubrepresentation F G U mu).toSubmodule.zero_mem,
          constantTerm_zero F G U mu⟩
      add_mem' := by
        intro f h hf hh
        refine ⟨(convergentConstantTermSubrepresentation F G U mu).toSubmodule.add_mem
          hf.1 hh.1, ?_⟩
        intro g
        rw [constantTerm_add F G U mu f h hf.1 hh.1 g, hf.2 g, hh.2 g, add_zero]
      smul_mem' := by
        intro c f hf
        refine ⟨(convergentConstantTermSubrepresentation F G U mu).toSubmodule.smul_mem
          c hf.1, ?_⟩
        intro g
        rw [constantTerm_smul, hf.2 g, smul_zero] }
  apply_mem_toSubmodule h f hf := by
    refine ⟨(convergentConstantTermSubrepresentation F G U mu).apply_mem_toSubmodule
      h hf.1, ?_⟩
    intro g
    rw [constantTerm_rightAction]
    exact hf.2 (g * h)

@[simp]
theorem mem_vanishingConstantTermSubrepresentation (f : ContinuousRationalFunctions F G) :
    f ∈ vanishingConstantTermSubrepresentation F G U mu ↔
      HasConvergentConstantTerm F G U mu f ∧
        ∀ g : AdelicGroupPoints F G, constantTerm F G U mu f g = 0 := Iff.rfl

theorem vanishingConstantTerm_le_convergent :
    vanishingConstantTermSubrepresentation F G U mu ≤
      convergentConstantTermSubrepresentation F G U mu :=
  fun _ hf => hf.1

/-- The kernel of the genuinely linear integral operator is a subrepresentation
of its actual convergence domain. -/
def constantTermKernelSubrepresentation :
    Subrepresentation (convergentConstantTermRightAction F G U mu) where
  toSubmodule := (constantTermLinearMap F G U mu).ker
  apply_mem_toSubmodule h f hf := by
    change constantTermLinearMap F G U mu _ = 0
    change constantTermLinearMap F G U mu f = 0 at hf
    funext g
    rw [constantTermLinearMap_rightAction]
    exact congrFun hf (g * h)

@[simp]
theorem mem_constantTermKernelSubrepresentation (f : ConvergentConstantTermFunctions F G U mu) :
    f ∈ constantTermKernelSubrepresentation F G U mu ↔
      (f.val : ContinuousRationalFunctions F G) ∈
        vanishingConstantTermSubrepresentation F G U mu := by
  change constantTermLinearMap F G U mu f = 0 ↔
    HasConvergentConstantTerm F G U mu f.val ∧
      ∀ g, constantTerm F G U mu f.val g = 0
  constructor
  · intro hf
    exact ⟨f.property, fun g => congrFun hf g⟩
  · intro hf
    funext g
    exact hf.2 g

section Compact

variable [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
  [BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U)] [IsFiniteMeasure mu]

/-- On the actual quotient, compactness and a finite Borel measure imply convergence
of every continuous integrand. These analytic hypotheses are not constructed here. -/
theorem hasConvergentConstantTerm_of_compact (f : ContinuousRationalFunctions F G) :
    HasConvergentConstantTerm F G U mu f := by
  intro g
  exact (continuous_constantTermIntegrand F G U f g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- With the explicit compact finite-measure hypotheses, the constant term is linear
on the entire original continuous rational-invariant function space. -/
def compactConstantTermLinearMap :
    ContinuousRationalFunctions F G →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun := constantTerm F G U mu
  map_add' f h := by
    funext g
    exact constantTerm_add F G U mu f h
      (hasConvergentConstantTerm_of_compact F G U mu f)
      (hasConvergentConstantTerm_of_compact F G U mu h) g
  map_smul' c f := by
    funext g
    exact constantTerm_smul F G U mu c f g

theorem compactConstantTermLinearMap_rightAction (f : ContinuousRationalFunctions F G)
    (h g : AdelicGroupPoints F G) :
    compactConstantTermLinearMap F G U mu (continuousRightAction F G h f) g =
      compactConstantTermLinearMap F G U mu f (g * h) :=
  constantTerm_rightAction F G U mu f h g

theorem mem_vanishingConstantTermSubrepresentation_of_compact
    (f : ContinuousRationalFunctions F G) :
    f ∈ vanishingConstantTermSubrepresentation F G U mu ↔
      ∀ g : AdelicGroupPoints F G, constantTerm F G U mu f g = 0 := by
  exact ⟨fun hf => hf.2,
    fun hf => ⟨hasConvergentConstantTerm_of_compact F G U mu f, hf⟩⟩

end Compact

section Family

variable {Index : Type v} (Us : Index → GroupScheme.SubgroupFunctor G)
  [∀ i, MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G (Us i))]
  (mus : ∀ i, Measure (AdelicSubgroupPoints.RationalQuotient F G (Us i)))

/-- Intersection of the convergent vanishing spaces for the supplied actual subgroup
family. No assertion identifies this family with all rational parabolics. -/
def familyVanishingConstantTermSubrepresentation :
    Subrepresentation (continuousRightAction F G) where
  toSubmodule := ⨅ i, (vanishingConstantTermSubrepresentation F G (Us i) (mus i)).toSubmodule
  apply_mem_toSubmodule h f hf := by
    simp only [Submodule.mem_iInf] at hf ⊢
    intro i
    exact (vanishingConstantTermSubrepresentation F G (Us i) (mus i)).apply_mem_toSubmodule
      h (hf i)

@[simp]
theorem mem_familyVanishingConstantTermSubrepresentation (f : ContinuousRationalFunctions F G) :
    f ∈ familyVanishingConstantTermSubrepresentation F G Us mus ↔
      ∀ i, HasConvergentConstantTerm F G (Us i) (mus i) f ∧
        ∀ g : AdelicGroupPoints F G, constantTerm F G (Us i) (mus i) f g = 0 := by
  change f ∈ (⨅ i,
    (vanishingConstantTermSubrepresentation F G (Us i) (mus i)).toSubmodule) ↔ _
  simp only [Submodule.mem_iInf]
  rfl

end Family

end Langlands.Automorphic.GroupSchemeFunctions
