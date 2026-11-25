/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorCoherence
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionSpecifiedHomNaturality
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionEvaluationPreservation

/-! # Coherent underived restriction on a specified action site

Source: the normalized tensor and evaluation formulas of the twisted action-site
presentation; Stacks 03EK, 03EL and 03EO. No native or derived category occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

attribute [local irreducible] SheafOfModules.monoidalCategory sigma
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

/-- The specified action-site tensor and Hom maps satisfy all underived coherence
and evaluation equations.

Source: twisted action-site presentation, tensor/Hom steps 9--13; Stacks 03EK,
03EL and 03EO; native ringed bridge step 2.
(blueprint: lem-sf-twisted-action-underived-restriction).

Proof: assemble P.tensor and P.hom into natural isomorphisms by
NatIso.ofComponents, using P.tensor_naturality and P.hom_naturality, and take
P.unit. To prove associativity,
precompose by the two inverse tensor comparisons. Maps from a triple sheaf
tensor are determined by local pure triples, by the sheafification adjunction
and sectionwise tensor induction. Apply P.tensor_pure twice and the ordinary
pure-triple associator formula: both composites send (x tensor y) tensor z to
x tensor (y tensor z). For the left and right unit laws use the same local
pure-tensor criterion, P.unit_sections and the coefficient restriction ring
isomorphism. Both paths multiply the module section by that coefficient.
Symmetry is P.symmetry. The canonical right evaluation is the braiding followed
by the left evaluationMap. Its pure-tensor formula characterizes it uniquely by
the same sheafification adjunction. Substitute P.evaluation and P.symmetry;
tensor naturality moves the Hom comparison through the braiding and gives the
required right evaluation square. These calculations include zero modules,
empty sites and zero coefficient rings. The construction uses a specified P
and asserts no existence of a site or any native Frobenius realization. -/
theorem underived_restriction (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∃ d : RingedForgetTensorTransposition.Underived.{u, u, u, u, u, u}
        P.topology P.coefficient J R U,
      ∀ M N : Modules P.coefficient,
        d.hom.hom.app (op M, N) = (P.hom M N).hom := by
  cases ‹s.functor.IsContinuous J J›
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  obtain ⟨τ, ⟨c⟩, hτ⟩ := tensor_coherence P
  obtain ⟨H, hH⟩ := hom_comparison P
  refine ⟨{ tensor := τ, hom := H, coherence := c, evaluation := ?_ }, hH⟩
  intro M N eB eA hB hA
  simp only [hτ, hH]
  exact specified_evaluation_square P M N eB eA hB hA

end CategoryTheory.TwistedActionRingedSite
