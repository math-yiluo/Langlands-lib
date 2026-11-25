/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraPullbackData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjNormalizedDescent
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjQuotientPullbackComparison
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent

/-!
# Open restriction of the normalized symmetric Proj quotient

Source: Stacks Project, Constructions, Tags 01NR, 01NQ and 01OB.
(blueprint: lem-trf-symmetric-proj-open-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

-- Match the finite-limit instance used by the normalized quotient definitions.
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.GradedAlgebraData.relProjHom
  ProjectiveBundleQuotientGeometry.HasOpenCompatibility

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Open restriction of the normalized symmetric Proj quotient.

Source: Stacks Project, Constructions, Tags 01NR, 01NQ and 01OB.
(blueprint: lem-trf-symmetric-proj-open-comparison).

Proof: For an open V, tensor pullback preserves quasi-coherence and normalized
descent supplies a quotient DV over V. The normalized pullback unit and affine
tensor-section identification induce coefficientwise pullback data for the
symmetric graded algebras; symmetric algebra base change proves its degreewise
base-change property. The relative-Proj base-change theorem then supplies j and
its pullback square. The fixed-comparison quotient-line theorem supplies w by
matching degree-one frames and their transition ratios on the corresponding
charts, and gives the exact quotient equation. These witnesses are precisely
HasOpenCompatibility D. The argument includes nonaffine and empty V. -/
theorem open_compatibility_of_normalized_quotient (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) :
    ProjectiveBundleQuotientGeometry.HasOpenCompatibility D := by
  unfold ProjectiveBundleQuotientGeometry.HasOpenCompatibility
  intro V
  have hE := Scheme.Modules.isQuasicoherent_tensorPullback V.ι E
  refine ⟨hE, ?_⟩
  obtain ⟨DV, _⟩ := @exists_normalized_quotient_with_affine_restriction V.toScheme
    ((Scheme.Modules.tensorPullback V.ι).obj E) hE
  refine ⟨DV, ?_⟩
  obtain ⟨b, hb⟩ := @SymmetricAlgebraSheaf.exists_normalized_pullbackData V.toScheme S V.ι E
    ‹E.IsQuasicoherent› hE
  refine ⟨b.relProjComparison, b.isPullback, ?_⟩
  -- Reuse the transport proof in the predicate, avoiding reduction of its auxiliary proof.
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let transport := (target.find? (fun t ↦
      t.isAppOfArity ``CategoryTheory.eqToIso 5)).getD target
    if !transport.isAppOfArity ``CategoryTheory.eqToIso 5 then
      throwError "expected the quotient transport isomorphism"
    let loc (n : Lean.Name) : Lean.MetaM Lean.Expr := do
      return Lean.mkFVar (← Lean.Meta.getLocalDeclFromUserName n).fvarId
    let v ← loc `V
    let s ← loc `S
    let moduleE ← loc `E
    let d ← loc `D
    let dv ← loc `DV
    let coefficientData ← loc `b
    let generators ← loc `hb
    let qc ← loc `hE
    let sourceQC := (← Lean.Meta.inferType d).appArg!
    let x ← Lean.Meta.mkAppM ``Scheme.Opens.toScheme #[v]
    let g ← Lean.Meta.mkAppM ``Scheme.Opens.ι #[v]
    let proof ← Lean.Meta.mkAppOptM ``quotient_comparison_of_normalized_pullbackData
      #[some x, some s, some g, some moduleE, some sourceQC, some qc,
        some d, some dv, some coefficientData, some generators, some transport.appArg!]
    Lean.Elab.Tactic.closeMainGoal `exact proof

end AlgebraicGeometry.SymmetricProjTautologicalCharts
