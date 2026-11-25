/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Canonical evaluation of normalized pure tensors

Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-singleton-tensor-pure-image) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option linter.auxLemma false in
/-- Canonical evaluation sends a lifted pure tensor to its normalized pure section.
Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-singleton-tensor-pure-image)

Proof: unfold the normalization predicate. The finite scheme product and the outer
additive-group product use the same diagrams as in that predicate. Their limit
witnesses are proofs of the same propositions, hence agree by proof irrelevance.
The composite q first projects onto the sole outer index and then applies ULift.down.
Evaluating q.comp f.hom on the displayed lifted tensor therefore gives exactly the
left side of the normalization equation. That equation gives the asserted product
of projection pullbacks times the restricted coefficient. No affineness is used.
For n=0 the diagram still has one factor; zero coefficients, zero functions and empty
schemes require no division or nonzero hypothesis.
-/
theorem singletonTensorDegreeComparisonHom_pure_image
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
    let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
    let N := Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)
    let D : (Fin (n + 1) → Fin 1) → AddCommGrpCat.{u + 1} :=
      fun _ ↦ AddCommGrpCat.of (ULift.{u + 1} N)
    let q : (singletonTensorCech X F U W g).X n →+ N :=
      (AddEquiv.ulift : ULift.{u + 1} N ≃+ N).toAddMonoidHom.comp
        (Pi.π D (fun _ ↦ 0)).hom
    ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤))
      (b : Fin (n + 1) → Γ(W.left, ⊤)),
      (q.comp f.hom) (ULift.up.{u + 1, u}
        (m ⊗ₜ[Γ(U.left, ⊤)] PiTensorProduct.tprod Γ(U.left, ⊤) b)) =
        (∏ k : Fin (n + 1),
          (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)) •
            Modules.etaleTensorSectionsRestriction F P.hom m := by
  -- Transport the product witness by proof irrelevance inside the proof only.
  -- This keeps the theorem signature on the library's usual limit instances.
  run_tac do
    let args ← #[`X, `U, `W, `g, `n].mapM fun name ↦ do
      return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
    let hPred ← Lean.Meta.mkAppM ``IsSingletonTensorDegreeComparison._proof_1 args
    let hType ← Lean.Meta.inferType hPred
    let hStd ← Lean.Meta.synthInstance hType
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let motive ← Lean.Meta.withLocalDeclD `h hType fun h ↦ do
      let normalized := target.replace fun e ↦ if e == hStd then some h else none
      if normalized == target then throwError "The product witness was not found"
      Lean.Meta.mkLambdaFVars #[h] normalized
    let eq ← Lean.Meta.mkAppM ``Subsingleton.elim #[hPred, hStd]
    let propEq ← Lean.Meta.mkAppM ``congrArg #[motive, eq]
    let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (Lean.mkApp motive hPred)
    goal.assign (Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
      #[Lean.mkApp motive hPred, Lean.mkApp motive hStd, propEq, next])
    Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
  let := IsSingletonTensorDegreeComparison._proof_1 X U W g n
  let := IsSingletonTensorDegreeComparison._proof_2 X F U W g n
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  intro m b
  exact hf m b

end
end AlgebraicGeometry.Scheme
