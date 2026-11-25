/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization

/-! # Evaluation of a normalized singleton comparison

Source: Stacks Project, Tag 03P2, singleton Čech term.
(blueprint: new-etale-singleton-tensor-normalization-evaluation) -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option linter.auxLemma false in
/-- Evaluating the sole outer Čech index gives an additive map whose value on
normalized pure tensors is the prescribed section. No affine hypothesis is needed.
Source: Stacks Project, Tag 03P2, affine Čech term identification.
(blueprint: new-etale-singleton-tensor-normalization-evaluation)

Proof: define q by the categorical product projection at the unique index
Fin(n+1) → Fin 1, followed by ULift.down. The projection is an additive homomorphism,
and ULift.down is an additive equivalence. Their composite is therefore additive.
Unfold IsSingletonTensorDegreeComparisonHom: its displayed equation is exactly
the asserted equation for q on pure tensors. The only Lean transport is unfolding
the degree-n Čech term and the lifted Amitsur term to expose their carriers.
This construction uses neither affineness, bijectivity nor tensor-generator
induction and applies to empty schemes and zero modules as well.
-/
theorem singletonTensor_normalization_evaluation
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∃ q : (singletonTensorCech X F U W g).X n →+
      Γ((Modules.tensorPullback (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).left.hom).obj F, ⊤),
      letI : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
      ∀ m b, q ((AddCommGrpCat.Hom.hom f) (ULift.up (m ⊗ₜ[Γ(U.left, ⊤)]
        PiTensorProduct.tprod Γ(U.left, ⊤) b))) =
        (∏ k : Fin (n + 1),
          (Pi.π (fun _ : Fin (n + 1) ↦ Over.mk g) k).left.left.appTop (b k)) •
            Modules.etaleTensorSectionsRestriction F
              (∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)).hom m := by
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
  let P := ∏ᶜ (fun _ : Fin (n + 1) ↦ Over.mk g)
  let N := Γ((Modules.tensorPullback P.left.hom).obj F, ⊤)
  let D : (Fin (n + 1) → Fin 1) → AddCommGrpCat.{u + 1} :=
    fun _ ↦ AddCommGrpCat.of (ULift.{u + 1} N)
  refine ⟨(AddEquiv.ulift : ULift.{u + 1} N ≃+ N).toAddMonoidHom.comp
    (Pi.π D (fun _ ↦ 0)).hom, ?_⟩
  let : Algebra Γ(U.left, ⊤) Γ(W.left, ⊤) := g.left.appTop.hom.toAlgebra
  intro m b
  exact hf m b


end
end AlgebraicGeometry.Scheme
