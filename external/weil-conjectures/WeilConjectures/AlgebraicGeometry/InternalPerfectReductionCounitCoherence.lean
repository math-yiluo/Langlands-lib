/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomEquiv
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.CounitComposition.InternalScalarExtensionCounitComposition
public import WeilConjectures.Tactic.ExactModProofs
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Homotopy-level counit coherence for the perfect reduction tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem quotient_obj_eq {C : Type*} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      DerivedCategory.Q.obj P := rfl

private meta def quotientObjectComparison? (a : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let args := a.getAppArgs
  unless a.getAppFn.isConstOf ``Functor.obj && args.size ≥ 2 do return none
  let F := args[args.size - 2]!
  let X := args.back!
  unless F.getAppFn.isConstOf ``DerivedCategory.Qh && F.getAppArgs.size == 4 do
    return none
  let xs := X.getAppArgs
  unless X.getAppFn.isConstOf ``Functor.obj && xs.size ≥ 2 do return none
  unless xs[xs.size - 2]!.getAppFn.isConstOf ``HomotopyCategory.quotient do return none
  let h ← Lean.Meta.mkAppOptM ``quotient_obj_eq
    ((F.getAppArgs.map some).push (some xs.back!))
  let eqArgs := (← Lean.Meta.inferType h).getAppArgs
  return some (eqArgs[1]!, eqArgs[2]!, ← Lean.Meta.mkHEqOfEq h)

private meta partial def zetaCounitHead (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .letE _ _ value body _ => zetaCounitHead (body.instantiate1 value)
  | .mdata _ body => zetaCounitHead body
  | _ => e.headBeta

-- Explicit heterogeneous congruence keeps the kernel from unfolding large derived functors.
-- Every leaf is either proof irrelevance or a separately kernel-checked reflexivity lemma.
-- No definitional equality is trusted without a proof term checked by the kernel.

private meta partial def certifyCounitAliases (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if a == b then return ← Lean.Meta.mkHEqRefl a
  if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
  let qa ← quotientObjectComparison? a
  let qb ← quotientObjectComparison? b
  match qa, qb with
  | some (a₀, a', e), none =>
    let p₀ ← certifyCounitAliases a a₀
    let p₁ ← certifyCounitAliases a' b
    return ← Lean.Meta.mkAppM ``HEq.trans
      #[← Lean.Meta.mkAppM ``HEq.trans #[p₀, e], p₁]
  | none, some (b₀, b', e) =>
    let p₀ ← certifyCounitAliases b b₀
    let p₁ ← certifyCounitAliases a b'
    let p₂ ← Lean.Meta.mkAppM ``HEq.trans #[p₀, e]
    return ← Lean.Meta.mkAppM ``HEq.trans #[p₁, ← Lean.Meta.mkAppM ``HEq.symm #[p₂]]
  | _, _ => pure ()
  let fa := a.getAppFn
  let fb := b.getAppFn
  let aa := a.getAppArgs
  let bb := b.getAppArgs
  if fa == fb && !aa.isEmpty && aa.size == bb.size then
    try
      let c ← Lean.Meta.mkHCongrWithArity fa aa.size
      let mut args := #[]
      for i in [:aa.size] do
        let p ← certifyCounitAliases aa[i]! bb[i]!
        let p ← match c.argKinds[i]! with
          | .eq => Lean.Meta.mkEqOfHEq p
          | .heq => pure p
          | _ => throwError "Unexpected congruence kind"
        args := args ++ #[aa[i]!, bb[i]!, p]
      let p := Lean.mkAppN c.proof args
      if (← Lean.Meta.inferType p).isAppOf ``Eq then
        return ← Lean.Meta.mkHEqOfEq p
      return p
    catch _ => pure ()
  let modelAliases := [``internalPerfectIntegralComplex, ``internalPerfectScalarModel]
  if let .const n _ := fa then
    if modelAliases.contains n then
      if let some a' ← Lean.Meta.unfoldDefinition? a then
        return ← certifyCounitAliases (zetaCounitHead a') b
  if let .const n _ := fb then
    if modelAliases.contains n then
      if let some b' ← Lean.Meta.unfoldDefinition? b then
        return ← certifyCounitAliases a (zetaCounitHead b')
  unless ← Lean.Meta.isDefEq a b do
    throwError "Not definitionally equal: {a} and {b}"
  Lean.Meta.mkAuxTheorem (← Lean.Meta.mkHEq a b) (← Lean.Meta.mkHEqRefl a)
    (zetaDelta := true) (kind? := `_counitAlias)

private meta def exactCertifiedCounit (stx : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Elab.Term.elabTerm stx none
    let H := ExactModProofs.stripMData (← Lean.Meta.whnf (← Lean.Meta.inferType h))
    let g ← Lean.Elab.Tactic.getMainGoal
    let G := ExactModProofs.stripMData (← g.getType)
    let p ← certifyCounitAliases H G
    let e ← Lean.Meta.mkEqOfHEq p
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[e, h])
    Lean.Elab.Tactic.replaceMainGoal []

private theorem restrictComp_eq (W : Scheme.{u}) (n : ℕ) :
    AdicCompletion.restrictComp l E W n =
      Mod.mapDerivedCategoryComapCompIso _ _ _
        (AdicCompletion.quotient_transition l E W n) := by
  rfl

private theorem reductionComp_eq (W : Scheme.{u}) (n : ℕ) :
    AdicCompletion.reductionComp l E W n =
      (((Mod.derivedExtendMapDerivedCategoryAdjunction
        (AdicCompletion.quotient l E W (n + 1))).comp
          (Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.transition l E W n))).ofNatIsoRight
              (Mod.mapDerivedCategoryComapCompIso _ _ _
                (AdicCompletion.quotient_transition l E W n))).leftAdjointUniq
                  (Mod.derivedExtendMapDerivedCategoryAdjunction
                    (AdicCompletion.quotient l E W n)) := by
  have he := restrictComp_eq l E W n
  exact congrArg (fun e ↦
    (((Mod.derivedExtendMapDerivedCategoryAdjunction
      (AdicCompletion.quotient l E W (n + 1))).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.transition l E W n))).ofNatIsoRight e).leftAdjointUniq
            (Mod.derivedExtendMapDerivedCategoryAdjunction
              (AdicCompletion.quotient l E W n))) he

private theorem reductionComp_counit_chain (W : Scheme.{u})
    (I : CochainComplex (AdicCompletion.Modules l E W) ℤ) (n : ℕ) :
    let φ := AdicCompletion.quotient l E W (n + 1)
    let ψ := AdicCompletion.transition l E W n
    let χ := AdicCompletion.quotient l E W n
    let α₀ := (Mod.extendScalarsComp φ ψ).symm ≪≫
      eqToIso (by congr 1; exact AdicCompletion.quotient_transition l E W n)
    (AdicCompletion.reductionComp l E W n).hom.app (DerivedCategory.Q.obj I) ≫
        (Mod.extendScalars χ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I) =
      (Mod.extendScalars ψ).leftDerivedFunctor.map
          ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ≫
        (Mod.extendScalars ψ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj I)) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso α₀ (.up ℤ)).hom.app I) := by
  dsimp only
  have hc := Mod.CounitComposition.derivedExtendScalars_comp_counit
    (φ := AdicCompletion.quotient l E W (n + 1))
    (ψ := AdicCompletion.transition l E W n)
    (χ := AdicCompletion.quotient l E W n)
    (AdicCompletion.quotient_transition l E W n) I
  rw [reductionComp_eq l E W n]
  dsimp only at hc
  run_tac exactCertifiedCounit (Lean.mkIdent `hc)

/-- Homotopy-level specialization of the scalar-extension counit composition square.

Source: `lem-pe-internal-scalar-extension-counit-composition` together with the
comparison definition `def-pe-internal-perfect-reduction-hom-equiv`.
(blueprint: lem-pe-internal-perfect-reduction-counit-coherence).

Proof: unfold the ordinary reduction step and the derived reduction comparison,
then apply the generic counit composition identity to the two quotient maps.
The remaining conversion from the chain quotient to the homotopy quotient is the
canonical quotient comparison naturality. This statement is strictly below the
homotopy comparison theorem: it contains no endomorphism or localization data. -/
theorem internalPerfectReduction_counit_coherence
    (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    let F := Mod.extendScalars (AdicCompletion.transition l E W n)
    let T := internalPerfectScalarModel l E W P
    let α := AdicCompletion.reductionComp l E W n
    let γ := internalPerfectReductionOrdinaryIso l E W P a b ha hb hfree
    let ε := F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (internalPerfectOrdinaryReduction l E W P (n + 1)))
    let H := HomotopyCategory.quotient
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (AdicCompletion.finiteRing l E W n)) (.up ℤ)
    let a₀ := internalPerfectOrdinaryReductionStep l E W P n
    let δ := ε ≫ DerivedCategory.Qh.map (H.map a₀.hom)
    α.hom.app T ≫ (γ n).hom = F.leftDerivedFunctor.map (γ (n + 1)).hom ≫ δ := by
  have hγ (k : ℕ) :
      (internalPerfectReductionOrdinaryIso l E W P a b ha hb hfree k).hom =
        (Mod.extendScalars (AdicCompletion.quotient l E W k)).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (internalPerfectIntegralComplex l E W P)) := by
    as_aux_lemma =>
      dsimp only [internalPerfectReductionOrdinaryIso, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Category.assoc]
      have hi : ((DerivedCategory.quotientCompQhIso
          (AdicCompletion.Modules l E W)).app
            (internalPerfectIntegralComplex l E W P)).inv = 𝟙 _ := rfl
      simp only [hi]
      let L := AdicCompletion.derivedReduction l E W k
      change L.map (𝟙 _) ≫ _ = _
      rw [L.map_id]
      exact Category.id_comp _
  have hstep :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (.up ℤ)).map
            (internalPerfectOrdinaryReductionStep l E W P n).hom) =
        DerivedCategory.Q.map (internalPerfectOrdinaryReductionStep l E W P n).hom := by
    as_aux_lemma =>
      have h := DerivedCategory.quotientCompQhIso_hom_naturality
        (internalPerfectOrdinaryReductionStep l E W P n).hom
      dsimp only [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom] at h
      erw [Category.comp_id, Category.id_comp] at h
      simpa only [internalPerfectOrdinaryReductionStep] using h
  dsimp only
  rw [hγ n, hγ (n + 1)]
  rw [hstep]
  as_aux_lemma =>
    have hs := reductionComp_counit_chain l E W
      (internalPerfectIntegralComplex l E W P) n
    dsimp only [internalPerfectOrdinaryReduction, internalPerfectOrdinaryReductionStep,
      internalPerfectScalarModel, Functor.comp_obj, Functor.mapHomotopyCategory_obj,
      HomotopyCategory.quotient_obj_as, Iso.app_hom, Category.assoc]
    run_tac exactCertifiedCounit (Lean.mkIdent `hs)

end AlgebraicGeometry.ProEtale
