/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluationIndex
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedComposition
import WeilConjectures.CategoryTheory.SmoothPurity.AdjunctionEvaluationComposition
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionCoherence
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequenceTransition
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequenceEvaluationComposition

/-! # Composition of derived subsequence extensions

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J))
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r s : ℕ ↪o ℕ)

/-- Evaluating composition of derived subsequence extensions gives the canonical
scalar associator at the actual first composite selected index. Source: Zheng 4.1
and its subsequence extension; Stacks 0FND
(blueprint: lem-pur-system-selected-derived-composition-evaluation).
Proof: reindex composite evaluation by t_(r∘s)(m)=t_s(t_r(m)). The right evaluation
squares paste: selected evaluation respects restriction composition, selected transition
commutes with restriction, and strict derived transitions compose. Apply evaluation
composition for normalized adjunction mates. Its extension uniqueness comparison is
the specified composition mate and its scalar comparison is the canonical associator.
Reindexing the composite evaluation inserts exactly the displayed equality transport. -/
theorem systemSelectedDerivedComposition_eval (m : ℕ)
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B (s.trans r)))) :
    (derivedSystemEvaluation B m).map
        ((systemSelectedDerivedComposition S (systemTensorCoherence S) B r s).hom.app P) ≫
      (systemSelectedDerivedBelow B (s.trans r) m S (systemTensorCoherence S)).hom.app P ≫
      eqToHom (systemSelectedTensor_trans S B r s m P) =
    (systemSelectedDerivedBelow B r m S (systemTensorCoherence S)).hom.app
        ((systemSelectedDerivedExtension (selectedSystemRings B r) s S
          (systemTensorCoherence S)).derived.obj P) ≫
      (systemDerivedTensor S B (systemNextSelected_spec r m).1).map
        ((systemSelectedDerivedBelow (selectedSystemRings B r) s (systemNextSelected r m)
          S (systemTensorCoherence S)).hom.app P) ≫
      ((systemTensorCoherence S).derivedAssoc B (systemNextSelected_spec r m).1
        (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1)).hom.app
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected s (systemNextSelected r m))).obj P) := by
  let T := systemTensorCoherence S
  let Br := selectedSystemRings B r
  let a := systemNextSelected r m
  let c := systemNextSelected s a
  let p := (systemNextSelected_spec r m).1
  let k := (systemNextSelected_spec s a).1
  let h := p.trans (r.monotone k)
  let df := systemSelectedDerivedExtension Br s S T
  let dg := systemSelectedDerivedExtension B r S T
  let dh := systemSelectedDerivedExtension B (s.trans r) S T
  let γ₁ := (systemDerivedSubsequenceEvaluation Br s c).hom ≫ systemDerivedTransition Br k
  let γ₂ := (systemDerivedSubsequenceEvaluation B r a).hom ≫ systemDerivedTransition B p
  let γ₃ := (systemDerivedSubsequenceEvaluation B (s.trans r) c).hom ≫
    systemDerivedTransition B h
  let ν₃ := systemSelectedDerivedBelowIndex S T B (s.trans r) m
    (systemNextSelected_trans r s m) h
  have hr (M : DerivedCategory (StrictRingSystem B)) :
      (derivedSystemEvaluation (selectedSystemRings B (s.trans r)) c).map
          ((systemDerivedSubsequenceComposition B r s).hom.app M) ≫ γ₃.app M =
      γ₁.app ((derivedSystemSubsequence B r).obj M) ≫
        (systemRestriction B (r.monotone k)).mapDerivedCategory.map (γ₂.app M) ≫
        (systemDerivedRestrictionComposition B p (r.monotone k)).hom.app
          ((derivedSystemEvaluation B m).obj M) := by
    dsimp only [γ₁, γ₂, γ₃, NatTrans.comp_app]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [reassoc_of% (systemDerivedSubsequenceEvaluation_composition B r s c M)]
    erw [← systemDerivedTransition_comp B p (r.monotone k) M]
    erw [reassoc_of% (systemDerivedSubsequenceTransition B r k M)]
  have hh := adjunctionEvaluation_composition df.adjunction dg.adjunction dh.adjunction
    (systemDerivedTensorAdj S Br k) (systemDerivedTensorAdj S B p)
    (systemDerivedTensorAdj S B h)
    (systemDerivedSubsequenceComposition B r s)
    (systemDerivedRestrictionComposition B p (r.monotone k)) γ₁ γ₂ γ₃
    (systemSelectedDerivedBelow Br s a S T) (systemSelectedDerivedBelow B r m S T) ν₃
    (by
      intro Q M f
      exact systemSelectedDerivedTranspose S T Br s a Q M f)
    (by
      intro Q M f
      exact systemSelectedDerivedTranspose S T B r m Q M f)
    (by
      intro Q M f
      exact systemSelectedDerivedBelowIndex_transpose S T B (s.trans r) m
        (systemNextSelected_trans r s m) h Q M f) hr P
  have hi := systemSelectedDerivedBelowIndex_hom S T B (s.trans r) m
    (systemNextSelected_trans r s m) h P (systemSelectedTensor_trans S B r s m P)
  change ν₃.hom.app P = _ at hi
  rw [hi] at hh
  exact hh

end SheafOfModules
