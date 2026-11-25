/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluation
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import WeilConjectures.CategoryTheory.SmoothPurity.AdjunctionTransitionCoherence
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionCoherence
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequenceTransition

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
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ)

/-- The derived selected extension has precisely the tensor-adjoint transition
specified by its actual iterated transition. Source: Zheng 4.1; Stacks 0FND
(blueprint: lem-pur-system-selected-derived-transition).
Proof: the selected evaluation comparisons are the normalized mates of evaluation
followed by the actual strict transition. Derived transitions compose by localization
of the strict composition law, and selected evaluations commute with transitions.
These give the right-adjoint cocone composition square. Apply the general transition
coherence calculation for mates. The two left-adjoint uniqueness comparisons are
exactly the canonical tensor associators. No inequality is made strict, so this also
covers equal successive next-selected indices. -/
theorem systemSelectedDerivedTransition (m : ℕ)
    (N : DerivedCategory (StrictRingSystem (selectedSystemRings B r))) :
    ((systemDerivedTensorAdj S B (Nat.le_succ m)).homEquiv _ _).symm
      ((systemDerivedTransition B (Nat.le_succ m)).app
        ((systemSelectedDerivedExtension B r S (systemTensorCoherence S)).derived.obj N)) =
    (systemDerivedTensor S B (Nat.le_succ m)).map
      ((systemSelectedDerivedBelow B r (m + 1) S (systemTensorCoherence S)).hom.app N) ≫
    ((systemTensorCoherence S).derivedAssoc B (Nat.le_succ m)
      (systemNextSelected_spec r (m + 1)).1).hom.app
        ((derivedSystemEvaluation (selectedSystemRings B r)
          (systemNextSelected r (m + 1))).obj N) ≫
    ((systemTensorCoherence S).derivedAssoc B (systemNextSelected_spec r m).1
      (r.monotone (systemNextSelected_mono r m))).inv.app
        ((derivedSystemEvaluation (selectedSystemRings B r)
          (systemNextSelected r (m + 1))).obj N) ≫
    (systemDerivedTensor S B (systemNextSelected_spec r m).1).map
      (((systemDerivedTensorAdj S (selectedSystemRings B r)
        (systemNextSelected_mono r m)).homEquiv _ _).symm
          ((systemDerivedTransition (selectedSystemRings B r)
            (systemNextSelected_mono r m)).app N)) ≫
    (systemSelectedDerivedBelow B r m S (systemTensorCoherence S)).inv.app N := by
  let T := systemTensorCoherence S
  let d := systemSelectedDerivedExtension B r S T
  let a := systemNextSelected r m
  let b := systemNextSelected r (m + 1)
  let p := (systemNextSelected_spec r m).1
  let q := (systemNextSelected_spec r (m + 1)).1
  let k := systemNextSelected_mono r m
  have hν (j : ℕ) (P : DerivedCategory (StrictRingSystem (selectedSystemRings B r))) :
      (systemDerivedTensorAdj S B (systemNextSelected_spec r j).1).homEquiv _ _
        ((systemSelectedDerivedBelow B r j S T).inv.app P) =
      (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r j)).map
        (d.adjunction.unit.app P) ≫
      (systemDerivedSubsequenceEvaluation B r (systemNextSelected r j)).hom.app (d.derived.obj P) ≫
      (systemDerivedTransition B (systemNextSelected_spec r j).1).app (d.derived.obj P) := by
    have hh := systemSelectedDerivedTranspose S T B r j P (d.derived.obj P) (𝟙 _)
    erw [(derivedSystemEvaluation B j).map_id, Category.comp_id,
      d.adjunction.homEquiv_id] at hh
    exact hh
  have hr (M : DerivedCategory (StrictRingSystem B)) :
      (systemDerivedSubsequenceEvaluation B r b).hom.app M ≫
        (systemDerivedTransition B q).app M ≫
        (systemRestriction B q).mapDerivedCategory.map
          ((systemDerivedTransition B (Nat.le_succ m)).app M) ≫
        (systemDerivedRestrictionComposition B (Nat.le_succ m) q).hom.app
          ((derivedSystemEvaluation B m).obj M) =
      (systemDerivedTransition (selectedSystemRings B r) k).app
          ((derivedSystemSubsequence B r).obj M) ≫
        (systemRestriction B (r.monotone k)).mapDerivedCategory.map
          ((systemDerivedSubsequenceEvaluation B r a).hom.app M) ≫
        (systemRestriction B (r.monotone k)).mapDerivedCategory.map
          ((systemDerivedTransition B p).app M) ≫
        (systemDerivedRestrictionComposition B p (r.monotone k)).hom.app
          ((derivedSystemEvaluation B m).obj M) := by
    erw [systemDerivedTransition_comp B (Nat.le_succ m) q M]
    erw [← systemDerivedTransition_comp B p (r.monotone k) M]
    erw [reassoc_of% (systemDerivedSubsequenceTransition B r k M)]
  have hh := adjunctionTransition_coherence d.adjunction
    (systemDerivedTensorAdj S B p) (systemDerivedTensorAdj S B q)
    (systemDerivedTensorAdj S B (Nat.le_succ m))
    (systemDerivedTensorAdj S (selectedSystemRings B r) k)
    (systemDerivedTensorAdj S B (p.trans (r.monotone k)))
    (systemDerivedRestrictionComposition B (Nat.le_succ m) q)
    (systemDerivedRestrictionComposition B p (r.monotone k))
    (systemDerivedSubsequenceEvaluation B r a).hom
    (systemDerivedSubsequenceEvaluation B r b).hom
    (systemDerivedTransition (selectedSystemRings B r) k)
    (systemDerivedTransition B (Nat.le_succ m))
    (systemDerivedTransition B p) (systemDerivedTransition B q)
    (systemSelectedDerivedBelow B r m S T)
    (systemSelectedDerivedBelow B r (m + 1) S T)
    (hν m) (hν (m + 1)) hr N
  exact hh

end SheafOfModules
