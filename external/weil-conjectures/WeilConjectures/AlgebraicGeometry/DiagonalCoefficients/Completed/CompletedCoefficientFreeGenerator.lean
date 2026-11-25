/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficients
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import WeilConjectures.CategoryTheory.SixFunctors.LocalAdicLinearity
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedFreeAdicSeparation

/-! # Free representables for the completed coefficient action

Source: the local generator argument in lem-sfb-diagonal-completed-section-action;
Mathlib's free-module and module-sheafification adjunctions.
(blueprint: lem-sfb-diagonal-completed-free-generator).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The free completed-coefficient presheaf on a representable, with the representable
lifted to the coefficient universe. Source: the free local generators in the proof of
lem-sfb-diagonal-completed-section-action
(blueprint: lem-sfb-diagonal-completed-free-generator). -/
def completedFreePresheaf (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :=
  (PresheafOfModules.free
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj).obj
      (uliftYoneda.{u + 1}.obj U.unop)

/-- Sheafify the actual free presheaf on the local representable. Source: module
sheafification, Mathlib's sheafificationAdjunction
(blueprint: lem-sfb-diagonal-completed-free-generator). -/
def completedFreeCell (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) : DiagonalCompleted l X :=
  (PresheafOfModules.sheafification
    (𝟙 (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj)).obj
      (completedFreePresheaf l X U)

/-- The distinguished local generator is the sheafification of the identity basis
vector. Source: the local generator argument, not a choice of an existence witness
(blueprint: lem-sfb-diagonal-completed-free-generator). -/
def completedFreeGenerator (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    (completedFreeCell l X U).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj)).unit.app
      (completedFreePresheaf l X U)).app U (ModuleCat.freeMk (ULift.up (𝟙 U.unop)))

/-- The morphism that sends the local generator to the specified section. Source:
compose the inverses of the sheafification, free-module, and Yoneda adjunctions
(blueprint: lem-sfb-diagonal-completed-free-generator). -/
def completedFreeDesc {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : DiagonalCompleted l X) (U : X.ProEtᵒᵖ) (m : M.val.obj U) :
    completedFreeCell l X U ⟶ M :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj)).homEquiv _ _ |>.symm
      (PresheafOfModules.freeHomEquiv.symm (uliftYonedaEquiv.{u + 1}.symm m))

/-- Evaluation of the explicitly constructed local generator map. Source: triangle
identities of the three adjunctions defining completedFreeDesc
(blueprint: lem-sfb-diagonal-completed-free-generator).
Proof: apply the sheafification Hom equivalence to its own inverse, then evaluate
on the identity basis vector; the free-module and Yoneda units evaluate to m. -/
theorem completedFreeDesc_generator {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : DiagonalCompleted l X) (U : X.ProEtᵒᵖ) (m : M.val.obj U) :
    (completedFreeDesc M U m).val.app U (completedFreeGenerator l X U) = m := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj)).homEquiv _ _
    |>.apply_symm_apply
      (PresheafOfModules.freeHomEquiv.symm (uliftYonedaEquiv.{u + 1}.symm m))
  have h' := congrArg (fun f ↦
    uliftYonedaEquiv.{u + 1} (PresheafOfModules.freeHomEquiv f)) h
  exact h'.trans (by simp only [Equiv.apply_symm_apply])

attribute [local irreducible] completedFreeCell completedFreePresheaf upperStarFromPoint
  Scheme.purTwistZlCompletionOfUniverses
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

/-- Every additive sheaf map into a free pro-affine etale completed-coefficient module is
linear for any ring isomorphism from the reconstructed condensed coefficient ring.
This concerns a fixed free target and arbitrary additive maps, with no realization
functor or normalization data.

Source: the free local generator step of lem-sfb-diagonal-completed-section-action;
WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear, linearity criterion;
blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1).
(blueprint: lem-sfb-diagonal-completed-free-generator).

Proof: the completed coefficient ring is locally generated by integers modulo
every l-power. A ring isomorphism preserves its unit and integer multiplications,
so the same is true after identifying it with the reconstructed condensed ring.
The free pro-affine etale representable is l-adically separated by
completedFree_adicSeparated, using local linear tests and the finite coefficient
projections. The sectionwise criterion
linearity_of_localIntegers_adicSeparated computes the action defect as a local
multiple of every l-power, so this separation makes the defect vanish. The empty test
object and zero module are included by the sheaf axioms and additivity. -/
theorem completedFreeCell_automaticLinearity (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (c : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    (N : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))))
    (g : (SheafOfModules.toSheaf _).obj N ⟶
      (SheafOfModules.toSheaf _).obj (completedFreeCell l X U))
    (V : X.ProEtᵒᵖ) (r : ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X)
          (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))).obj.obj V)
    (x : N.val.obj V) :
    g.hom.app V (r • x) =
      @SMul.smul _ ((completedFreeCell l X U).val.obj V) inferInstance
        (c.hom.hom.app V r) (g.hom.app V x) := by
  apply linearity_of_localIntegers_adicSeparated l c N (completedFreeCell l X U) g
    (fun n V r ↦ completedCoefficient_localIntegers l X n V r) ?_ V r x
  unfold completedFreeCell completedFreePresheaf
  exact completedFree_adicSeparated l X U hU

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
