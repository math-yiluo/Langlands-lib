/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The ordinary singleton mate of geometric evaluation

Source: Zheng Construction 4.1; Stacks 03D2 and 03EL.
(blueprint: lem-coef-geometric-ordinary-evaluation-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

/-- The ordinary singleton mate of geometric evaluation is invertible.
Source: Zheng, Construction 4.1, printed p. 21, and the paragraph before Lemma 4.10,
printed p. 23; Stacks 03D2 and 03EL.
(blueprint: lem-coef-geometric-ordinary-evaluation-mate).

Proof: the recorded ordinary system-unit evaluation identity characterizes the
right mate of the inverse pull-evaluation square. Transpose both sides, and cancel
the level pushforward of pull evaluation to identify that mate with the supplied
ordinary push-evaluation isomorphism. The iterated-mates identity identifies this
right mate with the conjugate of the singleton mate under the two composite
adjunctions. Conjugation reflects invertibility, proving the assertion for any
chosen singleton adjunctions. This uses neither coefficient flatness nor a derived
construction and applies also at level zero, on the empty site and to zero modules. -/
theorem geometricOrdinaryEvaluationMate_isIso [PreservesFiniteLimits uInv] (n : ℕ)
    (L : Mod.{c, v, max c v r} J (B n) ⥤ Systems.{c, v, max c v r} J B τ)
    (L' : Mod.{c, v, max c v r} J' (O.coefficients n) ⥤
      Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
    (adj : L ⊣ evaluation.{c, v, max c v r} J B τ n)
    (adj' : L' ⊣ evaluation.{c, v, max c v r}
      J' O.coefficients O.coefficientTransition n) :
    IsIso ((mateEquiv adj adj').symm
      (TwoSquare.mk _ _ _ _ (O.ordinaryPullEvaluation n).inv)) := by
  classical
  let δ := (O.ordinaryPullEvaluation n).symm
  let adjG := O.ordinaryAdjunction
  let adjL := O.levelAdjunction n
  let b := (mateEquiv adjG adjL (TwoSquare.mk _ _ _ _ δ.hom))
  have hb : b = (O.ordinaryPushEvaluation n).hom := by
    have he : (mateEquiv adjG adjL).symm
        (TwoSquare.mk _ _ _ _ (O.ordinaryPushEvaluation n).hom) =
        TwoSquare.mk _ _ _ _ δ.hom := by
      refine NatTrans.ext (funext fun M ↦ ?_)
      apply (adjL.homEquiv _ _).injective
      have hu := unit_mateEquiv_symm adjG adjL
        (TwoSquare.mk _ _ _ _ (O.ordinaryPushEvaluation n).hom) M
      change (adjL.homEquiv _ _) _ = (adjL.homEquiv _ _) (δ.hom.app M)
      simp only [Adjunction.homEquiv_unit]
      erw [← hu]
      apply (cancel_mono ((O.levelPush n).map
        ((O.ordinaryPullEvaluation n).hom.app M))).mp
      simp only [δ, Iso.symm_hom, Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app]
      erw [(O.levelPush n).map_id, Category.comp_id]
      exact O.ordinary_unit_evaluation n M
    have hh := congrArg (mateEquiv adjG adjL) he
    rw [Equiv.apply_symm_apply] at hh
    exact hh.symm
  let a := ((mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ δ.hom))
  have h := iterated_mateEquiv_conjugateEquiv adj adj' adjL adjG
    ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ δ.hom))
  rw [Equiv.apply_symm_apply] at h
  have hi : IsIso (conjugateEquiv (adj.comp adjG) (adjL.comp adj') a) := by
    rw [← h]
    change IsIso b
    rw [hb]
    infer_instance
  exact conjugateEquiv_of_iso (adj.comp adjG) (adjL.comp adj') a

end WeilConjectures.SemilinearSections
