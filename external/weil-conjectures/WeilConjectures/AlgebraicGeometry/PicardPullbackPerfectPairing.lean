/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDualPairing
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Perfectness of the explicit pulled-back evaluation pairing

Source: Stacks Project, Tags 0FNV and 01C8, the pulled-back dual basis.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The evaluation pairing used in the Picard cup-product construction is perfect
after pullback of a finite locally free module.

Source: Stacks Project, Tags 0FNV and 01C8, finite free evaluation and pullback.
(blueprint: lem-sc-picard-pullback-perfect-evaluation)

Proof: Finite local freeness makes E dualizable. Use its canonical exact pairing
with internal dual, whose evaluation is dualEvaluation E. The ordinary monoidal
pullback preserves this exact pairing. Transport it through picardTensorComparison
to the two tensor-formula pullbacks. Its evaluation is the explicit pulled-back
evaluation with the monoidal unit comparison. Replacing that comparison by
pullbackObjUnitIso only postcomposes evaluation by an automorphism of O_X.
Transposition takes postcomposition to the internal-Hom functor, which preserves
isomorphisms. Thus the explicit pairing is perfect. This includes the zero bundle
and empty schemes without choosing any nonempty local frame. -/
theorem isIso_curry_picardPullbackEvaluation
    {X Y : Scheme.{u}} (p : X ⟶ Y) (E : Y.Modules) [E.IsFiniteLocallyFree] :
    IsIso (curry ((picardTensorObjIso p E (dual E)).inv ≫
      (tensorPullback p).map (dualEvaluation E) ≫ (picardTensorUnitIso p).hom)) := by
  obtain ⟨pn⟩ := nonempty_exactPairing_dual_of_isFiniteLocallyFree E
  let : ExactPairing (dual E) E := pn
  have : IsIso (ihomUnitTensorToIhom E E) :=
    isIso_ihomUnitTensorToIhom (dual E) E E
  let : ExactPairing (dual E) E := exactPairingOfIsIso E
  have hbase : ε_ (dual E) E = dualEvaluation E := by
    change (ihom.ev E).app (SheafOfModules.unit Y.ringCatSheaf) = _
    erw [SheafOfModules.ihom_ev_app (R := Y.sheaf) E (SheafOfModules.unit Y.ringCatSheaf)]
    change (SheafOfModules.tensorObjIsoSheafification E (dual E)).hom ≫
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
        _ (SheafOfModules.unit Y.ringCatSheaf)).symm
        (presheafDualEvaluation E) = _
    rw [Adjunction.homEquiv_counit]
    rfl
  let : ExactPairing ((pullback p).obj (dual E)) ((pullback p).obj E) :=
    ExactPairing.map (pullback p) (dual E) E
  let : ExactPairing ((tensorPullback p).obj (dual E)) ((tensorPullback p).obj E) :=
    exactPairingCongr ((picardTensorComparison p).app (dual E))
      ((picardTensorComparison p).app E)
  let s := inv (Functor.OplaxMonoidal.η (pullback p)) ≫ (pullbackObjUnitIso p).hom
  have heval : ε_ ((tensorPullback p).obj (dual E)) ((tensorPullback p).obj E) ≫ s =
      (picardTensorObjIso p E (dual E)).inv ≫ (tensorPullback p).map (dualEvaluation E) ≫
        (picardTensorUnitIso p).hom := by
    change (tensorPullback p).obj E ◁ (picardTensorComparison p).hom.app (dual E) ≫
      (picardTensorComparison p).hom.app E ▷ (pullback p).obj (dual E) ≫
      Functor.LaxMonoidal.μ (pullback p) E (dual E) ≫
        (pullback p).map (ε_ (dual E) E) ≫ Functor.OplaxMonoidal.η (pullback p) ≫ s = _
    rw [hbase]
    simp only [picardTensorObjIso, picardTensorUnitIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, tensorIso_inv, Functor.Monoidal.μIso_hom, Category.assoc]
    erw [(picardTensorComparison p).hom.naturality_assoc (dualEvaluation E)]
    erw [← tensorHom_def'_assoc]
    erw [Iso.inv_hom_id_assoc ((picardTensorComparison p).app (E ⊗ dual E))]
    dsimp only [s]
    erw [Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc]
    rfl
  erw [← heval, curry_natural_right]
  dsimp only [s]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
