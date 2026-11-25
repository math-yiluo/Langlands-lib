/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDualPairing
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Perfect pushed-forward pairings split the evaluation counit

Source: Stacks Project, Tag 0BDP, final paragraph, the lifted dual basis.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed

section
variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C]

private theorem splitMono_of_pairing {A B M D : C} [ExactPairing B A]
    (a : A ⟶ M) (b : B ⟶ D) (ev : M ⊗ D ⟶ 𝟙_ C)
    (h : (a ⊗ₘ b) ≫ ev = ε_ B A) : IsSplitMono a := by
  let := BraidedCategory.exactPairing_swap B A
  let t := curry ((β_ B A).hom ≫ ε_ B A)
  have ht : IsIso t := inferInstanceAs (IsIso (curry (ε_ A B)))
  let r := curry ((β_ B M).hom ≫ M ◁ b ≫ ev) ≫ inv t
  apply IsSplitMono.mk'
  refine ⟨r, ?_⟩
  dsimp [r]
  rw [← Category.assoc, ← curry_natural_left]
  have he : B ◁ a ≫ (β_ B M).hom ≫ M ◁ b ≫ ev = (β_ B A).hom ≫ ε_ B A := by
    rw [BraidedCategory.braiding_naturality_right_assoc]
    rw [← Category.assoc (a ▷ B), ← tensorHom_def, h]
  rw [he]
  exact IsIso.hom_inv_id t

end

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A perfect pushed-forward pairing gives a retraction of the counit at its first
factor, provided that factor's direct image is finite locally free. No rank comparison
between the first factor and its direct image is needed.

Source: Stacks Project, Tag 0BDP, final paragraph, lifting the coordinate dual basis.
(blueprint: lem-sc-picard-perfect-pairing-split-counit)

Proof: A perfect pairing between p_*M and p_*D makes p_*D the dual of p_*M, since
p_*M is finite locally free. Pulling this exact pairing back gives an exact pairing
of p^*p_*M with p^*p_*D. The cup-product counit identity identifies this pairing
with evaluation after the two counits. Transpose the counit on the second factor
using the pulled-back perfect pairing: this is a map M to p^*p_*M. Composing it
with the first counit gives the identity, by that evaluation identity and the
injectivity of transposition. Thus the first counit is split injective. Empty bases
and zero-rank modules are covered by the exact-pairing identities. -/
theorem isSplitMono_counit_of_isIso_picardPushforwardPairing
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (M D : X.Modules) (ev : M ⊗ D ⟶ SheafOfModules.unit X.ringCatSheaf)
    [((pushforward p).obj M).IsFiniteLocallyFree]
    (h : IsIso (curry (picardPushforwardPairing p hO M D ev))) :
    IsSplitMono ((Classical.choose (exists_tensorPullbackAdjunction p)).counit.app M) := by
  let N := (pushforward p).obj M
  let B := (pushforward p).obj D
  let v := picardPushforwardPairing p hO M D ev
  obtain ⟨pn⟩ := nonempty_exactPairing_dual_of_isFiniteLocallyFree N
  let : ExactPairing (dual N) N := pn
  let : ExactPairing N (dual N) := BraidedCategory.exactPairing_swap (dual N) N
  have hn : IsDualizable N := ⟨{ rightDual := dual N, exact := inferInstance }⟩
  have hv : IsPerfectPairing v := ⟨h⟩
  let : ExactPairing B N := hv.exactPairing hn
  have hbase : ε_ B N = v := hv.evaluation_exactPairing hn
  let : ExactPairing ((pullback p).obj B) ((pullback p).obj N) :=
    ExactPairing.map (pullback p) B N
  let : ExactPairing ((tensorPullback p).obj B) ((tensorPullback p).obj N) :=
    exactPairingCongr ((picardTensorComparison p).app B) ((picardTensorComparison p).app N)
  let s := inv (Functor.OplaxMonoidal.η (pullback p)) ≫ (pullbackObjUnitIso p).hom
  have heval : ε_ ((tensorPullback p).obj B) ((tensorPullback p).obj N) ≫ s =
      (picardTensorObjIso p N B).inv ≫ (tensorPullback p).map v ≫
        (picardTensorUnitIso p).hom := by
    change (tensorPullback p).obj N ◁ (picardTensorComparison p).hom.app B ≫
      (picardTensorComparison p).hom.app N ▷ (pullback p).obj B ≫
      Functor.LaxMonoidal.μ (pullback p) N B ≫ (pullback p).map (ε_ B N) ≫
      Functor.OplaxMonoidal.η (pullback p) ≫ s = _
    rw [hbase]
    simp only [picardTensorObjIso, picardTensorUnitIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, tensorIso_inv, Functor.Monoidal.μIso_hom, Category.assoc]
    erw [(picardTensorComparison p).hom.naturality_assoc v]
    erw [← tensorHom_def'_assoc]
    erw [Iso.inv_hom_id_assoc ((picardTensorComparison p).app (N ⊗ B))]
    dsimp only [s]
    erw [Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc]
    rfl
  let A := (tensorPullback p).obj N
  let C := (tensorPullback p).obj B
  have hA : IsDualizable A := by
    let : ExactPairing A C := BraidedCategory.exactPairing_swap C A
    exact ⟨{ rightDual := C, exact := inferInstance }⟩
  let v' := (picardTensorObjIso p N B).inv ≫ (tensorPullback p).map v ≫
    (picardTensorUnitIso p).hom
  have hv' : IsPerfectPairing v' := by
    constructor
    change IsIso (curry v')
    dsimp only [v']
    erw [← heval, curry_natural_right]
    dsimp only [s]
    infer_instance
  let : ExactPairing C A := hv'.exactPairing hA
  have heval' : ε_ C A = v' := hv'.evaluation_exactPairing hA
  apply splitMono_of_pairing
    (A := (tensorPullback p).obj N) (B := (tensorPullback p).obj B)
    ((Classical.choose (exists_tensorPullbackAdjunction p)).counit.app M)
    ((Classical.choose (exists_tensorPullbackAdjunction p)).counit.app D) ev
  rw [heval']
  dsimp only [v']
  rw [picardPushforwardPairing_counit]
  dsimp only [N, B]
  simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules
