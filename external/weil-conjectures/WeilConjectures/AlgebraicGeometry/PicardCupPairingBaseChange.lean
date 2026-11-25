/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.PicardPairingPullbackCoherence

/-! # Compatibility of the cup pairing with arbitrary base change
Source: Stacks Project, Tag 0BDP, final two paragraphs.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem tensorIso_inv_naturality {W T : Scheme.{u}} (h : T ⟶ W)
    {A B C D : W.Modules} (a : A ⟶ B) (b : C ⟶ D) :
    ((Modules.tensorPullback h).map a ⊗ₘ (Modules.tensorPullback h).map b) ≫
        (Modules.picardTensorObjIso h B D).inv =
      (Modules.picardTensorObjIso h A C).inv ≫
        (Modules.tensorPullback h).map (a ⊗ₘ b) := by
  simp only [Modules.picardTensorObjIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [(Modules.picardTensorComparison h).hom.naturality a,
    (Modules.picardTensorComparison h).hom.naturality b]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_assoc]
  erw [(Modules.picardTensorComparison h).inv.naturality]
  rfl

@[reassoc]
private theorem tensorIso_hom_naturality {W T : Scheme.{u}} (h : T ⟶ W)
    {A B C D : W.Modules} (a : A ⟶ B) (b : C ⟶ D) :
    (Modules.tensorPullback h).map (a ⊗ₘ b) ≫
        (Modules.picardTensorObjIso h B D).hom =
      (Modules.picardTensorObjIso h A C).hom ≫
        ((Modules.tensorPullback h).map a ⊗ₘ (Modules.tensorPullback h).map b) := by
  apply (cancel_epi (Modules.picardTensorObjIso h A C).inv).1
  rw [← tensorIso_inv_naturality_assoc]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

private theorem pairing_pullback_injective {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf))) {A : Y.Modules}
    {a b : A ⟶ SheafOfModules.unit Y.ringCatSheaf}
    (hab : (Modules.tensorPullback p).map a ≫ (Modules.picardTensorUnitIso p).hom =
      (Modules.tensorPullback p).map b ≫ (Modules.picardTensorUnitIso p).hom) :
    a = b := by
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  let : IsIso (adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)) := hO
  have hh : (Modules.tensorPullback p).map a = (Modules.tensorPullback p).map b :=
    (cancel_mono (Modules.picardTensorUnitIso p).hom).1 hab
  apply (cancel_mono (adj.unit.app (SheafOfModules.unit Y.ringCatSheaf))).1
  rw [← adj.unit_naturality a, ← adj.unit_naturality b, hh]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero cup pairing commutes with the canonical direct-image maps.
This statement does not assume the direct-image maps are invertible and does not
assert any dual-pullback comparison is invertible.

Source: Stacks Project, Tag 0BDP, compatibility with arbitrary change of base
and the evaluation formula for the cup product in the final two paragraphs.
(blueprint: lem-sc-picard-cup-pairing-base-change)

Proof: Expand picardCupProductMap and uncurry its defining transpose, obtaining
the pushed-forward evaluation pairing. Apply the tensor comparison for h. Take
the adjoint along p_T of the two proposed pairings. Expand each canonical
base-change map as the mate of the top pullback unit. Naturality of the units
and counits, together with the two triangle identities, replaces the two
base-change maps followed by the p_T counits with the pullbacks of the p_W
counits. Tensor-composition comparisons transport their evaluations to X_T.
Both adjoints are then the pullback of E tensor dual E to X_T, followed by the
pulled evaluation and the inverse structure-sheaf unit. The structure units
commute with base change because their section formula is m mapped to 1 tensor m.
The tensor comparisons commute by naturality and tensor associativity. Thus the
adjoints agree; injectivity of the adjunction Hom equivalence proves the formula.
This calculation uses neither local freeness nor any flatness of h. Zero pairings
and empty bases satisfy the same identities. -/
theorem picardCupPairing_baseChange
    {X S W T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    (j : W ⟶ S) (h : T ⟶ W)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hOT : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).unit.app
        (SheafOfModules.unit T.ringCatSheaf))) :
    ((Modules.picardDirectImageBaseChangeMap f j h E) ⊗ₘ
        (Modules.picardDirectImageBaseChangeMap f j h (Modules.dual E))) ≫
      MonoidalClosed.uncurry (picardCupProductMap f E (h ≫ j) hOT) =
    (Modules.picardTensorObjIso h
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj E))
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E)))).inv ≫
      (Modules.tensorPullback h).map (MonoidalClosed.uncurry (picardCupProductMap f E j hO)) ≫
        (Modules.picardTensorUnitIso h).hom := by
  apply pairing_pullback_injective (pullback.snd f (h ≫ j)) hOT
  simp only [picardCupProductMap, MonoidalClosed.uncurry_curry]
  have hc := Modules.picardPairing_pullback_coherence f j h E (Modules.dual E)
    (Modules.dualEvaluation E)
    ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj E))
    ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E)))
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.snd f j))).counit.app ((Modules.tensorPullback (pullback.fst f j)).obj E))
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.snd f j))).counit.app
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E)))
    (Modules.picardPushforwardPairing (pullback.snd f j) hO
      ((Modules.tensorPullback (pullback.fst f j)).obj E)
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))
    ((Modules.picardTensorObjIso (pullback.fst f j) E (Modules.dual E)).inv ≫
      (Modules.tensorPullback (pullback.fst f j)).map (Modules.dualEvaluation E) ≫
      (Modules.picardTensorUnitIso (pullback.fst f j)).hom))
    (Modules.picardPushforwardPairing_counit (pullback.snd f j) hO
      ((Modules.tensorPullback (pullback.fst f j)).obj E)
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))
    ((Modules.picardTensorObjIso (pullback.fst f j) E (Modules.dual E)).inv ≫
      (Modules.tensorPullback (pullback.fst f j)).map (Modules.dualEvaluation E) ≫
      (Modules.picardTensorUnitIso (pullback.fst f j)).hom))
  conv_lhs => rw [Functor.map_comp, Category.assoc]
  conv_lhs => rw [Modules.picardPushforwardPairing_counit]
  conv_lhs => rw [tensorIso_hom_naturality_assoc]
  conv_lhs => rw [tensorHom_comp_tensorHom_assoc]
  conv_lhs => simp only [Modules.picardDirectImageBaseChangeMap_counit f j h E,
    Modules.picardDirectImageBaseChangeMap_counit f j h (Modules.dual E)]
  exact hc.symm

end AlgebraicGeometry.Scheme
