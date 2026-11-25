/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardBaseChangeCounit
import WeilConjectures.AlgebraicGeometry.PicardPairingComposition

/-! # Tensor and unit coherence for a pairing on a pullback square

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_pairing_paths
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B A' B' D E D' E' U : C} (i : A ≅ D) (j : B ≅ E)
    (i' : D ≅ D') (j' : E ≅ E') (k : A' ≅ D') (l : B' ≅ E')
    (r : D' ⊗ E' ⟶ U) (s : A ⊗ B ⟶ U) (t : A' ⊗ B' ⟶ U)
    (hs : s = ((i.hom ≫ i'.hom) ⊗ₘ (j.hom ≫ j'.hom)) ≫ r)
    (ht : t = (k.hom ⊗ₘ l.hom) ≫ r) :
    s = ((i ≪≫ i' ≪≫ k.symm).hom ⊗ₘ (j ≪≫ j' ≪≫ l.symm).hom) ≫ t := by
  rw [hs, ht]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorHom_comp_tensorHom_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem tensor_pairing_coefficients
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B D E D' E' F G F' G' U : C}
    (c : A ⟶ D) (d : B ⟶ E) (a : D ⟶ D') (b : E ⟶ E')
    (i : D' ≅ F) (j : E' ≅ G) (i' : F ≅ F') (j' : G ≅ G')
    (r : F' ⊗ G' ⟶ U) :
    (c ⊗ₘ d) ≫ (a ⊗ₘ b) ≫ ((i.hom ≫ i'.hom) ⊗ₘ (j.hom ≫ j'.hom)) ≫ r =
      ((c ≫ a ≫ (i ≪≫ i').hom) ⊗ₘ (d ≫ b ≫ (j ≪≫ j').hom)) ≫ r := by
  simp only [Iso.trans_hom, tensorHom_comp_tensorHom_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem pairing_tensor_naturality {W T : Scheme.{u}} (h : T ⟶ W)
    {A B C D : W.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    ((tensorPullback h).map f ⊗ₘ (tensorPullback h).map g) ≫
        (picardTensorObjIso h B D).inv =
      (picardTensorObjIso h A C).inv ≫ (tensorPullback h).map (f ⊗ₘ g) := by
  simp only [picardTensorObjIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [(picardTensorComparison h).hom.naturality f,
    (picardTensorComparison h).hom.naturality g]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_assoc]
  erw [(picardTensorComparison h).inv.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pairing_square_iso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (A : W.Modules)
    (e : Limits.pullback.snd f (h ≫ j) ≫ h =
      picardBaseChangeTop f j h ≫ Limits.pullback.snd f j) :
    picardBaseChangeSquareIso f j h A =
      picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h A ≪≫
        eqToIso (congrArg
          (fun (k : Limits.pullback f (h ≫ j) ⟶ W) ↦ (tensorPullback k).obj A) e) ≪≫
        (picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.snd f j) A).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pairing_square
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W)
    (A B : W.Modules) (g : A ⊗ B ⟶ SheafOfModules.unit W.ringCatSheaf) :
    (picardTensorObjIso (Limits.pullback.snd f (h ≫ j))
      ((tensorPullback h).obj A) ((tensorPullback h).obj B)).inv ≫
      (tensorPullback (Limits.pullback.snd f (h ≫ j))).map
        ((picardTensorObjIso h A B).inv ≫ (tensorPullback h).map g ≫
          (picardTensorUnitIso h).hom) ≫
      (picardTensorUnitIso (Limits.pullback.snd f (h ≫ j))).hom =
    ((picardBaseChangeSquareIso f j h A).hom ⊗ₘ
      (picardBaseChangeSquareIso f j h B).hom) ≫
      (picardTensorObjIso (picardBaseChangeTop f j h)
        ((tensorPullback (Limits.pullback.snd f j)).obj A)
        ((tensorPullback (Limits.pullback.snd f j)).obj B)).inv ≫
      (tensorPullback (picardBaseChangeTop f j h)).map
        ((picardTensorObjIso (Limits.pullback.snd f j) A B).inv ≫
          (tensorPullback (Limits.pullback.snd f j)).map g ≫
            (picardTensorUnitIso (Limits.pullback.snd f j)).hom) ≫
      (picardTensorUnitIso (picardBaseChangeTop f j h)).hom := by
  rw [pairing_square_iso f j h A (by exact (Limits.pullback.lift_snd _ _ _).symm),
    pairing_square_iso f j h B (by exact (Limits.pullback.lift_snd _ _ _).symm)]
  exact tensor_pairing_paths (C := (Limits.pullback f (h ≫ j)).Modules)
    (picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h A)
    (picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h B)
    (eqToIso (congrArg (fun (k : Limits.pullback f (h ≫ j) ⟶ W) ↦ (tensorPullback k).obj A)
      (by exact (Limits.pullback.lift_snd _ _ _).symm)))
    (eqToIso (congrArg (fun (k : Limits.pullback f (h ≫ j) ⟶ W) ↦ (tensorPullback k).obj B)
      (by exact (Limits.pullback.lift_snd _ _ _).symm)))
    (picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.snd f j) A)
    (picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.snd f j) B)
    _ _ _
    (picardPairing_comp (Limits.pullback.snd f (h ≫ j)) h
      (picardBaseChangeTop f j h ≫ Limits.pullback.snd f j)
      (by exact (Limits.pullback.lift_snd _ _ _).symm) A B g)
    (by
      simpa only [eqToIso_refl, Iso.refl_hom, Category.comp_id] using
        (picardPairing_comp (picardBaseChangeTop f j h) (Limits.pullback.snd f j)
          _ rfl A B g))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pairing_coefficient_iso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules)
    (e : picardBaseChangeTop f j h ≫ Limits.pullback.fst f j =
      Limits.pullback.fst f (h ≫ j)) :
    picardBaseChangeCoefficientIso f j h M =
      picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.fst f j) M ≪≫
        eqToIso (congrArg
          (fun (k : Limits.pullback f (h ≫ j) ⟶ X) ↦ (tensorPullback k).obj M) e) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a pulled pairing across the square and the coefficient comparisons.
This is a monoidal coherence statement: a and b are arbitrary maps, g is an
arbitrary pairing satisfying the displayed pullback equation, and there is no
base-change map or adjunction unit in the conclusion.
Source: Stacks Project, Tags 0095 and 0096 (tensor pullback and composition),
Tag 0BDP, evaluation formula. (blueprint: lem-sc-picard-pairing-pullback-coherence)

Proof: Write P_k for tensor pullback, δ_k for picardTensorObjIso(k).hom,
u_k for picardTensorUnitIso(k).hom, C_A for the square comparison, and D_M
for the coefficient comparison. Put e_W = δ_qW.inv followed by P_qW(ev)
and u_qW, and define e_T similarly. Transport by picardTensorComparison
to ordinary pullback. Its composition comparison sends the iterated pure
tensor r tensor (s tensor m) to rs tensor m. This respects tensor products
and sends the unit generator to the unit generator; these formulas extend
to the sheafifications by the universal property. Hence composition and
square comparisons are compatible with both δ and u. Transport back.

Square tensor/unit coherence and naturality express the left side as
δ_pT followed by C_A tensor C_B, then δ_v.inv, then P_v of
(δ_pW.inv followed by P_pW(g) and u_pW), and finally u_v. Substitute hg:
δ_pW.inv cancels δ_pW, leaving P_v of (a tensor b followed by e_W).
Functoriality and tensor naturality move a tensor b through δ_v.inv.
The resulting expression is δ_pT followed by
(C_A followed by P_v(a)) tensor (C_B followed by P_v(b)),
then δ_v.inv, P_v(e_W), and u_v. Coefficient tensor/unit coherence gives
δ_v.inv followed by P_v(e_W) and u_v = (D_M tensor D_N) followed by e_T.
Substitute and use tensorHom_comp_tensorHom to combine the two tensor
morphisms. This is exactly the right side. No adjunction counit, base-change
map, inverse structure unit, finiteness or flatness is used. Zero pairings
and empty schemes obey the same functorial identities. -/
theorem picardPairing_pullback_coherence
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W)
    (M N : X.Modules) (ev : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (A B : W.Modules)
    (a : (tensorPullback (Limits.pullback.snd f j)).obj A ⟶
      (tensorPullback (Limits.pullback.fst f j)).obj M)
    (b : (tensorPullback (Limits.pullback.snd f j)).obj B ⟶
      (tensorPullback (Limits.pullback.fst f j)).obj N)
    (g : A ⊗ B ⟶ SheafOfModules.unit W.ringCatSheaf)
    (hg : (tensorPullback (Limits.pullback.snd f j)).map g ≫
        (picardTensorUnitIso (Limits.pullback.snd f j)).hom =
      (picardTensorObjIso (Limits.pullback.snd f j) A B).hom ≫ (a ⊗ₘ b) ≫
        (picardTensorObjIso (Limits.pullback.fst f j) M N).inv ≫
        (tensorPullback (Limits.pullback.fst f j)).map ev ≫
        (picardTensorUnitIso (Limits.pullback.fst f j)).hom) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).map
      ((picardTensorObjIso h A B).inv ≫ (tensorPullback h).map g ≫
        (picardTensorUnitIso h).hom) ≫
      (picardTensorUnitIso (Limits.pullback.snd f (h ≫ j))).hom =
    (picardTensorObjIso (Limits.pullback.snd f (h ≫ j))
      ((tensorPullback h).obj A) ((tensorPullback h).obj B)).hom ≫
      (((picardBaseChangeSquareIso f j h A).hom ≫
          (tensorPullback (picardBaseChangeTop f j h)).map a ≫
          (picardBaseChangeCoefficientIso f j h M).hom) ⊗ₘ
        ((picardBaseChangeSquareIso f j h B).hom ≫
          (tensorPullback (picardBaseChangeTop f j h)).map b ≫
          (picardBaseChangeCoefficientIso f j h N).hom)) ≫
      (picardTensorObjIso (Limits.pullback.fst f (h ≫ j)) M N).inv ≫
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).map ev ≫
      (picardTensorUnitIso (Limits.pullback.fst f (h ≫ j))).hom := by
  apply (cancel_epi (picardTensorObjIso (Limits.pullback.snd f (h ≫ j))
    ((tensorPullback h).obj A) ((tensorPullback h).obj B)).inv).mp
  rw [pairing_square]
  simp only [Iso.inv_hom_id_assoc]
  rw [Functor.map_comp, Category.assoc, hg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← pairing_tensor_naturality_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [picardPairing_comp (picardBaseChangeTop f j h) (Limits.pullback.fst f j)
    (Limits.pullback.fst f (h ≫ j))
    (by exact Limits.pullback.lift_fst _ _ _) M N ev]
  rw [pairing_coefficient_iso f j h M (by exact Limits.pullback.lift_fst _ _ _),
    pairing_coefficient_iso f j h N (by exact Limits.pullback.lift_fst _ _ _)]
  exact tensor_pairing_coefficients _ _ _ _ _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules
