/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
public import WeilConjectures.CategoryTheory.Tensor.TensorTowerDatum
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Transport of a bilinear tower through recorded stage equalities -/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false

open CategoryTheory
namespace CategoryTheory.BilinearCoefficientDescent

/-- A tensor tower survives replacement of its transitions and associators by equal data.
Source: the transport step of the common-stage tensor argument.
Proof: substitute the transition equalities, then the associator equalities by function
extensionality. The equality isomorphisms are now identities, so the assertion reduces
to the given tower equation by the product and whiskering component formulas.
(blueprint: lem-weil-bilinear-stage-tower-transport). -/
theorem familyTower_of_transport
    {I : Type*} [Preorder I] {C : I → Type*} [∀ i, Category (C i)]
    (R : ∀ {i j : I}, i ≤ j → C i ⥤ C j)
    (a : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), R h ⋙ R k ≅ R (h.trans k))
    (U : ∀ i, C i × C i ⥤ C i)
    (c : ∀ {i j : I} (h : i ≤ j), U i ⋙ R h ≅ (R h).prod (R h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (hk : j ≤ k),
      (@TensorTowerDatum.mk (C i) (C j) (C k) (inferInstance : Category (C i))
        (inferInstance : Category (C j)) (inferInstance : Category (C k))
        (U i) (U j) (U k) (R h) (R hk) (R (h.trans hk))
        (a h hk) (c h) (c hk) (c (h.trans hk))).Coherent)
    (S : StageSystem C) (hR : ∀ {i j : I} (h : i ≤ j), S.T h = R h)
    (ha : ∀ {i j k : I} (h : i ≤ j) (k : j ≤ k), HEq (S.assoc h k) (a h k)) :
    BilinearCoefficientDescent.FamilyTower S S S U (fun {_ _} h ↦
      Functor.isoWhiskerLeft _ (eqToIso (hR h)) ≪≫ c h ≪≫
        Functor.isoWhiskerRight
          (NatIso.prod (eqToIso (hR h)).symm (eqToIso (hR h)).symm) _) := by
  rcases S with ⟨T, b, hb⟩
  have hT : @T = @R := by funext i j h; exact hR h
  cases hT
  have hB : @b = @a := by funext i j k h k; exact eq_of_heq (ha h k)
  cases hB
  unfold BilinearCoefficientDescent.FamilyTower
  intro i j k h hjk X Y
  have ht := tower h hjk
  unfold TensorTowerDatum.Coherent at ht
  simpa [NatIso.prod, NatTrans.prod] using ht X Y

end CategoryTheory.BilinearCoefficientDescent
