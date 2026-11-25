/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Opposites

/-! # Opposite stages and contravariant common-stage descent

The opposite of a stage system uses the inverse opposite associator. Reversing
finite-stage representatives identifies its pair category with the opposite of
the original pair category. This implements the representative construction in
blueprint `thm-coef-qbar-verdier`, proof steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v
open Opposite

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- Opposite stages, with the inverse opposite associator. -/
def opposite (S : StageSystem C) : StageSystem (fun i ↦ (C i)ᵒᵖ) where
  T h := (S.T h).op
  assoc h k := NatIso.op (S.assoc h k).symm
  cocycle h k m X := by
    apply Quiver.Hom.unop_inj
    exact S.cocycle_inv h k m X.unop

variable (S : StageSystem C)

/-- Reversing a representative commutes with further transport. -/
theorem opposite_transport {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {X : C i} {Y : C j}
    (f : (S.T hi).obj X ⟶ (S.T hj).obj Y) :
    (S.opposite.tr (hi := hj) (hj := hi) h f.op).unop = S.tr h f := by
  simp [tr, opposite, Category.assoc]

variable [IsDirectedOrder I]

/-- Reverse a pair into the opposite-stage system. -/
abbrev opPair (P : S.PairCategory) : S.opposite.PairCategory := ⟨P.stage, op P.obj⟩

/-- Reverse an ordinary pair arrow into the opposite-stage system. -/
def opPairHom {P Q : S.PairCategory} (f : P ⟶ Q) : S.opPair Q ⟶ S.opPair P :=
  Quotient.map
    (sa := PairCategory.Rep.setoid P Q)
    (sb := PairCategory.Rep.setoid (S.opPair Q) (S.opPair P))
    (fun r ↦ ⟨r.k, r.hY, r.hX, r.u.op⟩)
    (by
      rintro r s ⟨n, hr, hs, e⟩
      refine ⟨n, hr, hs, ?_⟩
      apply Quiver.Hom.unop_inj
      simpa [tr, opposite, Category.assoc] using e) f

/-- The inverse functor sends an opposite arrow to its opposite representative. -/
def pairUnopFunctor : S.PairCategoryᵒᵖ ⥤ S.opposite.PairCategory where
  obj P := S.opPair P.unop
  map f := S.opPairHom f.unop
  map_id P := by
    change S.opPairHom (𝟙 P.unop) = 𝟙 (S.opPair P.unop)
    rw [PairCategory.id_eq_mkHom P.unop le_rfl,
      PairCategory.id_eq_mkHom (S.opPair P.unop) le_rfl]
    rfl
  map_comp {P Q R} f g := by
    change S.opPairHom (g.unop ≫ f.unop) =
      S.opPairHom f.unop ≫ S.opPairHom g.unop
    obtain ⟨n, -, hR, hQ, hQ', hP, a, b, ha, hb⟩ :=
      PairCategory.exists_common_stage g.unop f.unop R.unop.stage
    rw [ha, hb, PairCategory.mkHom_comp_mkHom]
    change PairCategory.mkHom (X := S.opPair P.unop) (Y := S.opPair R.unop) n hP hR
        (a ≫ b).op =
      PairCategory.mkHom (X := S.opPair P.unop) (Y := S.opPair Q.unop) n hP hQ' b.op ≫
        PairCategory.mkHom (X := S.opPair Q.unop) (Y := S.opPair R.unop) n hQ hR a.op
    rw [PairCategory.mkHom_comp_mkHom]
    rfl

end CategoryTheory.StageSystem
