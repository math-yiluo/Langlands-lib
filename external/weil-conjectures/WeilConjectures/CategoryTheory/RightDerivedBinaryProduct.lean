/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Binary products of additive functors to abelian groups

Source: Stacks Project, Homology Tag 0117, and the componentwise description of
cycles and boundaries for finite products.
(blueprint: lem-weil-pbc-right-derived-binary-product)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The concrete pointwise product of two abelian-group-valued functors. -/
def abBinaryProduct (B D : C ⥤ AddCommGrpCat.{w}) : C ⥤ AddCommGrpCat.{w} where
  obj M := AddCommGrpCat.of (B.obj M × D.obj M)
  map f := AddCommGrpCat.ofHom ((B.map f).hom.prodMap (D.map f).hom)

instance (B D : C ⥤ AddCommGrpCat.{w}) [Preadditive C] [B.Additive] [D.Additive] :
    (abBinaryProduct B D).Additive where
  map_add {X Y} f g := by
    ext x
    simp [abBinaryProduct, Functor.map_add, Prod.ext_iff]

/-- The pair of two transformations, valued in the concrete pointwise product. -/
def abBinaryProductLift {A B D : C ⥤ AddCommGrpCat.{w}} (a : A ⟶ B) (b : A ⟶ D) :
    A ⟶ abBinaryProduct B D where
  app M := AddCommGrpCat.ofHom ((a.app M).hom.prod (b.app M).hom)
  naturality M N f := by
    ext x
    exact Prod.ext (ConcreteCategory.congr_hom (a.naturality f) x)
      (ConcreteCategory.congr_hom (b.naturality f) x)

/-- The difference of two transformations on the concrete pointwise product. -/
def abBinaryProductDifference {B D E : C ⥤ AddCommGrpCat.{w}}
    (c : B ⟶ E) (d : D ⟶ E) : abBinaryProduct B D ⟶ E where
  app M := AddCommGrpCat.ofHom
    ((c.app M).hom.comp (AddMonoidHom.fst _ _) -
      (d.app M).hom.comp (AddMonoidHom.snd _ _))
  naturality M N f := by
    ext x
    change c.app N (B.map f x.1) - d.app N (D.map f x.2) =
      E.map f (c.app M x.1 - d.app M x.2)
    rw [map_sub]
    exact congrArg₂ (· - ·) (ConcreteCategory.congr_hom (c.naturality f) x.1)
      (ConcreteCategory.congr_hom (d.naturality f) x.2)

/-- First projection of the pointwise product. -/
def abBinaryProductFst (B D : C ⥤ AddCommGrpCat.{w}) : abBinaryProduct B D ⟶ B where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)

/-- Second projection of the pointwise product. -/
def abBinaryProductSnd (B D : C ⥤ AddCommGrpCat.{w}) : abBinaryProduct B D ⟶ D where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)

/-- First inclusion into the pointwise product. -/
def abBinaryProductInl (B D : C ⥤ AddCommGrpCat.{w}) : B ⟶ abBinaryProduct B D where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.inl _ _)
  naturality M N f := by
    ext x
    simp [abBinaryProduct]

/-- Second inclusion into the pointwise product. -/
def abBinaryProductInr (B D : C ⥤ AddCommGrpCat.{w}) : D ⟶ abBinaryProduct B D where
  app M := AddCommGrpCat.ofHom (AddMonoidHom.inr _ _)
  naturality M N f := by
    ext x
    simp [abBinaryProduct]

section
variable [Abelian C] [HasInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
private theorem derived_add {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]
    (α β : F ⟶ G) (M : C) (n : ℕ) :
    ((α + β).rightDerived n).app M = (α.rightDerived n).app M +
      (β.rightDerived n).app M := by
  let P := injectiveResolution M
  have hc : (NatTrans.mapHomologicalComplex (α + β) _).app P.cocomplex =
      (NatTrans.mapHomologicalComplex α _).app P.cocomplex +
        (NatTrans.mapHomologicalComplex β _).app P.cocomplex := by
    ext k
    rfl
  rw [P.rightDerived_app_eq (α + β) n, P.rightDerived_app_eq α n,
    P.rightDerived_app_eq β n, hc, Functor.map_add]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

private theorem derived_zero {F G : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive]
    (M : C) (n : ℕ) : ((0 : F ⟶ G).rightDerived n).app M = 0 := by
  let P := injectiveResolution M
  have hc : (NatTrans.mapHomologicalComplex (0 : F ⟶ G) _).app P.cocomplex = 0 := by
    ext k
    rfl
  rw [P.rightDerived_app_eq (0 : F ⟶ G) n, hc, Functor.map_zero, zero_comp, comp_zero]

end

/-- Source: Stacks Project, Homology Tag 0117, finite products in the injective-resolution
argument for Tag 0A50.
(blueprint: lem-weil-pbc-right-derived-binary-product)

Proof: Let P be the pointwise Cartesian product functor. Its two projections p,q
and inclusions i,j satisfy ip = id, iq = 0, jp = 0, jq = id, and pi + qj = id.
Right derivation preserves composition and identity. It also preserves addition and zero:
compute transformation components through isoRightDerivedObj and rightDerived_app_eq,
then use additivity of homology. Thus the five identities still hold after derivation.
The derived projections define a map to the Cartesian product, and the sum of the derived
inclusions defines its inverse. The five identities prove both inverse equations.
The pair map followed by either projection is a or b, so derivation gives the asserted
pair equation. The difference is pc + q(-d), so additivity and composition give the
asserted difference equation. No left exactness is required, including at degree zero;
zero functors and split sequences satisfy the same identities. -/
theorem rightDerived_binaryProduct_iso
    [Abelian C] [HasInjectiveResolutions C]
    (A B D E : C ⥤ AddCommGrpCat.{w})
    [A.Additive] [B.Additive] [D.Additive] [E.Additive]
    (a : A ⟶ B) (b : A ⟶ D) (c : B ⟶ E) (d : D ⟶ E)
    (M : C) (n : ℕ) :
    ∃ e : ((abBinaryProduct B D).rightDerived n).obj M ≅
        AddCommGrpCat.of ((B.rightDerived n).obj M × (D.rightDerived n).obj M),
      (∀ x, e.hom (((abBinaryProductLift a b).rightDerived n).app M x) =
        ((a.rightDerived n).app M x, (b.rightDerived n).app M x)) ∧
      (∀ x, ((abBinaryProductDifference c d).rightDerived n).app M x =
        (c.rightDerived n).app M (e.hom x).1 -
          (d.rightDerived n).app M (e.hom x).2) := by
  let P := abBinaryProduct B D
  let p := abBinaryProductFst B D
  let q := abBinaryProductSnd B D
  let i := abBinaryProductInl B D
  let j := abBinaryProductInr B D
  have ip : i ≫ p = 𝟙 B := by ext M x; rfl
  have iq : i ≫ q = 0 := by ext M x; rfl
  have jp : j ≫ p = 0 := by ext M x; rfl
  have jq : j ≫ q = 𝟙 D := by ext M x; rfl
  have total : p ≫ i + q ≫ j = 𝟙 P := by
    ext M x
    exact Prod.ext (add_zero _) (zero_add _)
  let r (F G : C ⥤ AddCommGrpCat.{w}) [F.Additive] [G.Additive] (α : F ⟶ G) :=
    (α.rightDerived n).app M
  have comp {F G H : C ⥤ AddCommGrpCat.{w}} [F.Additive] [G.Additive] [H.Additive]
      (α : F ⟶ G) (β : G ⟶ H) : r F H (α ≫ β) = r F G α ≫ r G H β := by
    simp [r]
  have id (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] : r F F (𝟙 F) = 𝟙 _ := by
    simp [r]
  have rip : r B P i ≫ r P B p = 𝟙 _ := by rw [← comp, ip, id]
  have riq : r B P i ≫ r P D q = 0 := by rw [← comp, iq]; exact derived_zero M n
  have rjp : r D P j ≫ r P B p = 0 := by rw [← comp, jp]; exact derived_zero M n
  have rjq : r D P j ≫ r P D q = 𝟙 _ := by rw [← comp, jq, id]
  have rtotal : r P B p ≫ r B P i + r P D q ≫ r D P j = 𝟙 _ := by
    rw [← comp, ← comp, ← derived_add, total]
    exact id P
  let h : (P.rightDerived n).obj M ⟶
      AddCommGrpCat.of ((B.rightDerived n).obj M × (D.rightDerived n).obj M) :=
    AddCommGrpCat.ofHom ((r P B p).hom.prod (r P D q).hom)
  let inv : AddCommGrpCat.of ((B.rightDerived n).obj M × (D.rightDerived n).obj M) ⟶
      (P.rightDerived n).obj M :=
    AddCommGrpCat.ofHom ((r B P i).hom.comp (AddMonoidHom.fst _ _) +
      (r D P j).hom.comp (AddMonoidHom.snd _ _))
  let e : (P.rightDerived n).obj M ≅
      AddCommGrpCat.of ((B.rightDerived n).obj M × (D.rightDerived n).obj M) :=
    { hom := h
      inv := inv
      hom_inv_id := by
        ext x
        exact ConcreteCategory.congr_hom rtotal x
      inv_hom_id := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        apply Prod.ext
        · change r P B p (r B P i x.1 + r D P j x.2) = x.1
          rw [map_add (r P B p).hom]
          have h₁ := ConcreteCategory.congr_hom rip x.1
          have h₂ := ConcreteCategory.congr_hom rjp x.2
          change r P B p (r B P i x.1) = x.1 at h₁
          change r P B p (r D P j x.2) = 0 at h₂
          rw [h₁, h₂, add_zero]
        · change r P D q (r B P i x.1 + r D P j x.2) = x.2
          rw [map_add (r P D q).hom]
          have h₁ := ConcreteCategory.congr_hom riq x.1
          have h₂ := ConcreteCategory.congr_hom rjq x.2
          change r P D q (r B P i x.1) = 0 at h₁
          change r P D q (r D P j x.2) = x.2 at h₂
          rw [h₁, h₂, zero_add] }
  refine ⟨e, ?_, ?_⟩
  · intro x
    have hp : abBinaryProductLift a b ≫ p = a := by ext M x; rfl
    have hq : abBinaryProductLift a b ≫ q = b := by ext M x; rfl
    apply Prod.ext
    · exact ConcreteCategory.congr_hom ((comp (abBinaryProductLift a b) p).symm.trans
        (congrArg (r A B) hp)) x
    · exact ConcreteCategory.congr_hom ((comp (abBinaryProductLift a b) q).symm.trans
        (congrArg (r A D) hq)) x
  · intro x
    have hd : abBinaryProductDifference c d = p ≫ c + q ≫ (-d) := by
      ext M x
      simp [abBinaryProductDifference, p, q, abBinaryProductFst,
        abBinaryProductSnd, sub_eq_add_neg]
    have hn : r D E (-d) = -r D E d := by
      have hh := derived_add d (-d) M n
      rw [add_neg_cancel, derived_zero] at hh
      exact eq_neg_of_add_eq_zero_right hh.symm
    rw [hd, derived_add]
    change (r P E (p ≫ c) + r P E (q ≫ (-d))) x = _
    rw [comp, comp, hn]
    change r B E c (r P B p x) + (-r D E d) (r P D q x) = _
    simp [e, h, r, sub_eq_add_neg]
    rfl

end CategoryTheory
