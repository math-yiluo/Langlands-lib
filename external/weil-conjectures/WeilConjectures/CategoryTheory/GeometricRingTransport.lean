/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Transporting a sheaf of rings through a geometric inverse image

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem binaryOperation_transport
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [CartesianMonoidalCategory C₀] [CartesianMonoidalCategory D₀]
    (L : C₀ ⥤ D₀) [PreservesFiniteProducts L]
    {X R : C₀} {Y S : D₀} (e₀ : X ≅ R) (e₁ : Y ≅ L.obj X) (e₂ : Y ≅ S)
    (a : X ⊗ X ⟶ X) (b : Y ⊗ Y ⟶ Y)
    (h : b ≫ e₁.hom = (e₁.hom ⊗ₘ e₁.hom) ≫
      (CartesianMonoidalCategory.prodComparisonIso L X X).inv ≫ L.map a) :
    let e := e₂.symm ≪≫ e₁ ≪≫ L.mapIso e₀
    L.map (CartesianMonoidalCategory.lift (prod.fst ≫ e₀.inv) (prod.snd ≫ e₀.inv) ≫
      a ≫ e₀.hom) =
      Limits.prodComparison L R R ≫ prod.map e.inv e.inv ≫
        (CartesianMonoidalCategory.lift (prod.fst ≫ e₂.inv) (prod.snd ≫ e₂.inv) ≫
          b ≫ e₂.hom) ≫ e.hom := by
  dsimp only
  let e := e₂.symm ≪≫ e₁ ≪≫ L.mapIso e₀
  have hk : L.map (CartesianMonoidalCategory.lift
        (prod.fst ≫ e₀.inv) (prod.snd ≫ e₀.inv)) =
      Limits.prodComparison L R R ≫ prod.map e.inv e.inv ≫
        CartesianMonoidalCategory.lift (prod.fst ≫ e₂.inv) (prod.snd ≫ e₂.inv) ≫
        (e₁.hom ⊗ₘ e₁.hom) ≫
          (CartesianMonoidalCategory.prodComparisonIso L X X).inv := by
    apply (cancel_mono (CartesianMonoidalCategory.prodComparisonIso L X X).hom).mp
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp only [Category.assoc,
        CartesianMonoidalCategory.prodComparisonIso_hom,
        CartesianMonoidalCategory.prodComparison_fst,
        CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst_assoc,
        prod.map_fst_assoc, Limits.prodComparison_fst_assoc,
        e, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
        Iso.hom_inv_id_assoc, ← L.map_comp,
        CartesianMonoidalCategory.lift_fst]
      simp only [Iso.inv_hom_id, Category.comp_id, L.map_comp]
    · simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp only [Category.assoc,
        CartesianMonoidalCategory.prodComparisonIso_hom,
        CartesianMonoidalCategory.prodComparison_snd,
        CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd_assoc,
        prod.map_snd_assoc, Limits.prodComparison_snd_assoc,
        e, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
        Iso.hom_inv_id_assoc, ← L.map_comp,
        CartesianMonoidalCategory.lift_snd]
      simp only [Iso.inv_hom_id, Category.comp_id, L.map_comp]
  rw [Functor.map_comp, Functor.map_comp, hk]
  simp only [Category.assoc]
  have hh := congrArg (fun f ↦ f ≫ L.map e₀.hom) h
  simp only [Category.assoc] at hh
  rw [← hh]
  simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]

private theorem binaryOperation_sections
    {C₀ : Type u} [Category.{u} C₀] {J₀ : GrothendieckTopology C₀}
    (R : Sheaf J₀ CommRingCat.{u}) (X : Sheaf J₀ (Type u))
    (e : X ≅ (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R)
    (a : X ⊗ X ⟶ X)
    (op : ∀ W : C₀ᵒᵖ, R.obj.obj W → R.obj.obj W → R.obj.obj W)
    (h : ∀ W x y, e.hom.hom.app W (a.hom.app W (x, y)) =
      op W (e.hom.hom.app W x) (e.hom.hom.app W y))
    (W : C₀ᵒᵖ)
    (p : ((sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R ⨯
      (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R).obj.obj W) :
    (CartesianMonoidalCategory.lift (prod.fst ≫ e.inv) (prod.snd ≫ e.inv) ≫
        a ≫ e.hom).hom.app W p =
      op W ((prod.fst : (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R ⨯
        (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R ⟶ _).hom.app W p)
        ((prod.snd : (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R ⨯
          (sheafCompose J₀ (CategoryTheory.forget CommRingCat.{u})).obj R ⟶ _).hom.app W p) := by
  change e.hom.hom.app W (a.hom.app W
    (e.inv.hom.app W ((prod.fst : _ ⟶ (sheafCompose J₀
      (CategoryTheory.forget CommRingCat.{u})).obj R).hom.app W p),
      e.inv.hom.app W ((prod.snd : _ ⟶ (sheafCompose J₀
      (CategoryTheory.forget CommRingCat.{u})).obj R).hom.app W p))) = _
  rw [h]
  have hi (r : R.obj.obj W) : e.hom.hom.app W (e.inv.hom.app W r) = r :=
    congrArg (fun f ↦ f.hom.app W r) e.inv_hom_id
  rw [hi, hi]

/-- Inverse image transports the ring operations through product comparisons.
Source: Stacks Project, Tag 03D2, `lemma-pullback-module`.
(auxiliary; not a blueprint node).

Proof: put U equal to the set sheaf underlying R. Define addition and multiplication
on L(U) by applying L to the corresponding operations on U and precomposing by
the inverses of its product comparisons. Define zero and one using its terminal
comparison, and negation by L of negation. Each ring identity is an equality of
maps out of a finite power of U. Product preservation and functoriality send it
to the same identity on L(U). Evaluate on each object of the target site to obtain
a commutative ring; naturality makes each restriction a ring homomorphism. The
underlying set presheaf is L(U), hence is a sheaf, giving A. The identity on the
underlying sheaf gives eR. The componentwise descriptions of addR, mulR, addA,
and mulA and the two transport equations follow from the construction. -/
theorem geometric_ring_transport
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (A : Sheaf K CommRingCat.{u}) (eR : ((sheafCompose K (CategoryTheory.forget
      CommRingCat.{u})).obj A) ≅ L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
      R))
      (addR mulR : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose
        J (CategoryTheory.forget CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget
        CommRingCat.{u})).obj R))
      (addA mulA : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose
        K (CategoryTheory.forget CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget
        CommRingCat.{u})).obj A)),
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        addR.hom.app W x = @Add.add (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        mulR.hom.app W x = @Mul.mul (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        addA.hom.app W x = @Add.add (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        mulA.hom.app W x = @Mul.mul (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      L.map addR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ addA ≫ eR.hom ∧
      L.map mulR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ mulA ≫ eR.hom := by
  obtain ⟨F, _, hF, _, _, _, hops⟩ :=
    CategoryTheory.sheavesAlgebraicStructuresRing_core.{u, u, u} J
  obtain ⟨FF, hFF, hFFops⟩ := CategoryTheory.Adjunction.finiteProductRingFunctor L
  let X := F.obj R
  let Y := FF.obj X
  obtain ⟨A, hA, hAops⟩ :=
    CategoryTheory.sheafRingObject_sectionwise_reconstruction.{u, u, u} K Y
  let e₀ : X.X ≅ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R :=
    (eqToIso hF).app R
  let e₁ : Y.X ≅ L.obj X.X := (eqToIso hFF).app X
  let e₂ : Y.X ≅ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A :=
    eqToIso hA
  let addR := CartesianMonoidalCategory.lift (prod.fst ≫ e₀.inv) (prod.snd ≫ e₀.inv) ≫
    AddMonObj.add (X := X.X) ≫ e₀.hom
  let mulR := CartesianMonoidalCategory.lift (prod.fst ≫ e₀.inv) (prod.snd ≫ e₀.inv) ≫
    MonObj.mul (X := X.X) ≫ e₀.hom
  let addA := CartesianMonoidalCategory.lift (prod.fst ≫ e₂.inv) (prod.snd ≫ e₂.inv) ≫
    AddMonObj.add (X := Y.X) ≫ e₂.hom
  let mulA := CartesianMonoidalCategory.lift (prod.fst ≫ e₂.inv) (prod.snd ≫ e₂.inv) ≫
    MonObj.mul (X := Y.X) ≫ e₂.hom
  refine ⟨A, e₂.symm ≪≫ e₁ ≪≫ L.mapIso e₀, addR, mulR, addA, mulA,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact binaryOperation_sections R X.X e₀ _ (fun _ a b ↦ a + b)
      (fun W ↦ (hops R W).1)
  · exact binaryOperation_sections R X.X e₀ _ (fun _ a b ↦ a * b)
      (fun W ↦ (hops R W).2.2.2.1)
  · exact binaryOperation_sections A Y.X e₂ _ (fun _ a b ↦ a + b)
      (fun W ↦ (hAops W).1)
  · exact binaryOperation_sections A Y.X e₂ _ (fun _ a b ↦ a * b)
      (fun W ↦ (hAops W).2.2.2.1)
  · exact binaryOperation_transport L e₀ e₁ e₂ _ _ (hFFops X).1
  · exact binaryOperation_transport L e₀ e₁ e₂ _ _ (hFFops X).2.2.2.1

end SheafOfModules
