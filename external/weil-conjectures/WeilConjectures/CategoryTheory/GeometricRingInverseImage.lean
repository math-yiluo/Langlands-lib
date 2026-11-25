/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import WeilConjectures.CategoryTheory.InverseImageRingFunctor
import WeilConjectures.CategoryTheory.RouteInverseImageConstantComparison

/-! # Ring transport along a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tag 03D2.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u w uC vC uD vD
open CategoryTheory
namespace SheafOfModules
/-- The ring-only part of algebraic inverse image, specified on arbitrary generalized
sections. It includes no module functor or module operation.
Source: Stacks Project, Sites, Tag 00YV (rings as algebraic objects).
(auxiliary; not a blueprint node). -/
structure RingInverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (R : Sheaf JC CommRingCat.{w})
    (RI : Sheaf JD CommRingCat.{w}) where
  ringUnderlying : L.obj ((sheafCompose JC
      (CategoryTheory.forget CommRingCat.{w})).obj R) ≅
    (sheafCompose JD (CategoryTheory.forget CommRingCat.{w})).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1

end SheafOfModules

namespace CategoryTheory.ConstantCompletion

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

/-- A binary operation graph is preserved by its product-comparison equation. -/
private theorem transport_binary
    {A B : Type*} [Category A] [Category B]
    [CartesianMonoidalCategory A] [CartesianMonoidalCategory B]
    (F : A ⥤ B) [PreservesFiniteProducts F]
    {X : A} {Y : B} (e : F.obj X ⟶ Y)
    (op : X ⊗ X ⟶ X) (op' : Y ⊗ Y ⟶ Y)
    (hop : F.map op ≫ e = (prodComparisonIso F X X).hom ≫ (e ⊗ₘ e) ≫ op')
    {T : A} (a b t : T ⟶ X) (ht : t = lift a b ≫ op) :
    F.map t ≫ e = lift (F.map a ≫ e) (F.map b ≫ e) ≫ op' := by
  have hp : F.map (lift a b) ≫ (prodComparisonIso F X X).hom ≫ (e ⊗ₘ e) =
      lift (F.map a ≫ e) (F.map b ≫ e) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, prodComparisonIso_hom,
        CartesianMonoidalCategory.prodComparison_fst_assoc, lift_fst]
      rw [← Category.assoc, ← F.map_comp, lift_fst]
    · simp only [Category.assoc, tensorHom_snd, prodComparisonIso_hom,
        CartesianMonoidalCategory.prodComparison_snd_assoc, lift_snd]
      rw [← Category.assoc, ← F.map_comp, lift_snd]
  rw [ht, F.map_comp, Category.assoc, hop]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ op') hp

/-- A constant operation graph is preserved by its terminal-comparison equation. -/
private theorem transport_constant
    {A B : Type*} [Category A] [Category B]
    [CartesianMonoidalCategory A] [CartesianMonoidalCategory B]
    (F : A ⥤ B) [PreservesFiniteProducts F]
    {X : A} {Y : B} (e : F.obj X ⟶ Y)
    (op : 𝟙_ A ⟶ X) (op' : 𝟙_ B ⟶ Y)
    (hop : F.map op ≫ e = (preservesTerminalIso F).hom ≫ op')
    {T : A} (a : T ⟶ X) (ha : a = toUnit T ≫ op) :
    F.map a ≫ e = toUnit (F.obj T) ≫ op' := by
  rw [ha, F.map_comp, Category.assoc, hop, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

/-- Coherent inverse image of ring sheaves, including the natural constant comparison.
Source: Stacks Project, Sites, Tag 00YV (ring objects and constant objects), and
Modules on Sites, Tag 03D2.
(auxiliary; not a blueprint node).

Proof: identify a ring sheaf with a commutative ring object in the category of set
sheaves. Apply L to its underlying object and every operation, using the inverse
finite-product comparisons for binary operations and the inverse terminal comparison
for zero and one. The ring identities follow by applying L to their finite-product
identity diagrams. On a ring morphism use L of its underlying morphism; the operation
comparison equations show this is a ring morphism. The underlying maps then satisfy
the displayed naturality equation. Since L is a left adjoint preserving the terminal
object, it preserves coproducts of terminal objects. A constant set sheaf is such a
coproduct. The resulting natural constant-set isomorphism preserves every operation:
check on the summands indexed by the operands and use the product comparison.
It therefore lifts to the natural isomorphism of constant ring sheaves. The graph
identities follow by expressing each generalized operation as the universal operation
precomposed with the tuple of its operands. -/
theorem coherentRingInverseImage_exists
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] :
    ∃ (F : Sheaf J CommRingCat.{u} ⥤ Sheaf K CommRingCat.{u})
      (d : ∀ R : Sheaf J CommRingCat.{u}, SheafOfModules.RingInverseImage L R (F.obj R)),
      (∀ {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S),
        L.map ((sheafCompose J (forget CommRingCat)).map f) ≫ (d S).ringUnderlying.hom =
          (d R).ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat)).map (F.map f)) ∧
      Nonempty (constantSheaf J CommRingCat.{u} ⋙ F ≅ constantSheaf K CommRingCat.{u}) := by
  obtain ⟨F, _, _, e, _, hops, _⟩ := inverseImage_ring_functor J K adj
  let d : ∀ R : Sheaf J CommRingCat.{u}, CategoryTheory.RingInverseImage L R (F.obj R) :=
    fun R ↦
      { ringUnderlying := e.app R
        ringAdd := by
          intro T a b t ht W x
          have h : t = lift a b ≫ ringSheafAdd R := by
            ext U y
            exact ht U y
          exact congrArg (fun f ↦ f.hom.app W x)
            (transport_binary L (e.app R).hom _ _ (hops R).1 a b t h)
        ringMul := by
          intro T a b t ht W x
          have h : t = lift a b ≫ ringSheafMul R := by
            ext U y
            exact ht U y
          exact congrArg (fun f ↦ f.hom.app W x)
            (transport_binary L (e.app R).hom _ _ (hops R).2.1 a b t h)
        ringZero := by
          intro T a ha W x
          have h : a = toUnit T ≫ ringSheafZero R := by
            ext U y
            exact ha U y
          exact congrArg (fun f ↦ f.hom.app W x)
            (transport_constant L (e.app R).hom _ _ (hops R).2.2.1 a h)
        ringOne := by
          intro T a ha W x
          have h : a = toUnit T ≫ ringSheafOne R := by
            ext U y
            exact ha U y
          exact congrArg (fun f ↦ f.hom.app W x)
            (transport_constant L (e.app R).hom _ _ (hops R).2.2.2 a h) }
  have hn : ∀ {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S),
      L.map ((sheafCompose J (forget CommRingCat)).map f) ≫ (d S).ringUnderlying.hom =
        (d R).ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat)).map (F.map f) :=
    fun f ↦ e.hom.naturality f
  obtain ⟨constants, _, _⟩ := inverseImageConstantComparison J K L V adj
    inferInstance F d hn
  exact ⟨F, fun R ↦
    { ringUnderlying := (d R).ringUnderlying
      ringAdd := (d R).ringAdd
      ringMul := (d R).ringMul
      ringZero := (d R).ringZero
      ringOne := (d R).ringOne }, hn, ⟨constants⟩⟩

end CategoryTheory.ConstantCompletion
