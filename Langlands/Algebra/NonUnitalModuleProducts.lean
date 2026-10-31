import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coordinatewise products of original nonunital modules

These internal derived constructions keep the original actions and additive maps.
The unbundled action allows any index universe. The bundled index is in `Type`,
so its product carrier stays in its given universe. No nondegeneracy or
idempotentedness assumption is made.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory CategoryTheory.Limits

universe uA uM uI

namespace NonUnitalModule

/-- The original action on a dependent product is coordinatewise. -/
instance pi {A : Type uA} [NonUnitalRing A] {I : Type uI} (M : I → Type uM)
    [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)] :
    NonUnitalModule A (∀ i, M i) where
  smul a m i := a • m i
  smul_zero a := funext fun _ => smul_zero a
  smul_add a m n := funext fun i => smul_add a (m i) (n i)
  mul_smul a b m := funext fun i => mul_smul a b (m i)
  add_smul a b m := funext fun i => NonUnitalModule.add_smul a b (m i)
  zero_smul m := funext fun i => NonUnitalModule.zero_smul (m i)

end NonUnitalModule

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A] {I : Type}
  (M : I → NonUnitalModuleCat.{uA, uM} A)

/-- A base-small family has its actual function carrier, with the original actions. -/
abbrev concreteProduct : NonUnitalModuleCat.{uA, uM} A :=
  of A (∀ i, M i)

/-- Coordinate projection as an original additive intertwiner. -/
def concreteProductπ (i : I) : concreteProduct M ⟶ M i where
  toFun m := m i
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original map assembling a family of original maps. -/
def concreteProductLift {N : NonUnitalModuleCat.{uA, uM} A}
    (f : ∀ i, N ⟶ M i) : N ⟶ concreteProduct M where
  toFun n i := (f i).toAddMonoidHom n
  map_zero' := funext fun i => (f i).map_zero
  map_add' n n' := funext fun i => (f i).map_add n n'
  map_smul' a n := funext fun i => (f i).map_smul a n

@[simp] theorem concreteProduct_zero_apply (i : I) :
    (0 : concreteProduct M) i = 0 := rfl

@[simp] theorem concreteProduct_add_apply (m n : concreteProduct M) (i : I) :
    (m + n) i = m i + n i := rfl

@[simp] theorem concreteProduct_neg_apply (m : concreteProduct M) (i : I) :
    (-m) i = -m i := rfl

@[simp] theorem concreteProduct_smul_apply (a : A) (m : concreteProduct M) (i : I) :
    (a • m) i = a • m i := rfl

@[simp] theorem concreteProductπ_apply (i : I) (m : concreteProduct M) :
    (concreteProductπ M i).toAddMonoidHom m = m i := rfl

@[simp] theorem concreteProductLift_apply {N : NonUnitalModuleCat.{uA, uM} A}
    (f : ∀ i, N ⟶ M i) (n : N) (i : I) :
    (concreteProductLift M f).toAddMonoidHom n i = (f i).toAddMonoidHom n := rfl

@[simp] theorem concreteProductLift_π {N : NonUnitalModuleCat.{uA, uM} A}
    (f : ∀ i, N ⟶ M i) (i : I) :
    concreteProductLift M f ≫ concreteProductπ M i = f i := by
  apply NonUnitalModuleHom.ext
  intro n
  rfl

/-- Original maps into the product are determined by their coordinates. -/
theorem concreteProduct_hom_ext {N : NonUnitalModuleCat.{uA, uM} A}
    {f g : N ⟶ concreteProduct M}
    (h : ∀ i, f ≫ concreteProductπ M i = g ≫ concreteProductπ M i) : f = g := by
  apply NonUnitalModuleHom.ext
  intro n
  funext i
  exact congrArg (fun k : N ⟶ M i => k.toAddMonoidHom n) (h i)

@[simp] theorem concreteProductLift_eta {N : NonUnitalModuleCat.{uA, uM} A}
    (f : N ⟶ concreteProduct M) :
    concreteProductLift M (fun i => f ≫ concreteProductπ M i) = f := by
  apply concreteProduct_hom_ext M
  intro i
  exact concreteProductLift_π M _ i

/-- The universal lift is compatible with precomposition by an original map. -/
theorem concreteProductLift_comp {N P : NonUnitalModuleCat.{uA, uM} A}
    (g : P ⟶ N) (f : ∀ i, N ⟶ M i) :
    g ≫ concreteProductLift M f = concreteProductLift M (fun i => g ≫ f i) := by
  apply NonUnitalModuleHom.ext
  intro p
  rfl

/-- The actual product cone, with the original coordinate projections. -/
def concreteProductFan : Fan M :=
  Fan.mk (concreteProduct M) (concreteProductπ M)

/-- The coordinatewise product has Mathlib's categorical product universal property. -/
def concreteProductIsLimit : IsLimit (concreteProductFan M) :=
  Fan.IsLimit.mk _ (fun s => concreteProductLift M s.proj)
    (fun s i => concreteProductLift_π M s.proj i)
    (fun s _m hm => concreteProduct_hom_ext M (fun i => (hm i).trans
      (concreteProductLift_π M s.proj i).symm))

/-- Product existence furnished directly by the coordinatewise cone. -/
theorem concreteHasProduct : HasProduct M :=
  ⟨⟨concreteProductFan M, concreteProductIsLimit M⟩⟩

section Finite

variable [Finite I]

/-- Compare the selected finite product with the actual coordinatewise product. -/
noncomputable def productIsoConcrete : (∏ᶜ M) ≅ concreteProduct M :=
  (limit.isLimit (Discrete.functor M)).conePointUniqueUpToIso (concreteProductIsLimit M)

@[simp] theorem productIsoConcrete_hom_π (i : I) :
    (productIsoConcrete M).hom ≫ concreteProductπ M i = Pi.π M i := by
  exact (limit.isLimit (Discrete.functor M)).conePointUniqueUpToIso_hom_comp
    (concreteProductIsLimit M) (Discrete.mk i)

@[simp] theorem productIsoConcrete_inv_π (i : I) :
    (productIsoConcrete M).inv ≫ Pi.π M i = concreteProductπ M i := by
  exact (limit.isLimit (Discrete.functor M)).conePointUniqueUpToIso_inv_comp
    (concreteProductIsLimit M) (Discrete.mk i)

@[simp] theorem productIsoConcrete_lift {N : NonUnitalModuleCat.{uA, uM} A}
    (f : ∀ i, N ⟶ M i) :
    Pi.lift f ≫ (productIsoConcrete M).hom = concreteProductLift M f := by
  apply concreteProduct_hom_ext M
  intro i
  simp

end Finite

end NonUnitalModuleCat

/-! Complete unapplied construction interfaces, with independent ring and carrier universes. -/

example : {A : Type uA} → [NonUnitalRing A] → {I : Type uI} →
    (M : I → Type uM) → [∀ i, AddCommGroup (M i)] →
    [∀ i, NonUnitalModule A (M i)] → NonUnitalModule A (∀ i, M i) :=
  @NonUnitalModule.pi.{uA, uM, uI}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → NonUnitalModuleCat.{uA, uM} A :=
  @NonUnitalModuleCat.concreteProduct.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → (i : I) →
    (NonUnitalModuleCat.concreteProduct M ⟶ M i) :=
  @NonUnitalModuleCat.concreteProductπ.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N : NonUnitalModuleCat.{uA, uM} A} → (∀ i, N ⟶ M i) →
    (N ⟶ NonUnitalModuleCat.concreteProduct M) :=
  @NonUnitalModuleCat.concreteProductLift.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → (i : I) →
    (0 : NonUnitalModuleCat.concreteProduct M) i = 0 :=
  @NonUnitalModuleCat.concreteProduct_zero_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    (m n : NonUnitalModuleCat.concreteProduct M) → (i : I) →
    (m + n) i = m i + n i :=
  @NonUnitalModuleCat.concreteProduct_add_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    (m : NonUnitalModuleCat.concreteProduct M) → (i : I) → (-m) i = -m i :=
  @NonUnitalModuleCat.concreteProduct_neg_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    (a : A) → (m : NonUnitalModuleCat.concreteProduct M) → (i : I) →
    (a • m) i = a • m i :=
  @NonUnitalModuleCat.concreteProduct_smul_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    (i : I) → (m : NonUnitalModuleCat.concreteProduct M) →
    (NonUnitalModuleCat.concreteProductπ M i).toAddMonoidHom m = m i :=
  @NonUnitalModuleCat.concreteProductπ_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N : NonUnitalModuleCat.{uA, uM} A} →
    (f : ∀ i, N ⟶ M i) → (n : N) → (i : I) →
    (NonUnitalModuleCat.concreteProductLift M f).toAddMonoidHom n i =
      (f i).toAddMonoidHom n :=
  @NonUnitalModuleCat.concreteProductLift_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N : NonUnitalModuleCat.{uA, uM} A} → (f : ∀ i, N ⟶ M i) → (i : I) →
    NonUnitalModuleCat.concreteProductLift M f ≫
      NonUnitalModuleCat.concreteProductπ M i = f i :=
  @NonUnitalModuleCat.concreteProductLift_π.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N : NonUnitalModuleCat.{uA, uM} A} →
    {f g : N ⟶ NonUnitalModuleCat.concreteProduct M} →
    (∀ i, f ≫ NonUnitalModuleCat.concreteProductπ M i =
      g ≫ NonUnitalModuleCat.concreteProductπ M i) → f = g :=
  @NonUnitalModuleCat.concreteProduct_hom_ext.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N : NonUnitalModuleCat.{uA, uM} A} →
    (f : N ⟶ NonUnitalModuleCat.concreteProduct M) →
    NonUnitalModuleCat.concreteProductLift M
      (fun i => f ≫ NonUnitalModuleCat.concreteProductπ M i) = f :=
  @NonUnitalModuleCat.concreteProductLift_eta.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    {N P : NonUnitalModuleCat.{uA, uM} A} →
    (g : P ⟶ N) → (f : ∀ i, N ⟶ M i) →
    g ≫ NonUnitalModuleCat.concreteProductLift M f =
      NonUnitalModuleCat.concreteProductLift M (fun i => g ≫ f i) :=
  @NonUnitalModuleCat.concreteProductLift_comp.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → Fan M :=
  @NonUnitalModuleCat.concreteProductFan.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) →
    IsLimit (NonUnitalModuleCat.concreteProductFan M) :=
  @NonUnitalModuleCat.concreteProductIsLimit.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → HasProduct M :=
  @NonUnitalModuleCat.concreteHasProduct.{uA, uM}

noncomputable example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → [Finite I] →
    ((∏ᶜ M) ≅ NonUnitalModuleCat.concreteProduct M) :=
  @NonUnitalModuleCat.productIsoConcrete.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).hom ≫
      NonUnitalModuleCat.concreteProductπ M i = Pi.π M i :=
  @NonUnitalModuleCat.productIsoConcrete_hom_π.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).inv ≫ Pi.π M i =
      NonUnitalModuleCat.concreteProductπ M i :=
  @NonUnitalModuleCat.productIsoConcrete_inv_π.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{uA, uM} A) → [Finite I] →
    {N : NonUnitalModuleCat.{uA, uM} A} → (f : ∀ i, N ⟶ M i) →
    Pi.lift f ≫ (NonUnitalModuleCat.productIsoConcrete M).hom =
      NonUnitalModuleCat.concreteProductLift M f :=
  @NonUnitalModuleCat.productIsoConcrete_lift.{uA, uM}

example : {A : Type} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{0, 1} A) →
    IsLimit (NonUnitalModuleCat.concreteProductFan M) :=
  @NonUnitalModuleCat.concreteProductIsLimit.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{1, 0} A) →
    IsLimit (NonUnitalModuleCat.concreteProductFan M) :=
  @NonUnitalModuleCat.concreteProductIsLimit.{1, 0}

noncomputable example : {A : Type} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{0, 1} A) → [Finite I] →
    ((∏ᶜ M) ≅ NonUnitalModuleCat.concreteProduct M) :=
  @NonUnitalModuleCat.productIsoConcrete.{0, 1}

noncomputable example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{1, 0} A) → [Finite I] →
    ((∏ᶜ M) ≅ NonUnitalModuleCat.concreteProduct M) :=
  @NonUnitalModuleCat.productIsoConcrete.{1, 0}

example : {A : Type} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{0, 1} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).hom ≫
      NonUnitalModuleCat.concreteProductπ M i = Pi.π M i :=
  @NonUnitalModuleCat.productIsoConcrete_hom_π.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{1, 0} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).hom ≫
      NonUnitalModuleCat.concreteProductπ M i = Pi.π M i :=
  @NonUnitalModuleCat.productIsoConcrete_hom_π.{1, 0}

example : {A : Type} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{0, 1} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).inv ≫ Pi.π M i =
      NonUnitalModuleCat.concreteProductπ M i :=
  @NonUnitalModuleCat.productIsoConcrete_inv_π.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{1, 0} A) → [Finite I] → (i : I) →
    (NonUnitalModuleCat.productIsoConcrete M).inv ≫ Pi.π M i =
      NonUnitalModuleCat.concreteProductπ M i :=
  @NonUnitalModuleCat.productIsoConcrete_inv_π.{1, 0}

example : {A : Type} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{0, 1} A) → [Finite I] →
    {N : NonUnitalModuleCat.{0, 1} A} → (f : ∀ i, N ⟶ M i) →
    Pi.lift f ≫ (NonUnitalModuleCat.productIsoConcrete M).hom =
      NonUnitalModuleCat.concreteProductLift M f :=
  @NonUnitalModuleCat.productIsoConcrete_lift.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (M : I → NonUnitalModuleCat.{1, 0} A) → [Finite I] →
    {N : NonUnitalModuleCat.{1, 0} A} → (f : ∀ i, N ⟶ M i) →
    Pi.lift f ≫ (NonUnitalModuleCat.productIsoConcrete M).hom =
      NonUnitalModuleCat.concreteProductLift M f :=
  @NonUnitalModuleCat.productIsoConcrete_lift.{1, 0}

end Langlands.Algebra
