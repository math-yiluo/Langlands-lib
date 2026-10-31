import Langlands.Algebra.IntegerUnitizationCategory
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Pointwise additive structure on original nonunital modules

The additive operations are defined directly on the published intertwiners. The
published integer-unitization functors preserve them; their equivalence supplies
finite products without changing either the scalar or the carrier universe.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra

universe u v w x

namespace NonUnitalModuleHom

variable {A : Type u} {M : Type v} {N : Type w} {P : Type x}
  [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule A M] [NonUnitalModule A N] [NonUnitalModule A P]

/-- The zero additive map intertwines the original actions. -/
instance instZero : Zero (NonUnitalModuleHom A M N) where
  zero :=
    { toAddMonoidHom := 0
      map_smul' a m := by simp only [AddMonoidHom.zero_apply, smul_zero] }

/-- Addition of intertwiners is pointwise addition. -/
instance instAdd : Add (NonUnitalModuleHom A M N) where
  add f g :=
    { toAddMonoidHom := f.toAddMonoidHom + g.toAddMonoidHom
      map_smul' a m := by
        change f (a • m) + g (a • m) = a • (f m + g m)
        rw [map_smul, map_smul, smul_add] }

/-- Negation of an intertwiner is pointwise negation. -/
instance instNeg : Neg (NonUnitalModuleHom A M N) where
  neg f :=
    { toAddMonoidHom := -f.toAddMonoidHom
      map_smul' a m := by
        change -f (a • m) = a • (-f m)
        rw [map_smul, smul_neg] }

@[simp] theorem zero_apply (m : M) : (0 : NonUnitalModuleHom A M N) m = 0 := rfl

@[simp] theorem add_apply (f g : NonUnitalModuleHom A M N) (m : M) :
    (f + g) m = f m + g m := rfl

@[simp] theorem neg_apply (f : NonUnitalModuleHom A M N) (m : M) :
    (-f) m = -f m := rfl

@[simp] theorem toAddMonoidHom_zero :
    (0 : NonUnitalModuleHom A M N).toAddMonoidHom = 0 := rfl

@[simp] theorem toAddMonoidHom_add (f g : NonUnitalModuleHom A M N) :
    (f + g).toAddMonoidHom = f.toAddMonoidHom + g.toAddMonoidHom := rfl

@[simp] theorem toAddMonoidHom_neg (f : NonUnitalModuleHom A M N) :
    (-f).toAddMonoidHom = -f.toAddMonoidHom := rfl

/-- The pointwise abelian group, with independent scalar, source and target universes. -/
instance instAddCommGroup : AddCommGroup (NonUnitalModuleHom A M N) where
  add_assoc f g h := by ext m; exact add_assoc (f m) (g m) (h m)
  zero_add f := by ext m; exact zero_add (f m)
  add_zero f := by ext m; exact add_zero (f m)
  neg_add_cancel f := by ext m; exact neg_add_cancel (f m)
  add_comm f g := by ext m; exact add_comm (f m) (g m)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Forgetting the intertwining condition is an additive homomorphism. -/
def toAddMonoidHomAddHom : NonUnitalModuleHom A M N →+ (M →+ N) where
  toFun := toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem toAddMonoidHomAddHom_apply (f : NonUnitalModuleHom A M N) :
    toAddMonoidHomAddHom f = f.toAddMonoidHom := rfl

/-- Postcomposition distributes over sums of original intertwiners. -/
theorem comp_add (g : NonUnitalModuleHom A N P) (f f' : NonUnitalModuleHom A M N) :
    g.comp (f + f') = g.comp f + g.comp f' := by
  ext m
  exact g.map_add (f m) (f' m)

/-- Precomposition distributes over sums of original intertwiners. -/
theorem add_comp (g g' : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    (g + g').comp f = g.comp f + g'.comp f := by
  ext m
  rfl

end NonUnitalModuleHom

namespace NonUnitalModuleCat

variable (A : Type u) [NonUnitalRing A]

/-- The original category is preadditive with exactly its pointwise Hom groups. -/
instance preadditive : Preadditive (NonUnitalModuleCat.{u, v} A) where
  homGroup M N := inferInstanceAs (AddCommGroup (NonUnitalModuleHom A M N))
  add_comp _ _ _ f f' g := NonUnitalModuleHom.comp_add g f f'
  comp_add _ _ _ f g g' := NonUnitalModuleHom.add_comp g g' f

/-- The category's Hom group is definitionally the unbundled pointwise group. -/
theorem homGroup_eq (M N : NonUnitalModuleCat.{u, v} A) :
    (preadditive A).homGroup M N =
      NonUnitalModuleHom.instAddCommGroup (A := A) (M := M) (N := N) := rfl

end NonUnitalModuleCat

namespace IntegerUnitization

variable (A : Type u) [NonUnitalRing A]

/-- Extension keeps the entire underlying additive map. -/
@[simp] theorem extendMap_toAddMonoidHom {M N : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) :
    (extendMap A f).hom.toAddMonoidHom = f.toAddMonoidHom := rfl

@[simp] theorem extendMap_zero {M N : NonUnitalModuleCat.{u, v} A} :
    extendMap A (0 : NonUnitalModuleHom A M N) = 0 := by ext m; rfl

@[simp] theorem extendMap_add {M N : NonUnitalModuleCat.{u, v} A}
    (f g : NonUnitalModuleHom A M N) :
    extendMap A (f + g) = extendMap A f + extendMap A g := by ext m; rfl

@[simp] theorem extendMap_neg {M N : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) :
    extendMap A (-f) = -extendMap A f := by ext m; rfl

/-- The published extension functor is additive for the pointwise structure. -/
instance extendFunctor_additive : (extendFunctor.{u, v} A).Additive where
  map_add := extendMap_add A _ _

/-- Restriction keeps the entire underlying additive map. -/
@[simp] theorem restrictMap_toAddMonoidHom {M N : ModuleCat.{v} (Unitization ℤ A)}
    (f : M ⟶ N) : (restrictMap A f).toAddMonoidHom = f.hom.toAddMonoidHom := rfl

@[simp] theorem restrictMap_zero {M N : ModuleCat.{v} (Unitization ℤ A)} :
    restrictMap A (0 : M ⟶ N) = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem restrictMap_add {M N : ModuleCat.{v} (Unitization ℤ A)} (f g : M ⟶ N) :
    restrictMap A (f + g) = restrictMap A f + restrictMap A g := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem restrictMap_neg {M N : ModuleCat.{v} (Unitization ℤ A)} (f : M ⟶ N) :
    restrictMap A (-f) = -restrictMap A f := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- The published restriction functor is additive for the same pointwise structure. -/
instance restrictFunctor_additive : (restrictFunctor.{u, v} A).Additive where
  map_add := restrictMap_add A _ _

end IntegerUnitization

namespace NonUnitalModuleCat

variable (A : Type u) [NonUnitalRing A]

/-- Finite products transported from ordinary modules by the published equivalence. -/
instance hasFiniteProducts : HasFiniteProducts (NonUnitalModuleCat.{u, v} A) where
  out n := Adjunction.hasLimitsOfShape_of_equivalence
    (J := Discrete (Fin n)) (IntegerUnitization.extendFunctor.{u, v} A)

end NonUnitalModuleCat

/-! Complete unapplied interfaces and unequal-universe specializations. -/

example : {A : Type u} → {M : Type v} → {N : Type w} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    AddCommGroup (NonUnitalModuleHom A M N) := @NonUnitalModuleHom.instAddCommGroup.{u, v, w}

example : (A : Type u) → [NonUnitalRing A] →
    Preadditive (NonUnitalModuleCat.{u, v} A) := @NonUnitalModuleCat.preadditive.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    HasFiniteProducts (NonUnitalModuleCat.{u, v} A) :=
  @NonUnitalModuleCat.hasFiniteProducts.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    (IntegerUnitization.extendFunctor.{u, v} A).Additive :=
  @IntegerUnitization.extendFunctor_additive.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    (IntegerUnitization.restrictFunctor.{u, v} A).Additive :=
  @IntegerUnitization.restrictFunctor_additive.{u, v}

example : (A : Type) → [NonUnitalRing A] → Preadditive (NonUnitalModuleCat.{0, 1} A) :=
  @NonUnitalModuleCat.preadditive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] → Preadditive (NonUnitalModuleCat.{1, 0} A) :=
  @NonUnitalModuleCat.preadditive.{1, 0}

example : (A : Type) → [NonUnitalRing A] → HasFiniteProducts (NonUnitalModuleCat.{0, 1} A) :=
  @NonUnitalModuleCat.hasFiniteProducts.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] → HasFiniteProducts (NonUnitalModuleCat.{1, 0} A) :=
  @NonUnitalModuleCat.hasFiniteProducts.{1, 0}

example : (A : Type) → [NonUnitalRing A] →
    (IntegerUnitization.extendFunctor.{0, 1} A).Additive :=
  @IntegerUnitization.extendFunctor_additive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    (IntegerUnitization.extendFunctor.{1, 0} A).Additive :=
  @IntegerUnitization.extendFunctor_additive.{1, 0}

example : (A : Type) → [NonUnitalRing A] →
    (IntegerUnitization.restrictFunctor.{0, 1} A).Additive :=
  @IntegerUnitization.restrictFunctor_additive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    (IntegerUnitization.restrictFunctor.{1, 0} A).Additive :=
  @IntegerUnitization.restrictFunctor_additive.{1, 0}

example (A : Type u) [NonUnitalRing A] : Preadditive (NonUnitalModuleCat.{u, v} A) :=
  inferInstance

example (A : Type u) [NonUnitalRing A] : HasFiniteProducts (NonUnitalModuleCat.{u, v} A) :=
  inferInstance

example (A : Type u) [NonUnitalRing A] :
    (IntegerUnitization.extendFunctor.{u, v} A).Additive := inferInstance

example (A : Type u) [NonUnitalRing A] :
    (IntegerUnitization.restrictFunctor.{u, v} A).Additive := inferInstance

end Langlands.Algebra
