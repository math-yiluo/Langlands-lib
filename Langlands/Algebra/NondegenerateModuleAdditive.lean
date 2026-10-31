import Langlands.Algebra.NonUnitalModuleAdditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the actual nondegenerate-part functor

Restriction preserves the published pointwise original Hom operations.
The full subcategory uses its inherited preadditive structure throughout.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN

namespace NonUnitalModuleHom

variable {A : Type uA} {M : Type uM} {N : Type uN}
  [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N]

@[simp] theorem restrictNondegeneratePart_zero (hA : IsIdempotented A) :
    (0 : NonUnitalModuleHom A M N).restrictNondegeneratePart hA = 0 := by
  apply NonUnitalModuleHom.ext
  intro m
  apply Subtype.ext
  rfl

@[simp] theorem restrictNondegeneratePart_add (hA : IsIdempotented A)
    (f g : NonUnitalModuleHom A M N) :
    (f + g).restrictNondegeneratePart hA =
      f.restrictNondegeneratePart hA + g.restrictNondegeneratePart hA := by
  apply NonUnitalModuleHom.ext
  intro m
  apply Subtype.ext
  rfl

@[simp] theorem restrictNondegeneratePart_neg (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) :
    (-f).restrictNondegeneratePart hA = -f.restrictNondegeneratePart hA := by
  apply NonUnitalModuleHom.ext
  intro m
  apply Subtype.ext
  rfl

/-- Restriction is an additive homomorphism on the original Hom groups. -/
def restrictNondegeneratePartAddHom (hA : IsIdempotented A) :
    NonUnitalModuleHom A M N →+
      NonUnitalModuleHom A (nondegeneratePart hA M) (nondegeneratePart hA N) where
  toFun f := f.restrictNondegeneratePart hA
  map_zero' := restrictNondegeneratePart_zero hA
  map_add' f g := restrictNondegeneratePart_add hA f g

@[simp] theorem restrictNondegeneratePartAddHom_apply (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) :
    restrictNondegeneratePartAddHom hA f = f.restrictNondegeneratePart hA := rfl

/-- The bundled Hom map has exactly the existing restriction as its function. -/
theorem coe_restrictNondegeneratePartAddHom (hA : IsIdempotented A) :
    ⇑(restrictNondegeneratePartAddHom (M := M) (N := N) hA) =
      fun f => f.restrictNondegeneratePart hA := rfl

end NonUnitalModuleHom

/-- The published inclusion is additive for the inherited Hom groups. -/
theorem nondegenerateInclusion_additive (A : Type uA) [NonUnitalRing A] :
    (nondegenerateInclusion.{uA, uM} A).Additive := inferInstance

variable {A : Type uA} [NonUnitalRing A]

/-- The actual part functor preserves the published pointwise sums. -/
instance nondegeneratePartFunctor_additive (hA : IsIdempotented A) :
    (nondegeneratePartFunctor.{uA, uM} hA).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact NonUnitalModuleHom.restrictNondegeneratePart_add hA f g

/-- No change of original morphism accompanies the categorical Hom map. -/
@[simp] theorem nondegeneratePartFunctor_map_hom (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegeneratePartFunctor hA).map f).hom = f.restrictNondegeneratePart hA := rfl

@[simp] theorem nondegeneratePartFunctor_map_zero (hA : IsIdempotented A)
    (M N : NonUnitalModuleCat.{uA, uM} A) :
    (nondegeneratePartFunctor hA).map (0 : M ⟶ N) = 0 :=
  (nondegeneratePartFunctor hA).map_zero M N

@[simp] theorem nondegeneratePartFunctor_map_add (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f g : M ⟶ N) :
    (nondegeneratePartFunctor hA).map (f + g) =
      (nondegeneratePartFunctor hA).map f + (nondegeneratePartFunctor hA).map g :=
  (nondegeneratePartFunctor hA).map_add

@[simp] theorem nondegeneratePartFunctor_map_neg (hA : IsIdempotented A)
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (nondegeneratePartFunctor hA).map (-f) = -(nondegeneratePartFunctor hA).map f :=
  (nondegeneratePartFunctor hA).map_neg

/-- The actual ambient composite inherits additivity by composition. -/
theorem nondegeneratePartComposite_additive (hA : IsIdempotented A) :
    (nondegeneratePartFunctor.{uA, uM} hA ⋙ nondegenerateInclusion A).Additive :=
  inferInstance

/-! Complete unapplied interfaces with independent universes. -/

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (NonUnitalModuleHom A M N →+
      NonUnitalModuleHom A (nondegeneratePart hA M) (nondegeneratePart hA N)) :=
  @NonUnitalModuleHom.restrictNondegeneratePartAddHom.{uA, uM, uN}

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    ⇑(NonUnitalModuleHom.restrictNondegeneratePartAddHom (M := M) (N := N) hA) =
      (fun f => f.restrictNondegeneratePart hA) :=
  @NonUnitalModuleHom.coe_restrictNondegeneratePartAddHom.{uA, uM, uN}

example : (A : Type uA) → [NonUnitalRing A] →
    (nondegenerateInclusion.{uA, uM} A).Additive :=
  @nondegenerateInclusion_additive.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{uA, uM} hA).Additive :=
  @nondegeneratePartFunctor_additive.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{uA, uM} hA ⋙ nondegenerateInclusion A).Additive :=
  @nondegeneratePartComposite_additive.{uA, uM}

example : (A : Type) → [NonUnitalRing A] →
    (nondegenerateInclusion.{0, 1} A).Additive :=
  @nondegenerateInclusion_additive.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{0, 1} hA).Additive :=
  @nondegeneratePartFunctor_additive.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{0, 1} hA ⋙ nondegenerateInclusion A).Additive :=
  @nondegeneratePartComposite_additive.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    (nondegenerateInclusion.{1, 0} A).Additive :=
  @nondegenerateInclusion_additive.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{1, 0} hA).Additive :=
  @nondegeneratePartFunctor_additive.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartFunctor.{1, 0} hA ⋙ nondegenerateInclusion A).Additive :=
  @nondegeneratePartComposite_additive.{1, 0}

example (hA : IsIdempotented A) :
    (nondegeneratePartFunctor.{uA, uM} hA ⋙ nondegenerateInclusion A).Additive :=
  inferInstance

end Langlands.Algebra
