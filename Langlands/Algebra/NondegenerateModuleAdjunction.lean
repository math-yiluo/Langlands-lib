import Langlands.Algebra.NonUnitalModule
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual nondegenerate-part coreflection

Internal infrastructure derived from the largest-part property in Renard
I.1.2 and the adjunction definitions in A.V. The inclusion is left adjoint
to the already defined nondegenerate-part functor.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN

namespace NonUnitalModuleHom

variable {A : Type uA} {M : Type uM} {N : Type uN}
  [NonUnitalRing A] [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N]

/-- Every original map from a nondegenerate source lands in the actual part. -/
def factorNondegeneratePart (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A M (nondegeneratePart hA N) where
  toFun m := ⟨f m, by
    obtain ⟨e, he⟩ := hM m
    exact ⟨e, (f.map_smul e m).symm.trans (congrArg f he)⟩⟩
  map_zero' := Subtype.ext f.map_zero
  map_add' m n := Subtype.ext (f.map_add m n)
  map_smul' a m := Subtype.ext (f.map_smul a m)

@[simp] theorem factorNondegeneratePart_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (f : NonUnitalModuleHom A M N) (m : M) :
    (factorNondegeneratePart hA hM f m : N) = f m := rfl

@[simp] theorem subtype_comp_factorNondegeneratePart (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (f : NonUnitalModuleHom A M N) :
    (nondegeneratePart hA N).subtype.comp (factorNondegeneratePart hA hM f) = f := by
  ext m
  rfl

/-- The factorization is unique as an original additive intertwiner. -/
theorem factorNondegeneratePart_unique (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (f : NonUnitalModuleHom A M N)
    (g : NonUnitalModuleHom A M (nondegeneratePart hA N))
    (hg : (nondegeneratePart hA N).subtype.comp g = f) :
    g = factorNondegeneratePart hA hM f := by
  apply NonUnitalModuleHom.ext
  intro m
  apply Subtype.ext
  exact congrArg (fun k : NonUnitalModuleHom A M N => k m) hg

end NonUnitalModuleHom

variable {A : Type uA} [NonUnitalRing A]

/-- Restricting the codomain to the actual part, with inverse its inclusion. -/
def nondegeneratePartHomEquiv (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A) (Y : NonUnitalModuleCat.{uA, uM} A) :
    ((nondegenerateInclusion A).obj X ⟶ Y) ≃
      (X ⟶ (nondegeneratePartFunctor hA).obj Y) where
  toFun f := ObjectProperty.homMk
    (NonUnitalModuleHom.factorNondegeneratePart hA X.property f)
  invFun g := g.hom ≫ (nondegeneratePart hA Y).subtype
  left_inv f := by
    apply NonUnitalModuleHom.ext
    intro x
    rfl
  right_inv g := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro x
    apply Subtype.ext
    rfl

@[simp] theorem nondegeneratePartHomEquiv_apply (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A) (Y : NonUnitalModuleCat.{uA, uM} A)
    (f : (nondegenerateInclusion A).obj X ⟶ Y) (x : X.obj) :
    Subtype.val (((nondegeneratePartHomEquiv hA X Y) f).hom.toAddMonoidHom x) =
      f.toAddMonoidHom x := rfl

@[simp] theorem nondegeneratePartHomEquiv_symm_apply (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A) (Y : NonUnitalModuleCat.{uA, uM} A)
    (g : X ⟶ (nondegeneratePartFunctor hA).obj Y) (x : X.obj) :
    ((nondegeneratePartHomEquiv hA X Y).symm g).toAddMonoidHom x =
      Subtype.val (g.hom.toAddMonoidHom x) := rfl

/-- The inclusion of the actual full subcategory is left adjoint to its part functor. -/
def nondegeneratePartAdjunction (hA : IsIdempotented A) :
    nondegenerateInclusion.{uA, uM} A ⊣ nondegeneratePartFunctor hA :=
  Adjunction.mkOfHomEquiv
    { homEquiv := nondegeneratePartHomEquiv hA
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply NonUnitalModuleHom.ext
        intro x
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ObjectProperty.hom_ext
        apply NonUnitalModuleHom.ext
        intro x
        apply Subtype.ext
        rfl }

/-- The counit is exactly the published natural inclusion of the actual parts. -/
@[simp] theorem nondegeneratePartAdjunction_counit (hA : IsIdempotented A) :
    (nondegeneratePartAdjunction.{uA, uM} hA).counit =
      nondegeneratePartInclusion hA := by
  apply NatTrans.ext
  funext Y
  apply NonUnitalModuleHom.ext
  intro y
  rfl

/-- The unit sends each vector to itself in the actual nondegenerate part. -/
@[simp] theorem nondegeneratePartAdjunction_unit_apply (hA : IsIdempotented A)
    (X : NondegenerateModuleCat.{uA, uM} A) (x : X.obj) :
    Subtype.val (((nondegeneratePartAdjunction hA).unit.app X).hom.toAddMonoidHom x) = x := rfl

/-! Complete interfaces retain independent acting-ring and carrier universes. -/

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → IsNondegenerate A M →
    NonUnitalModuleHom A M N → NonUnitalModuleHom A M (nondegeneratePart hA N) :=
  @NonUnitalModuleHom.factorNondegeneratePart.{uA, uM, uN}

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (f : NonUnitalModuleHom A M N) → (m : M) →
    (NonUnitalModuleHom.factorNondegeneratePart hA hM f m : N) = f m :=
  @NonUnitalModuleHom.factorNondegeneratePart_apply.{uA, uM, uN}

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (f : NonUnitalModuleHom A M N) →
    (nondegeneratePart hA N).subtype.comp
      (NonUnitalModuleHom.factorNondegeneratePart hA hM f) = f :=
  @NonUnitalModuleHom.subtype_comp_factorNondegeneratePart.{uA, uM, uN}

example : {A : Type uA} → {M : Type uM} → {N : Type uN} →
    [NonUnitalRing A] → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (f : NonUnitalModuleHom A M N) →
    (g : NonUnitalModuleHom A M (nondegeneratePart hA N)) →
    (nondegeneratePart hA N).subtype.comp g = f →
    g = NonUnitalModuleHom.factorNondegeneratePart hA hM f :=
  @NonUnitalModuleHom.factorNondegeneratePart_unique.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{uA, uM} A) →
    (Y : NonUnitalModuleCat.{uA, uM} A) →
    (((nondegenerateInclusion A).obj X ⟶ Y) ≃
      (X ⟶ (nondegeneratePartFunctor hA).obj Y)) :=
  @nondegeneratePartHomEquiv.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{uA, uM} A) →
    (Y : NonUnitalModuleCat.{uA, uM} A) →
    (f : (nondegenerateInclusion A).obj X ⟶ Y) → (x : X.obj) →
    Subtype.val (((nondegeneratePartHomEquiv hA X Y) f).hom.toAddMonoidHom x) =
      f.toAddMonoidHom x :=
  @nondegeneratePartHomEquiv_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{uA, uM} A) →
    (Y : NonUnitalModuleCat.{uA, uM} A) →
    (g : X ⟶ (nondegeneratePartFunctor hA).obj Y) → (x : X.obj) →
    ((nondegeneratePartHomEquiv hA X Y).symm g).toAddMonoidHom x =
      Subtype.val (g.hom.toAddMonoidHom x) :=
  @nondegeneratePartHomEquiv_symm_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegenerateInclusion.{uA, uM} A ⊣ nondegeneratePartFunctor hA :=
  @nondegeneratePartAdjunction.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartAdjunction.{uA, uM} hA).counit =
      nondegeneratePartInclusion hA :=
  @nondegeneratePartAdjunction_counit.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{uA, uM} A) → (x : X.obj) →
    Subtype.val (((nondegeneratePartAdjunction hA).unit.app X).hom.toAddMonoidHom x) = x :=
  @nondegeneratePartAdjunction_unit_apply.{uA, uM}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegenerateInclusion.{0, 1} A ⊣ nondegeneratePartFunctor hA :=
  @nondegeneratePartAdjunction.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{0, 1} A) →
    (Y : NonUnitalModuleCat.{0, 1} A) →
    (((nondegenerateInclusion A).obj X ⟶ Y) ≃
      (X ⟶ (nondegeneratePartFunctor hA).obj Y)) :=
  @nondegeneratePartHomEquiv.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartAdjunction.{0, 1} hA).counit = nondegeneratePartInclusion hA :=
  @nondegeneratePartAdjunction_counit.{0, 1}

example : {A : Type} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{0, 1} A) → (x : X.obj) →
    Subtype.val (((nondegeneratePartAdjunction hA).unit.app X).hom.toAddMonoidHom x) = x :=
  @nondegeneratePartAdjunction_unit_apply.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    nondegenerateInclusion.{1, 0} A ⊣ nondegeneratePartFunctor hA :=
  @nondegeneratePartAdjunction.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{1, 0} A) →
    (Y : NonUnitalModuleCat.{1, 0} A) →
    (((nondegenerateInclusion A).obj X ⟶ Y) ≃
      (X ⟶ (nondegeneratePartFunctor hA).obj Y)) :=
  @nondegeneratePartHomEquiv.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (nondegeneratePartAdjunction.{1, 0} hA).counit = nondegeneratePartInclusion hA :=
  @nondegeneratePartAdjunction_counit.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (X : NondegenerateModuleCat.{1, 0} A) → (x : X.obj) →
    Subtype.val (((nondegeneratePartAdjunction hA).unit.app X).hom.toAddMonoidHom x) = x :=
  @nondegeneratePartAdjunction_unit_apply.{1, 0}

end Langlands.Algebra
