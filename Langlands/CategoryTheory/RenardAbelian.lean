import Mathlib.CategoryTheory.Abelian.Basic

/-! # Renard's seven abelian-category axioms and Mathlib's construction -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C]

/-- Renard A.VI.1, AB0--AB3*, with a fixed compatible choice of zero morphisms. -/
def AbelianAxiomsWithZero (z : HasZeroMorphisms C) : Prop :=
  letI := z
  HasZeroObject C ∧
    HasFiniteProducts C ∧
    HasFiniteCoproducts C ∧
    HasKernels C ∧
    HasCokernels C ∧
    IsNormalMonoCategory C ∧
    IsNormalEpiCategory C

/-- Renard's seven axioms, with zero-morphism data existentially packaged.
No additive structure on morphisms is an input. -/
def AbelianAxioms : Prop :=
  ∃ z : HasZeroMorphisms C, AbelianAxiomsWithZero C z

/-- AB0 supplies zero-morphism data; no global instance is installed. -/
theorem nonempty_zeroMorphisms_of_zeroObject [HasZeroObject C] :
    Nonempty (HasZeroMorphisms C) :=
  ⟨HasZeroObject.zeroMorphismsOfZeroObject⟩

/-- The zero-object construction agrees with any existing zero-morphism data. -/
theorem zeroMorphismsOfZeroObject_eq [HasZeroObject C] (z : HasZeroMorphisms C) :
    (HasZeroObject.zeroMorphismsOfZeroObject : HasZeroMorphisms C) = z :=
  Subsingleton.elim _ _

/-- The seven properties do not depend on the choice of compatible zero data. -/
theorem abelianAxiomsWithZero_iff (z z' : HasZeroMorphisms C) :
    AbelianAxiomsWithZero C z ↔ AbelianAxiomsWithZero C z' := by
  cases Subsingleton.elim z z'
  rfl

/-- Unpack the existential using the category's existing zero morphisms. -/
theorem abelianAxioms_iff_withZero (z : HasZeroMorphisms C) :
    AbelianAxioms C ↔ AbelianAxiomsWithZero C z := by
  constructor
  · rintro ⟨z', h⟩
    exact (abelianAxiomsWithZero_iff C z' z).mp h
  · exact fun h => ⟨z, h⟩

namespace AbelianAxiomsWithZero

variable {C} {z : HasZeroMorphisms C}

/-- Assemble the actual nonpreadditive abelian structure from the seven axioms. -/
@[instance_reducible]
def nonPreadditiveAbelian (h : AbelianAxiomsWithZero C z) :
    NonPreadditiveAbelian C := by
  letI := z
  exact
    { toHasZeroMorphisms := z
      has_zero_object := h.1
      has_finite_products := h.2.1
      has_finite_coproducts := h.2.2.1
      has_kernels := h.2.2.2.1
      has_cokernels := h.2.2.2.2.1
      toIsNormalMonoCategory := h.2.2.2.2.2.1
      toIsNormalEpiCategory := h.2.2.2.2.2.2 }

/-- The constructor retains the supplied zero data definitionally. -/
@[simp]
theorem nonPreadditiveAbelian_zero (h : AbelianAxiomsWithZero C z) :
    h.nonPreadditiveAbelian.toHasZeroMorphisms = z := rfl

/-- AB3 provides an actual kernel witness for each monomorphism. -/
@[instance_reducible]
def normalMono (h : AbelianAxiomsWithZero C z) {X Y : C} (f : X ⟶ Y) [Mono f] :
    letI := z
    NormalMono f := by
  letI := z
  letI : IsNormalMonoCategory C := h.2.2.2.2.2.1
  exact normalMonoOfMono f

/-- AB3* provides an actual cokernel witness for each epimorphism. -/
@[instance_reducible]
def normalEpi (h : AbelianAxiomsWithZero C z) {X Y : C} (f : X ⟶ Y) [Epi f] :
    letI := z
    NormalEpi f := by
  letI := z
  letI : IsNormalEpiCategory C := h.2.2.2.2.2.2
  exact normalEpiOfEpi f

/-- Unpack all seven fields of an actual nonpreadditive abelian structure. -/
theorem ofNonPreadditiveAbelian (a : NonPreadditiveAbelian C) :
    AbelianAxiomsWithZero C a.toHasZeroMorphisms := by
  let := a
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- Wrapping and unwrapping retains the seven properties with the original zeros. -/
theorem ofNonPreadditiveAbelian_nonPreadditiveAbelian (h : AbelianAxiomsWithZero C z) :
    ofNonPreadditiveAbelian h.nonPreadditiveAbelian = h := rfl

end AbelianAxiomsWithZero

namespace AbelianAxioms

variable {C}

/-- Package the fields of an existing nonpreadditive abelian structure. -/
theorem ofNonPreadditiveAbelian (a : NonPreadditiveAbelian C) : AbelianAxioms C :=
  ⟨a.toHasZeroMorphisms, AbelianAxiomsWithZero.ofNonPreadditiveAbelian a⟩

/-- Select the uniquely compatible zero data and assemble the actual structure. -/
@[instance_reducible]
def nonPreadditiveAbelian (h : AbelianAxioms C) : NonPreadditiveAbelian C :=
  h.choose_spec.nonPreadditiveAbelian

/-- Construct addition and additive inverses on the unchanged Hom types using Mathlib. -/
@[instance_reducible]
def preadditive (h : AbelianAxioms C) : Preadditive C :=
  letI := h.nonPreadditiveAbelian
  NonPreadditiveAbelian.preadditive

/-- Promote the source axioms to an actual abelian structure on the same category. -/
@[instance_reducible]
def abelian (h : AbelianAxioms C) : Abelian C :=
  letI := h.nonPreadditiveAbelian
  NonPreadditiveAbelian.abelian C

/-- Enter from an ordinary abelian category via Mathlib's reverse conversion. -/
theorem ofAbelian [Abelian C] : AbelianAxioms C :=
  ofNonPreadditiveAbelian Abelian.nonPreadditiveAbelian

/-- The abelian constructor uses precisely the constructed preadditive structure. -/
@[simp]
theorem abelian_toPreadditive (h : AbelianAxioms C) :
    h.abelian.toPreadditive = h.preadditive := rfl

/-- Unwrapping a constructed structure recovers the source proposition. -/
theorem ofNonPreadditiveAbelian_nonPreadditiveAbelian (h : AbelianAxioms C) :
    ofNonPreadditiveAbelian h.nonPreadditiveAbelian = h := rfl

/-- Any ambient preadditive structure agrees with the constructed one. -/
theorem preadditive_eq (h : AbelianAxioms C) (p : Preadditive C) :
    h.preadditive = p := by
  let a := h.abelian
  let z := @Preadditive.preadditiveHasZeroMorphisms C _ a.toPreadditive
  let b := @Abelian.hasBinaryBiproducts C _ a
  exact (@subsingleton_preadditive_of_hasBinaryBiproducts C _ z b).elim _ _

/-- The additive commutative group on each Hom in A.VI.2(6). -/
@[instance_reducible]
def homGroup (h : AbelianAxioms C) (X Y : C) : AddCommGroup (X ⟶ Y) :=
  h.preadditive.homGroup X Y

/-- The neutral element of the constructed Hom group is the existing categorical zero. -/
theorem homGroup_zero (h : AbelianAxioms C) (z : HasZeroMorphisms C) (X Y : C) :
    (h.homGroup X Y).zero = (z.zero X Y).zero := by
  have hz : @Preadditive.preadditiveHasZeroMorphisms C _ h.preadditive = z :=
    Subsingleton.elim _ _
  exact congrArg (fun w : HasZeroMorphisms C => (w.zero X Y).zero) hz

/-- Composition distributes over addition in its first variable. -/
theorem add_comp (h : AbelianAxioms C) {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    letI := h.preadditive
    (f + f') ≫ g = f ≫ g + f' ≫ g := by
  let := h.preadditive
  exact Preadditive.add_comp X Y Z f f' g

/-- Composition distributes over addition in its second variable. -/
theorem comp_add (h : AbelianAxioms C) {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    letI := h.preadditive
    f ≫ (g + g') = f ≫ g + f ≫ g' := by
  let := h.preadditive
  exact Preadditive.comp_add X Y Z f g g'

end AbelianAxioms

/-- The explicit source interface is equivalent to existence of Mathlib's nonadditive input. -/
theorem abelianAxioms_iff_nonempty_nonPreadditiveAbelian :
    AbelianAxioms C ↔ Nonempty (NonPreadditiveAbelian C) :=
  ⟨fun h => ⟨h.nonPreadditiveAbelian⟩,
    fun ⟨a⟩ => AbelianAxioms.ofNonPreadditiveAbelian a⟩

/-- Intrinsic correspondence with Mathlib's data-bearing abelian structure. -/
theorem abelianAxioms_iff_nonempty_abelian :
    AbelianAxioms C ↔ Nonempty (Abelian C) := by
  constructor
  · exact fun h => ⟨h.abelian⟩
  · rintro ⟨a⟩
    let := a
    exact AbelianAxioms.ofAbelian

end Langlands.Renard
