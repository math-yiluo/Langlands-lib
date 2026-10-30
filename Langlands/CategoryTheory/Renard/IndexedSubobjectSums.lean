import Langlands.CategoryTheory.RenardGrothendieckAxioms

/-!
# Renard A.VI.2: sums of indexed families of subobjects

Source: Renard, *Représentations des groupes réductifs p-adiques*
(French edition dated 9 July 2026), Appendix A.VI.2, printed page 263, the
remark after AB5: sums of subobjects exist because of AB4*.

For a family `F : I → Subobject X`, the sum is the image of the coproduct map
`Sigma.desc fun i => (F i).arrow : ∐ (fun i => (F i : C)) ⟶ X`. It is the least
upper bound of the family in Mathlib's existing order on `Subobject X`. The
construction needs only the coproduct of this family and the image of this map;
no well-poweredness, local smallness or complete-lattice structure is used.
The family universe `w`, the Hom universe `v` and the object universe `u` are
independent.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

section General

variable {C : Type u} [Category.{v} C] {X : C} {I : Type w} (F : I → Subobject X)

/-- The coproduct map of a family of subobjects: the morphism out of the
coproduct of the underlying objects whose restriction to the `i`-th summand is
the inclusion `(F i).arrow`. -/
abbrev subobjectSumDesc [HasCoproduct fun i => (F i : C)] : (∐ fun i => (F i : C)) ⟶ X :=
  Sigma.desc fun i => (F i).arrow

/-- The sum of an indexed family of subobjects: the subobject represented by the
image inclusion of the coproduct map `Sigma.desc fun i => (F i).arrow`. -/
def subobjectSum [HasCoproduct fun i => (F i : C)]
    [HasImage (Sigma.desc fun i => (F i).arrow)] : Subobject X :=
  Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow))

variable [HasCoproduct fun i => (F i : C)] [HasImage (subobjectSumDesc F)]

/-- The sum is, by definition, the image subobject of the coproduct map. -/
theorem subobjectSum_def :
    subobjectSum F = Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow)) :=
  rfl

/-- The object underlying the sum is isomorphic to the image of the coproduct map. -/
def subobjectSumIso : (subobjectSum F : C) ≅ image (subobjectSumDesc F) :=
  Subobject.underlyingIso (image.ι (subobjectSumDesc F))

/-- The representative isomorphism carries the image inclusion to the arrow of the sum. -/
@[reassoc (attr := simp)]
theorem subobjectSumIso_hom_comp_image_ι :
    (subobjectSumIso F).hom ≫ image.ι (subobjectSumDesc F) = (subobjectSum F).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

/-- The inverse representative isomorphism carries the arrow of the sum to the
image inclusion. -/
@[reassoc (attr := simp)]
theorem subobjectSumIso_inv_comp_arrow :
    (subobjectSumIso F).inv ≫ (subobjectSum F).arrow = image.ι (subobjectSumDesc F) :=
  Subobject.underlyingIso_arrow _

/-- The map from the coproduct onto the sum: the factorization of the coproduct
map through its image, followed by the representative isomorphism. -/
def subobjectSumπ : (∐ fun i => (F i : C)) ⟶ (subobjectSum F : C) :=
  factorThruImage (subobjectSumDesc F) ≫ (subobjectSumIso F).inv

/-- The map onto the sum, followed by the arrow of the sum, is the coproduct map. -/
@[reassoc (attr := simp)]
theorem subobjectSumπ_arrow :
    subobjectSumπ F ≫ (subobjectSum F).arrow = subobjectSumDesc F := by
  simp [subobjectSumπ]

/-- With equalizers, the map from the coproduct onto the sum is an epimorphism. -/
instance epi_subobjectSumπ [HasEqualizers C] : Epi (subobjectSumπ F) := by
  unfold subobjectSumπ
  infer_instance

/-- Every member of the family lies below the sum. -/
theorem le_subobjectSum (i : I) : F i ≤ subobjectSum F :=
  Subobject.le_of_comm (Sigma.ι (fun i => (F i : C)) i ≫ subobjectSumπ F) (by simp)

/-- The sum lies below every common upper bound of the family. -/
theorem subobjectSum_le {G : Subobject X} (h : ∀ i, F i ≤ G) : subobjectSum F ≤ G :=
  Subobject.le_of_comm
    ((subobjectSumIso F).hom ≫
      image.lift
        { I := (G : C)
          m := G.arrow
          e := Sigma.desc fun i => Subobject.ofLE (F i) G (h i)
          fac := by ext; simp })
    (by rw [Category.assoc, image.lift_fac, subobjectSumIso_hom_comp_image_ι])

/-- The sum lies below `G` exactly when every member of the family does. -/
theorem subobjectSum_le_iff {G : Subobject X} : subobjectSum F ≤ G ↔ ∀ i, F i ≤ G :=
  ⟨fun h i => (le_subobjectSum F i).trans h, subobjectSum_le F⟩

/-- The sum is the least upper bound of the members of the family. -/
theorem isLUB_subobjectSum : IsLUB (Set.range F) (subobjectSum F) :=
  ⟨by rintro _ ⟨i, rfl⟩; exact le_subobjectSum F i,
    fun _ hG => subobjectSum_le F fun i => hG ⟨i, rfl⟩⟩

/-- Any least upper bound of the members of the family is the sum. -/
theorem subobjectSum_eq_of_isLUB {U : Subobject X} (hU : IsLUB (Set.range F) U) :
    subobjectSum F = U :=
  (isLUB_subobjectSum F).unique hU

end General

/-- With images and `w`-indexed coproducts, every `w`-indexed family of
subobjects has a least upper bound, namely its sum `subobjectSum F`. -/
theorem hasIndexedSubobjectSums_of_hasImages {C : Type u} [Category.{v} C] [HasImages C] :
    HasCoproducts.{w} C → HasIndexedSubobjectSums.{w} C :=
  fun _ _ _ F => ⟨subobjectSum F, isLUB_subobjectSum F⟩

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard A.VI.2, remark after AB5: in an abelian category with `w`-indexed
coproducts (source AB4* at size `w`), every `w`-indexed family of subobjects,
including the empty family, has a sum. -/
theorem hasIndexedSubobjectSums_of_hasCoproducts :
    HasCoproducts.{w} C → HasIndexedSubobjectSums.{w} C :=
  hasIndexedSubobjectSums_of_hasImages

/-- The same statement for Renard's cocomplete abelian categories. -/
theorem IsSourceCocomplete.hasIndexedSubobjectSums (h : IsSourceCocomplete.{w} C) :
    HasIndexedSubobjectSums.{w} C :=
  hasIndexedSubobjectSums_of_hasCoproducts h

variable [HasCoproducts.{w} C] {X : C}

/-- In the abelian source setting the sum is the image subobject of the actual
coproduct map, with the instances found from `[Abelian C]` and
`[HasCoproducts.{w} C]`. -/
theorem subobjectSum_eq_mk {I : Type w} (F : I → Subobject X) :
    subobjectSum F = Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow)) :=
  rfl

/-- The sum of the empty family is the zero subobject. -/
theorem subobjectSum_eq_bot_of_isEmpty {I : Type w} [IsEmpty I] (F : I → Subobject X) :
    subobjectSum F = ⊥ := by
  have h := isLUB_subobjectSum F
  rw [Set.range_eq_empty F, isLUB_empty_iff] at h
  exact h.eq_bot

end Abelian

/-- Specialization `w = max u v`: since `Subobject X : Type (max u v)`, the
subtype of any set of subobjects is a family index of this size, and the sum
of that family is the least upper bound of the set.

The global hypothesis `HasCoproducts.{max u v} C` is degenerate: by Freyd's
Cantor argument it makes every Hom type a subsingleton, so in an abelian
category every object is zero. For nonzero applications use
`isLUB_subobjectSum` with the particular coproduct of the family at hand. -/
theorem isLUB_subobjectSum_set {C : Type u} [Category.{v} C] [HasImages C]
    [HasCoproducts.{max u v} C] {X : C} (s : Set (Subobject X)) :
    IsLUB s (subobjectSum fun P : s => (P : Subobject X)) := by
  simpa using isLUB_subobjectSum fun P : s => (P : Subobject X)

end

end Langlands.Renard
