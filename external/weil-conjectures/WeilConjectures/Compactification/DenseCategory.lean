/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Compactification.StrictRefinement

/-!

# The category of dense compactifications

For a morphism `f : X ⟶ Y`, the dense compactifications of `f` together with the strict
refinements (blueprint `definition-compactification-refinement--3`) form a full subcategory
`AlgebraicGeometry.Compactification.DenseCategory f` of the category of compactifications with
strict refinements. When `f` is quasi-compact, every refinement out of a dense compactification
is strict, so this is also the full subcategory of `AlgebraicGeometry.Compactification.category`
on the dense compactifications.

## Main definitions

- `AlgebraicGeometry.Compactification.DenseCategory`: the category of dense compactifications
  of `f` with strict refinements;
- `AlgebraicGeometry.Compactification.DenseCategory.homMk`: a refinement between dense
  compactifications, as a morphism of `DenseCategory f`;
- `AlgebraicGeometry.Compactification.DenseCategory.inclusion`: the inclusion of the dense
  compactifications into all compactifications, which is fully faithful.

## Main results

- `AlgebraicGeometry.Compactification.refinement_common_dense` (blueprint
  `proposition-dense-compactifications-form-cofiltered-category--1`): the closure `inf c d` of the
  diagonal is a dense compactification and both projections are strict refinements;
- `AlgebraicGeometry.Compactification.exists_isDense_isStrict_refinement`: every finite
  nonempty family of compactifications has a common dense strict refinement;
- `AlgebraicGeometry.Compactification.DenseCategory.isThin` and
  `AlgebraicGeometry.Compactification.DenseCategory.isCofiltered`: the category of dense
  compactifications is a cofiltered preorder (blueprint
  `proposition-dense-compactifications-form-cofiltered-category--3`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section Inf

variable [QuasiCompact f]

/-- The closure of the diagonal is a dense compactification. -/
theorem isDense_inf (c d : Compactification f) : (inf c d).IsDense :=
  isSchemeTheoreticallyDominant_inf_i c d

/-- The first projection out of the closure of the diagonal is a strict refinement. -/
theorem isStrict_infFst (c d : Compactification f) : (infFst c d).IsStrict :=
  Refinement.isStrict_of_isSchemeTheoreticallyDominant (isSchemeTheoreticallyDominant_inf_i c d) _

/-- The second projection out of the closure of the diagonal is a strict refinement. -/
theorem isStrict_infSnd (c d : Compactification f) : (infSnd c d).IsStrict :=
  Refinement.isStrict_of_isSchemeTheoreticallyDominant (isSchemeTheoreticallyDominant_inf_i c d) _

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category--1`: The closure of the
diagonal is a common dense refinement.

For compactifications `c₁`, `c₂` of a quasi-compact `f`, the scheme-theoretic image `inf c₁ c₂`
of `X` in `c₁.Z ×_Y c₂.Z` is a dense compactification of `f`, and both projections are strict
refinements, i.e. `qₖ ∘ j = jₖ` and `qₖ⁻¹(jₖ(X)) = j(X)`. The finite family version is
`AlgebraicGeometry.Compactification.exists_isDense_isStrict_refinement`. -/
theorem refinement_common_dense (c₁ c₂ : Compactification f) :
    (inf c₁ c₂).IsDense ∧ (infFst c₁ c₂).IsStrict ∧ (infSnd c₁ c₂).IsStrict :=
  ⟨isDense_inf c₁ c₂, isStrict_infFst c₁ c₂, isStrict_infSnd c₁ c₂⟩

end Inf

variable (f) in
/-- Blueprint `definition-compactification-refinement--3`: the dense compactifications of `f` form a
full subcategory of the category of compactifications with strict refinements. -/
abbrev DenseCategory : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := StrictCategory f) fun c ↦ c.obj.IsDense

namespace DenseCategory

/-- A dense compactification, as an object of `DenseCategory f`. -/
abbrev mk (c : Compactification f) (hc : c.IsDense) : DenseCategory f :=
  ⟨⟨c⟩, hc⟩

/-- A refinement between dense compactifications of a quasi-compact morphism is a morphism of
`DenseCategory f`, being automatically strict. -/
def homMk [QuasiCompact f] {c d : DenseCategory f} (r : c.obj.obj.Refinement d.obj.obj) :
    c ⟶ d :=
  ObjectProperty.homMk ⟨r, Refinement.isStrict_of_isSchemeTheoreticallyDominant c.property r⟩

@[simp]
lemma homMk_hom_hom [QuasiCompact f] {c d : DenseCategory f}
    (r : c.obj.obj.Refinement d.obj.obj) : (homMk r).hom.hom = r :=
  rfl

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category--3`: there is at most
one morphism between two dense compactifications, by uniqueness of refinements out of a dense
compactification. -/
instance isThin : Quiver.IsThin (DenseCategory f) := fun c _ ↦
  ⟨fun r s ↦ ObjectProperty.hom_ext _ (WideSubcategory.hom_ext _
    (Refinement.ext_of_isSchemeTheoreticallyDominant c.property r.hom.hom s.hom.hom))⟩

variable (f) in
/-- The inclusion of the dense compactifications into all compactifications. -/
def inclusion : DenseCategory f ⥤ Compactification f :=
  ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _

instance [QuasiCompact f] : (inclusion f).Full where
  map_surjective r := ⟨homMk r, rfl⟩

instance : (inclusion f).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The category of dense compactifications of a quasi-compact morphism is cofiltered or
empty: two dense compactifications are refined by the closure of the diagonal, and parallel
morphisms are equal. -/
instance isCofilteredOrEmpty [QuasiCompact f] : IsCofilteredOrEmpty (DenseCategory f) where
  cone_objs c d := ⟨mk (inf c.obj.obj d.obj.obj) (isDense_inf _ _), homMk (infFst _ _),
    homMk (infSnd _ _), trivial⟩
  cone_maps c _ _ _ := ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-- A compactifiable quasi-compact morphism has a dense compactification. -/
instance nonempty [QuasiCompact f] [HasCompactification f] : Nonempty (DenseCategory f) :=
  HasCompactification.nonempty_compactification.map fun c ↦ mk (inf c c) (isDense_inf c c)

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category--3`: the category of
dense compactifications of a quasi-compact compactifiable morphism is cofiltered. -/
instance isCofiltered [QuasiCompact f] [HasCompactification f] :
    IsCofiltered (DenseCategory f) where

end DenseCategory

/-- Every finite nonempty family of compactifications of a quasi-compact morphism has a common
dense strict refinement (blueprint
`proposition-dense-compactifications-form-cofiltered-category--1`). -/
theorem exists_isDense_isStrict_refinement [QuasiCompact f] {ι : Type*} [Finite ι] [Nonempty ι]
    (c : ι → Compactification f) :
    ∃ e : Compactification f, e.IsDense ∧ ∀ i, ∃ r : e.Refinement (c i), r.IsStrict := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let c' : ι → DenseCategory f := fun i ↦ .mk (inf (c i) (c i)) (isDense_inf _ _)
  have : Nonempty (DenseCategory f) := ⟨c' (Classical.arbitrary ι)⟩
  have : IsCofiltered (DenseCategory f) := { }
  obtain ⟨e, he⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image c')
  refine ⟨e.obj.obj, e.property, fun i ↦ ?_⟩
  obtain ⟨r⟩ := he (Finset.mem_image_of_mem c' (Finset.mem_univ i))
  exact ⟨r.hom.hom.comp (infFst (c i) (c i)),
    Refinement.IsStrict.comp r.hom.property (isStrict_infFst _ _)⟩

/-- Blueprint `proposition-dense-compactifications-form-cofiltered-category--3`: The category of
dense compactifications is cofiltered.

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` separated, quasi-compact and
locally of finite type. The category of dense compactifications of `f` with the (strict)
refinements as morphisms is a cofiltered preorder. -/
theorem DenseCategory.isCofiltered_and_isThin [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsCofiltered (DenseCategory f) ∧ Quiver.IsThin (DenseCategory f) :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Compactification
