/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison

/-!
# Detecting dualizability along a jointly conservative family of monoidal functors

Let `C` be a braided monoidal closed category and `Gᵢ : C ⥤ Dᵢ` a family of monoidal functors to
braided monoidal closed categories which jointly reflect isomorphisms. If every `Gᵢ` commutes with
the internal homs out of `X` (the comparison maps `Gᵢ [X, -] ⟶ [Gᵢ X, Gᵢ -]` are isomorphisms) and
every `Gᵢ X` is dualizable, then `X` is dualizable
(`CategoryTheory.isDualizable_of_isDualizable_map`).

The proof uses the criterion
`CategoryTheory.MonoidalClosed.isDualizable_iff_isIso_ihomUnitTensorToIhom`:
`X` is dualizable if and only if `[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism, and `Gᵢ` carries this
map to the corresponding map for `Gᵢ X` up to isomorphisms
(`CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison`). This is the
abstract form of the statement that dualizability is local, for instance for a cover of a site.

Similarly, an object of a full monoidal closed subcategory which is dualizable in the ambient
braided monoidal closed category is dualizable in the subcategory
(`CategoryTheory.ObjectProperty.isDualizable_of_isDualizable_obj`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {ι : Type*} {D : ι → Type*} [∀ i, Category* (D i)] [∀ i, MonoidalCategory (D i)]
  [∀ i, BraidedCategory (D i)] [∀ i, MonoidalClosed (D i)]

/-- **Dualizability is detected by a jointly conservative family of monoidal functors commuting
with internal homs.** -/
theorem isDualizable_of_isDualizable_map (G : ∀ i, C ⥤ D i) [∀ i, (G i).Monoidal]
    (hG : ∀ ⦃Y Z : C⦄ (f : Y ⟶ Z), (∀ i, IsIso ((G i).map f)) → IsIso f) {X : C}
    [∀ i, IsIso (ihomComparison (G i) X)] (hX : ∀ i, IsDualizable ((G i).obj X)) :
    IsDualizable X := by
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom]
  refine hG _ fun i ↦ ?_
  have := (isDualizable_iff_isIso_ihomUnitTensorToIhom _).1 (hX i)
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom_of_ihomComparison (G i) X X

/-- **Dualizability in a full monoidal closed subcategory.** An object of a full subcategory,
stable under tensor products, the unit and internal homs, of a braided monoidal closed category,
which is dualizable in the ambient category, is dualizable in the subcategory: its dual is
`[X, 𝟙]`, which lies in the subcategory. -/
theorem ObjectProperty.isDualizable_of_isDualizable_obj (P : ObjectProperty C) [P.IsMonoidal]
    [P.IsMonoidalClosed] (X : P.FullSubcategory) (hX : IsDualizable X.obj) : IsDualizable X := by
  have := (isDualizable_iff_isIso_ihomUnitTensorToIhom X.obj).1 hX
  let Y : P.FullSubcategory := ⟨_, P.prop_ihom X.property P.prop_unit⟩
  let : ExactPairing (P.ι.obj Y) (P.ι.obj X) := exactPairingOfIsIso X.obj
  let : ExactPairing (P.ι.obj X) (P.ι.obj Y) := BraidedCategory.exactPairing_swap _ _
  exact ⟨{ rightDual := Y, exact := ExactPairing.ofFullyFaithful P.ι X Y }⟩

end CategoryTheory
