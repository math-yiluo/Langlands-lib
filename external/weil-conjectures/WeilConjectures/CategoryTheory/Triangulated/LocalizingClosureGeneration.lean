/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.CategoryTheory.Triangulated.IdempotentCompleteOfCoproducts

/-!
# Formal properties of the localizing closure

Let `P` be a property of objects of a pretriangulated category `C` whose `Hom`-types live in
`Type v`, and `Loc(P)` its localizing closure (`CategoryTheory.ObjectProperty.localizingClosure`).

* If `C` has coproducts indexed by `Type v`, then `Loc(P)` is idempotent complete
  (`CategoryTheory.ObjectProperty.isIdempotentComplete_localizingClosure`, blueprint
  `lemma-hypotheses-brown-representability`).
* If `P` is stable under shifts, the objects of `P` detect zero objects of `Loc(P)`
  (`CategoryTheory.ObjectProperty.isZero_of_forall_eq_zero_localizingClosure`, blueprint
  `lemma-hypotheses-brown-representability`): the objects `M` with `Hom(M, Y⟦n⟧) = 0` for all `n`
  form a localizing subcategory.
* So, for `P` stable under shifts, `P` compactly generates `Loc(P)` as soon as it is essentially
  small and its objects are compact in `Loc(P)`
  (`CategoryTheory.ObjectProperty.CompactlyGeneratesLocalizingClosure.of_isStableUnderShift`).
* A triangulated functor `Φ : C₁ ⥤ C₂` mapping `P₁` into `Loc(P₂)`, whose restriction to
  `Loc(P₁)` preserves coproducts, maps `Loc(P₁)` into `Loc(P₂)`
  (`CategoryTheory.ObjectProperty.localizingClosure_obj_of_le`, the argument of blueprint
  `proposition-proper-direct-image-extension-zero`).
-/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits Pretriangulated Category ZeroObject

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- Blueprint `lemma-hypotheses-brown-representability`: the localizing closure of a property of
objects of a pretriangulated category with coproducts is idempotent complete. -/
theorem isIdempotentComplete_localizingClosure [HasCoproducts.{v} C] :
    IsIdempotentComplete P.localizingClosure.FullSubcategory :=
  Pretriangulated.isIdempotentComplete_of_hasCoproducts

/-- The objects isomorphic to a shift of a given object. -/
def shiftsOf (Y : C) : ObjectProperty C :=
  fun W ↦ ∃ n : ℤ, Nonempty (W ≅ Y⟦n⟧)

instance (Y : C) : (shiftsOf Y).IsStableUnderShift ℤ where
  isStableUnderShiftBy m := ⟨fun _ ⟨n, ⟨e⟩⟩ ↦
    ⟨n + m, ⟨(shiftFunctor C m).mapIso e ≪≫ ((shiftFunctorAdd C n m).app Y).symm⟩⟩⟩

/-- The left orthogonal of a property of objects is closed under coproducts. -/
instance isClosedUnderColimitsOfShape_discrete_leftOrthogonal (Q : ObjectProperty C)
    (J : Type*) : Q.leftOrthogonal.IsClosedUnderColimitsOfShape (Discrete J) where
  colimitsOfShape_le := fun _ ⟨h⟩ _ _ hW ↦
    h.isColimit.hom_ext fun j ↦ (h.prop_diag_obj j _ hW).trans comp_zero.symm

/-- The left orthogonal of a property of objects stable under shifts is localizing. -/
instance isLocalizing_leftOrthogonal (Q : ObjectProperty C) [Q.IsStableUnderShift ℤ] :
    Q.leftOrthogonal.IsLocalizing where
  isClosedUnderColimitsOfShape_discrete _ := inferInstance

variable {P}

/-- Blueprint `lemma-hypotheses-brown-representability`: if `P` is stable under shifts, an object
`Y` of `Loc(P)` without nonzero morphisms from the objects of `P` is zero. Indeed the objects `M`
with `Hom(M, Y⟦n⟧) = 0` for all `n` form a localizing subcategory containing `P`, hence `Y`. -/
theorem isZero_of_forall_eq_zero_localizingClosure [P.IsStableUnderShift ℤ]
    (Y : P.localizingClosure.FullSubcategory)
    (hY : ∀ X : P.localizingClosure.FullSubcategory, P X.obj → ∀ f : X ⟶ Y, f = 0) :
    IsZero Y := by
  have hP : P ≤ (shiftsOf Y.obj).leftOrthogonal := by
    rintro X hX W f ⟨n, ⟨e⟩⟩
    let adj := (shiftEquiv' C (-n) n (by simp)).toAdjunction
    have hX' : P (X⟦-n⟧) := P.le_shift (-n) X hX
    have h₀ := congrArg P.localizingClosure.ι.map
      (hY ⟨_, P.le_localizingClosure _ hX'⟩ hX' (homMk ((adj.homEquiv _ _).symm (f ≫ e.hom))))
    rw [Functor.map_zero, ι_map, homMk_hom] at h₀
    rw [← cancel_mono e.hom, zero_comp, ← (adj.homEquiv _ _).apply_symm_apply (f ≫ e.hom), h₀]
    simp [Adjunction.homEquiv_unit]
  have h := P.localizingClosure_le hP Y.obj Y.property (𝟙 Y.obj)
    ⟨0, ⟨(shiftFunctorZero C ℤ).symm.app Y.obj⟩⟩
  rw [IsZero.iff_id_eq_zero]
  exact P.localizingClosure.ι.map_injective (by simpa using h)

/-- If `P` is stable under shifts, then `P` compactly generates its localizing closure as soon as
it has a small set of isomorphism representatives and its objects are compact in `Loc(P)`
(blueprint `lemma-hypotheses-brown-representability`). -/
theorem CompactlyGeneratesLocalizingClosure.of_isStableUnderShift [P.IsStableUnderShift ℤ]
    (hsmall : ∃ (ι : Type v) (S : ι → C), (∀ i, P (S i)) ∧ ∀ X, P X → ∃ i, Nonempty (S i ≅ X))
    (hcompact : ∀ X : P.localizingClosure.FullSubcategory, P X.obj →
      BrownRepresentability.IsCompactObj X) :
    P.CompactlyGeneratesLocalizingClosure where
  exists_skeleton := hsmall
  isCompactObj := hcompact
  isZero_of_forall_eq_zero := isZero_of_forall_eq_zero_localizingClosure

end

section Map

variable {C₁ : Type u₁} [Category.{v} C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type u₂} [Category.{v} C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (Φ : C₁ ⥤ C₂) [Φ.CommShift ℤ]
  [Φ.IsTriangulated]

/-- The objects of `Loc(P₁)` which `Φ` maps into `Loc(P₂)`. -/
def localizingClosureInverseImage : ObjectProperty C₁ :=
  P₁.localizingClosure ⊓ P₂.localizingClosure.inverseImage Φ

omit [Φ.CommShift ℤ] [Φ.IsTriangulated] in
lemma localizingClosureInverseImage_iff (X : C₁) :
    localizingClosureInverseImage P₁ P₂ Φ X ↔
      P₁.localizingClosure X ∧ P₂.localizingClosure (Φ.obj X) :=
  Iff.rfl

omit [Φ.CommShift ℤ] [Φ.IsTriangulated] in
instance : (localizingClosureInverseImage P₁ P₂ Φ).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨P₁.localizingClosure.prop_of_iso e h.1,
    P₂.localizingClosure.prop_of_iso (Φ.mapIso e) h.2⟩

/-- If the restriction of the triangulated functor `Φ` to `Loc(P₁)` preserves coproducts, the
objects of `Loc(P₁)` which `Φ` maps into `Loc(P₂)` form a localizing subcategory. -/
instance isLocalizing_localizingClosureInverseImage
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) (P₁.localizingClosure.ι ⋙ Φ)] :
    (localizingClosureInverseImage P₁ P₂ Φ).IsLocalizing where
  exists_zero := ⟨0, isZero_zero C₁, P₁.localizingClosure.prop_of_isZero (isZero_zero C₁),
    P₂.localizingClosure.prop_of_isZero (Φ.map_isZero (isZero_zero C₁))⟩
  isStableUnderShiftBy n := ⟨fun X h ↦ ⟨P₁.localizingClosure.le_shift n X h.1,
    P₂.localizingClosure.prop_of_iso ((Φ.commShiftIso n).app X).symm
      (P₂.localizingClosure.le_shift n _ h.2)⟩⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    ⟨P₁.localizingClosure.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1,
      P₂.localizingClosure.ext_of_isTriangulatedClosed₂ _ (Φ.map_distinguished T hT) h₁.2 h₃.2⟩
  isClosedUnderColimitsOfShape_discrete J := ⟨fun X ⟨h⟩ ↦ by
    have hX : P₁.localizingClosure X :=
      P₁.localizingClosure.prop_of_isColimit h.isColimit fun j ↦ (h.prop_diag_obj j).1
    let F : Discrete J ⥤ P₁.localizingClosure.FullSubcategory :=
      P₁.localizingClosure.lift h.diag fun j ↦ (h.prop_diag_obj j).1
    let c : Cocone F :=
      { pt := ⟨X, hX⟩
        ι := { app j := homMk (h.ι.app j)
               naturality j j' f := by
                 obtain rfl : j = j' := Discrete.ext (Discrete.eq_of_hom f)
                 obtain rfl : f = 𝟙 j := Subsingleton.elim _ _
                 simp } }
    have hc : IsColimit c := isColimitOfReflects P₁.localizingClosure.ι
      (h.isColimit.ofIsoColimit (Cocone.ext (Iso.refl _) (by simp [c])))
    exact ⟨hX, P₂.localizingClosure.prop_of_isColimit
      (isColimitOfPreserves (P₁.localizingClosure.ι ⋙ Φ) hc) fun j ↦ (h.prop_diag_obj j).2⟩⟩

/-- The argument of blueprint `proposition-proper-direct-image-extension-zero` (its detailed node
`proposition-proper-direct-image-extension-zero`): let `Φ : C₁ ⥤ C₂` be a
triangulated functor mapping `P₁` into `Loc(P₂)`, whose restriction to `Loc(P₁)` preserves
coproducts. Then `Φ` maps `Loc(P₁)` into `Loc(P₂)`. -/
theorem localizingClosure_obj_of_le
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) (P₁.localizingClosure.ι ⋙ Φ)]
    (hΦ : ∀ X, P₁ X → P₂.localizingClosure (Φ.obj X)) (X : C₁)
    (hX : P₁.localizingClosure X) : P₂.localizingClosure (Φ.obj X) :=
  (P₁.localizingClosure_le (Q := localizingClosureInverseImage P₁ P₂ Φ)
    (fun Y hY ↦ ⟨P₁.le_localizingClosure Y hY, hΦ Y hY⟩) X hX).2

end Map

end CategoryTheory.ObjectProperty
