/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The iso locus of a natural transformation of contravariant functors

Let `C` be a pretriangulated category and `κ : S ⟶ T` a natural transformation of functors
`Cᵒᵖ ⥤ D` to a preadditive category, which need not be compatible with any shift. Suppose that
for every `T' : D` the functors `N ↦ (S N ⟶ T')` and `N ↦ (T N ⟶ T')` send distinguished
triangles of `C` to sequences which are exact in the middle
(`CategoryTheory.Functor.IsHomExact`). Then, by the five lemma, the objects `N` such that
`κ` is an isomorphism at all shifts `N⟦n⟧` form a triangulated subcategory of `C` closed under
retracts (`CategoryTheory.NatTrans.shiftIsoLocusOp`).

The exactness hypothesis holds as soon as `Hom(S N, T') ≅ Hom(A, F N)` naturally in `N`, for a
triangulated functor `F` (`CategoryTheory.Functor.IsHomExact.mk_of_homEquiv`): this is how the
contravariant variable of the Künneth–Verdier map is handled, without shifts.

## Main statements

- `CategoryTheory.NatTrans.isIso_app_obj₂_of_isHomExact`: the five lemma.
- `CategoryTheory.NatTrans.isTriangulated_shiftIsoLocusOp`: `κ.shiftIsoLocusOp` is triangulated.
- `CategoryTheory.NatTrans.isIso_app_op_of_triangEnvelope`: dévissage along a triangulated
  envelope.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Opposite Preadditive ObjectProperty ZeroObject

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace NatTrans

variable {S T : Cᵒᵖ ⥤ D}

/-- An isomorphism `N ≅ N'` transports the invertibility of `κ` at `N'` to `N`. -/
lemma isIso_app_op_of_iso (κ : S ⟶ T) {N N' : C} (e : N ≅ N') (h : IsIso (κ.app (op N'))) :
    IsIso (κ.app (op N)) :=
  κ.isoLocus.prop_of_iso e.op h

variable [HasShift C ℤ]

/-- The objects `N` such that `κ` is an isomorphism at every shift `N⟦n⟧`. -/
def shiftIsoLocusOp (κ : S ⟶ T) : ObjectProperty C :=
  fun N ↦ ∀ n : ℤ, IsIso (κ.app (op (N⟦n⟧)))

/-- Membership in `κ.shiftIsoLocusOp`. -/
lemma shiftIsoLocusOp_iff (κ : S ⟶ T) (N : C) :
    κ.shiftIsoLocusOp N ↔ ∀ n : ℤ, IsIso (κ.app (op (N⟦n⟧))) := Iff.rfl


/-- If `N` lies in `κ.shiftIsoLocusOp`, then `κ` is an isomorphism at the iterated shifts
`N⟦n⟧⟦m⟧`. -/
lemma isIso_app_op_shift_shift (κ : S ⟶ T) {N : C} (hN : κ.shiftIsoLocusOp N) (n m : ℤ) :
    IsIso (κ.app (op (N⟦n⟧⟦m⟧))) :=
  κ.isIso_app_op_of_iso ((shiftFunctorAdd C n m).app N).symm (hN (n + m))

instance isClosedUnderIsomorphisms_shiftIsoLocusOp (κ : S ⟶ T) :
    κ.shiftIsoLocusOp.IsClosedUnderIsomorphisms where
  of_iso e h n := κ.isIso_app_op_of_iso ((shiftFunctor C n).mapIso e.symm) (h n)

instance isStableUnderRetracts_shiftIsoLocusOp (κ : S ⟶ T) :
    κ.shiftIsoLocusOp.IsStableUnderRetracts where
  of_retract h hY n :=
    have := hY n
    κ.isIso_app_of_retract (h.map (shiftFunctor C n)).op

instance isStableUnderShift_shiftIsoLocusOp (κ : S ⟶ T) :
    κ.shiftIsoLocusOp.IsStableUnderShift ℤ where
  isStableUnderShiftBy a :=
    { le_shift N hN := by
        rw [prop_shift_iff]
        exact κ.isIso_app_op_shift_shift hN a }

end NatTrans

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D]

namespace Functor

/-- A functor `S : Cᵒᵖ ⥤ D` such that for every `T' : D`, the covariant functor
`N ↦ (S N ⟶ T')` sends every distinguished triangle `N₁ ⟶ N₂ ⟶ N₃ ⟶ N₁⟦1⟧` to a sequence
`(S N₁ ⟶ T') ⟶ (S N₂ ⟶ T') ⟶ (S N₃ ⟶ T')` which is exact in the middle. -/
class IsHomExact (S : Cᵒᵖ ⥤ D) : Prop where
  exact (T' : D) (Tr : Triangle C) (hTr : Tr ∈ distTriang C) (x : S.obj (op Tr.obj₂) ⟶ T')
    (hx : S.map Tr.mor₂.op ≫ x = 0) : ∃ y : S.obj (op Tr.obj₁) ⟶ T', S.map Tr.mor₁.op ≫ y = x

/-- If `Hom(S N, T') ≃ Hom(A_{T'}, F N)` naturally in `N` for a triangulated functor `F`, then `S`
satisfies `IsHomExact`: the functor `Hom(A_{T'}, F -)` is homological. -/
lemma IsHomExact.mk_of_homEquiv {C' : Type*} [Category* C'] [HasZeroObject C'] [HasShift C' ℤ]
    [Preadditive C'] [∀ n : ℤ, (shiftFunctor C' n).Additive] [Pretriangulated C']
    (S : Cᵒᵖ ⥤ D) [S.PreservesZeroMorphisms] (F : C ⥤ C') [F.CommShift ℤ] [F.IsTriangulated]
    (A : D → C') (e : ∀ (T' : D) (N : C), (A T' ⟶ F.obj N) ≃ (S.obj (op N) ⟶ T'))
    (he : ∀ (T' : D) {N N' : C} (f : N ⟶ N') (x : A T' ⟶ F.obj N),
      e T' N' (x ≫ F.map f) = S.map f.op ≫ e T' N x) :
    S.IsHomExact where
  exact T' Tr hTr x hx := by
    have h0 (N : C) : e T' N 0 = 0 := by
      have := he T' (0 : N ⟶ N) 0
      rw [zero_comp] at this
      rw [this, op_zero, S.map_zero, zero_comp]
    obtain ⟨x', rfl⟩ := (e T' Tr.obj₂).surjective x
    have hx' : x' ≫ F.map Tr.mor₂ = 0 := (e T' _).injective (by rw [he, hx, h0])
    obtain ⟨y', hy'⟩ := Triangle.coyoneda_exact₂ _ (F.map_distinguished Tr hTr) x' hx'
    exact ⟨e T' _ y', by rw [← he, hy']; rfl⟩

end Functor

namespace NatTrans

variable {S T : Cᵒᵖ ⥤ D}

/-- **The five lemma for a natural transformation of contravariant functors.** Let `κ : S ⟶ T`
with `S` and `T` satisfying `IsHomExact`. For a distinguished triangle `N₁ ⟶ N₂ ⟶ N₃ ⟶ N₁⟦1⟧`,
if `κ` is an isomorphism at `N₁`, `N₃`, `N₁⟦1⟧` and `N₃⟦-1⟧`, it is an isomorphism at `N₂`: for
every `T'`, the rows of
```
(S N₁⟦1⟧, T') ⟶ (S N₃, T') ⟶ (S N₂, T') ⟶ (S N₁, T') ⟶ (S N₃⟦-1⟧, T')
      ▲                ▲              ▲              ▲                 ▲
(T N₁⟦1⟧, T') ⟶ (T N₃, T') ⟶ (T N₂, T') ⟶ (T N₁, T') ⟶ (T N₃⟦-1⟧, T')
```
(the vertical maps precomposition with `κ`) are exact in the middle, so the five lemma applies. -/
lemma isIso_app_obj₂_of_isHomExact [S.PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
    [S.IsHomExact] [T.IsHomExact] (κ : S ⟶ T) (Tr : Triangle C) (hTr : Tr ∈ distTriang C)
    (h₁ : IsIso (κ.app (op Tr.obj₁))) (h₃ : IsIso (κ.app (op Tr.obj₃)))
    (h₁' : IsIso (κ.app (op (Tr.obj₁⟦(1 : ℤ)⟧))))
    (h₃' : IsIso (κ.app (op (Tr.obj₃⟦(-1 : ℤ)⟧)))) :
    IsIso (κ.app (op Tr.obj₂)) := by
  have nat {N N' : C} (f : N ⟶ N') :
      S.map f.op ≫ κ.app (op N) = κ.app (op N') ≫ T.map f.op := κ.naturality f.op
  obtain ⟨g, hg⟩ : ∃ g : Tr.obj₃⟦(-1 : ℤ)⟧ ⟶ Tr.obj₁, g = Tr.invRotate.mor₁ := ⟨_, rfl⟩
  have hg₀ : g ≫ Tr.mor₁ = 0 := hg ▸ comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hTr)
  rw [isIso_iff_coyoneda_map_bijective]
  intro Z
  have hexS (x : S.obj (op Tr.obj₂) ⟶ Z) (hx : S.map Tr.mor₂.op ≫ x = 0) :
      ∃ y : S.obj (op Tr.obj₁) ⟶ Z, S.map Tr.mor₁.op ≫ y = x :=
    Functor.IsHomExact.exact Z Tr hTr x hx
  have hexS' (x : S.obj (op Tr.obj₁) ⟶ Z) (hx : S.map Tr.mor₁.op ≫ x = 0) :
      ∃ y : S.obj (op (Tr.obj₃⟦(-1 : ℤ)⟧)) ⟶ Z, S.map g.op ≫ y = x :=
    hg ▸ Functor.IsHomExact.exact Z Tr.invRotate (inv_rot_of_distTriang _ hTr) x hx
  have hexT (x : T.obj (op Tr.obj₂) ⟶ Z) (hx : T.map Tr.mor₂.op ≫ x = 0) :
      ∃ y : T.obj (op Tr.obj₁) ⟶ Z, T.map Tr.mor₁.op ≫ y = x :=
    Functor.IsHomExact.exact Z Tr hTr x hx
  have hexT' (x : T.obj (op Tr.obj₃) ⟶ Z) (hx : T.map Tr.mor₃.op ≫ x = 0) :
      ∃ y : T.obj (op Tr.obj₂) ⟶ Z, T.map Tr.mor₂.op ≫ y = x :=
    Functor.IsHomExact.exact Z Tr.rotate (rot_of_distTriang _ hTr) x hx
  refine ⟨fun u v huv ↦ ?_, fun y ↦ ?_⟩
  · dsimp only at huv
    rw [← sub_eq_zero]
    have hx : κ.app (op Tr.obj₂) ≫ (u - v) = 0 := by rw [comp_sub, huv, sub_self]
    have h1 : T.map Tr.mor₂.op ≫ (u - v) = 0 := by
      rw [← cancel_epi (κ.app (op Tr.obj₃)), ← reassoc_of% (nat Tr.mor₂), hx, comp_zero,
        comp_zero]
    obtain ⟨x₁, hx₁⟩ := hexT _ h1
    have h2 : S.map Tr.mor₁.op ≫ (κ.app (op Tr.obj₁) ≫ x₁) = 0 := by
      rw [reassoc_of% (nat Tr.mor₁), hx₁, hx]
    obtain ⟨w, hw⟩ := hexS' _ h2
    have hx₁' : x₁ = T.map g.op ≫ (inv (κ.app (op (Tr.obj₃⟦(-1 : ℤ)⟧))) ≫ w) := by
      rw [← cancel_epi (κ.app (op Tr.obj₁)), ← reassoc_of% (nat g), IsIso.hom_inv_id_assoc]
      exact hw.symm
    rw [← hx₁, hx₁', ← Category.assoc, ← T.map_comp, ← CategoryTheory.op_comp, hg₀, op_zero,
      T.map_zero, zero_comp]
  · have h3 : T.map Tr.mor₃.op ≫ (inv (κ.app (op Tr.obj₃)) ≫ S.map Tr.mor₂.op ≫ y) = 0 := by
      rw [← cancel_epi (κ.app (op (Tr.obj₁⟦(1 : ℤ)⟧))), ← reassoc_of% (nat Tr.mor₃),
        IsIso.hom_inv_id_assoc, ← Category.assoc, ← S.map_comp, ← CategoryTheory.op_comp,
        comp_distTriang_mor_zero₂₃ _ hTr, op_zero, S.map_zero, zero_comp, comp_zero]
    obtain ⟨x₂, hx₂⟩ := hexT' _ h3
    have h4 : S.map Tr.mor₂.op ≫ (y - κ.app (op Tr.obj₂) ≫ x₂) = 0 := by
      rw [comp_sub, reassoc_of% (nat Tr.mor₂), hx₂, IsIso.hom_inv_id_assoc, sub_self]
    obtain ⟨z₁, hz₁⟩ := hexS _ h4
    refine ⟨x₂ + T.map Tr.mor₁.op ≫ inv (κ.app (op Tr.obj₁)) ≫ z₁, ?_⟩
    dsimp only
    rw [comp_add, ← reassoc_of% (nat Tr.mor₁), IsIso.hom_inv_id_assoc, hz₁,
      add_sub_cancel]

instance containsZero_shiftIsoLocusOp [S.PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
    (κ : S ⟶ T) :
    κ.shiftIsoLocusOp.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, fun n ↦ by
    have hZ : IsZero ((0 : C)⟦n⟧) := (shiftFunctor C n).map_isZero (isZero_zero C)
    have hS := S.map_isZero hZ.op
    have hT := T.map_isZero hZ.op
    exact ⟨⟨0, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩⟩

/-- **Two out of three** for `κ.shiftIsoLocusOp`. -/
instance isTriangulated_shiftIsoLocusOp [S.PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
    [S.IsHomExact] [T.IsHomExact] (κ : S ⟶ T) : κ.shiftIsoLocusOp.IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' fun Tr hTr h₁ h₃ n ↦ by
    have hTr' := Triangle.shift_distinguished Tr hTr n
    exact κ.isIso_app_obj₂_of_isHomExact _ hTr' (h₁ n) (h₃ n)
      (κ.isIso_app_op_shift_shift h₁ n 1) (κ.isIso_app_op_shift_shift h₃ n (-1))

/-- **Dévissage for a natural transformation of contravariant functors**: if `κ` is an
isomorphism at all shifts of the objects of a class `P`, it is an isomorphism at every object of
the triangulated envelope of `P`. -/
lemma isIso_app_op_of_triangEnvelope [S.PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
    [S.IsHomExact] [T.IsHomExact] (κ : S ⟶ T) {P : ObjectProperty C}
    (h : ∀ N, P N → ∀ n : ℤ, IsIso (κ.app (op (N⟦n⟧)))) {N : C} (hN : P.triangEnvelope N) :
    IsIso (κ.app (op N)) := by
  have := (P.triangEnvelope_le_iff (Q := κ.shiftIsoLocusOp)).2 h N hN 0
  exact κ.isIso_app_op_of_iso ((shiftFunctorZero C ℤ).app N).symm this

end NatTrans

end CategoryTheory
