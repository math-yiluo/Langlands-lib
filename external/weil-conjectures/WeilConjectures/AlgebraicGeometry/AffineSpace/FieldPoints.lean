/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Weil.Definitions

/-!
# Rational points of affine spaces

For a field extension `L` of `k` and an index type `ι`, the `L`-rational points of the affine
space `𝔸^ι_k` are the vectors `ι → L`: a point `x : Spec L ⟶ 𝔸^ι_k` over `k` is determined by
the values of the coordinate functions at `x`. For the affine line `𝔸¹_k = 𝔸^PUnit_k` this
identifies the `L`-rational points with the elements of `L`.

## Main definitions

- `AlgebraicGeometry.AffineSpace.fieldPointsEquivPi`: `𝔸^ι_k(L) ≃ (ι → L)`.
- `AlgebraicGeometry.AffineSpace.fieldPointsEquiv`: `𝔸¹_k(L) ≃ L`, the case `ι = PUnit`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

variable (ι : Type u) (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]

/-- The `L`-rational points of the affine space `𝔸^ι_k` over `k` are the vectors `ι → L`: a
point `x : Spec L ⟶ 𝔸^ι_k` corresponds to the values `x^*(tᵢ) ∈ Γ(Spec L, 𝒪) = L` of the
coordinates `tᵢ`. -/
noncomputable def fieldPointsEquivPi :
    (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L ≃ (ι → L) where
  toFun x i := (Scheme.ΓSpecIso (.of L)).hom.hom (x.1.appTop (coord _ i))
  invFun a := ⟨homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    fun i ↦ (Scheme.ΓSpecIso (.of L)).inv.hom (a i), homOfVector_over _ _⟩
  left_inv x := by
    refine Subtype.ext (hom_ext ?_ fun i ↦ ?_)
    · rw [homOfVector_over, x.2]
    · rw [homOfVector_appTop_coord, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply]
  right_inv a := by
    funext i
    change (Scheme.ΓSpecIso (.of L)).hom.hom ((homOfVector _ _).appTop (coord _ i)) = a i
    rw [homOfVector_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]

lemma fieldPointsEquivPi_apply
    (x : (𝔸(ι; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L) (i : ι) :
    fieldPointsEquivPi ι k L x i = (Scheme.ΓSpecIso (.of L)).hom.hom (x.1.appTop (coord _ i)) :=
  rfl

/-- The `L`-rational points of the affine line `𝔸¹_k` over `k` are the elements of `L`: a point
`x : Spec L ⟶ 𝔸¹_k` corresponds to the value `x^*(t) ∈ Γ(Spec L, 𝒪) = L` of the coordinate
`t`. It is the case `ι = PUnit` of `AlgebraicGeometry.AffineSpace.fieldPointsEquivPi`, followed
by `PUnit → L ≃ L`. -/
noncomputable def fieldPointsEquiv :
    (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L ≃ L :=
  (fieldPointsEquivPi PUnit.{u + 1} k L).trans (Equiv.funUnique PUnit.{u + 1} L)

lemma fieldPointsEquiv_apply
    (x : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L) :
    fieldPointsEquiv k L x = (Scheme.ΓSpecIso (.of L)).hom.hom (x.1.appTop (coord _ PUnit.unit)) :=
  rfl

/-- For `ι = PUnit`, the coordinate of `fieldPointsEquivPi` is `fieldPointsEquiv`. -/
lemma fieldPointsEquivPi_punit
    (x : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L)
    (i : PUnit.{u + 1}) :
    fieldPointsEquivPi PUnit k L x i = fieldPointsEquiv k L x :=
  rfl

/-- The inverse of `fieldPointsEquiv` is the inverse of `fieldPointsEquivPi` at the constant
vector. -/
lemma fieldPointsEquiv_symm_apply (a : L) :
    (fieldPointsEquiv k L).symm a = (fieldPointsEquivPi PUnit.{u + 1} k L).symm fun _ ↦ a :=
  rfl


end AlgebraicGeometry.AffineSpace
