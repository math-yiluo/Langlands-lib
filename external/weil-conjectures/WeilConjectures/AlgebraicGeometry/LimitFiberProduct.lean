/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Fibre products and quasi-compact opens in inverse limits

## Main results

- `CategoryTheory.IsPullback.isPullback_map_of_isLimit` (blueprint
  `lem-kun-fibre-product-limits`): in any category, a limit of cartesian squares is cartesian;
  in particular inverse limits of schemes commute with fibre products.
- `CategoryTheory.Limits.limitPullbackIso`: the canonical comparison
  `lim (Xᵢ ×_{Sᵢ} Yᵢ) ≅ (lim Xᵢ) ×_{lim Sᵢ} (lim Yᵢ)`.
- `AlgebraicGeometry.Scheme.exists_preimage_eq_of_isAffine` (blueprint
  `corollary-open-direct-image-over-field--2`): a quasi-compact open of a cofiltered limit of affine
  schemes descends to a quasi-compact open of some stage.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {J : Type*} [Category J] {C : Type*} [Category C]

/-- Blueprint `lem-kun-fibre-product-limits`: **limits commute with fibre products.** Let
`Pⱼ → Xⱼ, Pⱼ → Yⱼ, Xⱼ → Sⱼ, Yⱼ → Sⱼ` be a system of cartesian squares, natural in `j`, and let
`cP, cX, cY, cS` be limit cones of the four diagrams. Then the square of limits, formed by the
induced maps `lim P → lim X`, `lim P → lim Y`, `lim X → lim S`, `lim Y → lim S`, is cartesian:
the canonical map `lim (Xⱼ ×_{Sⱼ} Yⱼ) → lim Xⱼ ×_{lim Sⱼ} lim Yⱼ` is an isomorphism. Both sides
represent compatible systems of pairs of maps into `Xⱼ` and `Yⱼ` agreeing in `Sⱼ`. -/
theorem IsPullback.isPullback_map_of_isLimit {P X Y S : J ⥤ C} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : ∀ j, IsPullback (fst.app j) (snd.app j) (f.app j) (g.app j))
    {cP : Cone P} {cX : Cone X} {cY : Cone Y} {cS : Cone S} (hP : IsLimit cP) (hX : IsLimit cX)
    (hY : IsLimit cY) (hS : IsLimit cS) :
    IsPullback (hX.map cP fst) (hY.map cP snd) (hS.map cX f) (hS.map cY g) := by
  have hw : ∀ j, cP.π.app j ≫ fst.app j ≫ f.app j = cP.π.app j ≫ snd.app j ≫ g.app j :=
    fun j ↦ by rw [(h j).w]
  refine ⟨⟨hS.hom_ext fun j ↦ by simpa using hw j⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ hP.lift ⟨s.pt, fun j ↦ (h j).lift (s.fst ≫ cX.π.app j) (s.snd ≫ cY.π.app j) ?_,
      fun j k u ↦ ?_⟩) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · simpa using congrArg (· ≫ cS.π.app j) s.condition
  · refine (h k).hom_ext ?_ ?_
    · simp
    · simp
  · exact hX.hom_ext fun j ↦ by simp
  · exact hY.hom_ext fun j ↦ by simp
  · refine hP.hom_ext fun j ↦ (h j).hom_ext ?_ ?_
    · simpa using congrArg (· ≫ cX.π.app j) h₁
    · simpa using congrArg (· ≫ cY.π.app j) h₂

namespace Limits

variable [HasLimitsOfShape J C] [HasPullbacks C]

/-- The canonical comparison `lim (Xⱼ ×_{Sⱼ} Yⱼ) ≅ (lim Xⱼ) ×_{lim Sⱼ} (lim Yⱼ)`, for natural
transformations `f : X ⟶ S` and `g : Y ⟶ S` of diagrams `J ⥤ C`: the functor `lim` is a right
adjoint, hence preserves fibre products (compare `lem-kun-fibre-product-limits`). -/
noncomputable def limitPullbackIso {X Y S : J ⥤ C} (f : X ⟶ S) (g : Y ⟶ S) :
    limit (pullback f g) ≅ pullback (lim.map f) (lim.map g) :=
  PreservesPullback.iso lim f g

end Limits

end CategoryTheory

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- Blueprint `corollary-open-direct-image-over-field--2`: **descent of a quasi-compact open in an
affine limit.** Let `X = lim Xᵢ` be a cofiltered limit of affine schemes (so that all transition
maps are affine) and `U ⊆ X` a quasi-compact open. Then there are an index `i` and a quasi-compact
open `Uᵢ ⊆ Xᵢ` with `U = pᵢ⁻¹(Uᵢ)`. Write `U` as a finite union of basic opens `D(fₖ)`; the finitely
many `fₖ` all come from a common stage `Aᵢ`. -/
theorem Scheme.exists_preimage_eq_of_isAffine [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
    {c : Cone D} (hc : IsLimit c) (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (Uᵢ : (D.obj i).Opens), IsCompact (Uᵢ : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ Uᵢ = U :=
  exists_preimage_eq D c hc U hU

end AlgebraicGeometry
