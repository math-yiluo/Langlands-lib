/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Points of finite schemes over algebraically closed fields

Let `K` be an algebraically closed field. A nonempty finite `K`-scheme has a `K`-point, and
consequently a finite surjective morphism `f : X ⟶ Y` is surjective on `K`-valued points: every
`y : Spec K ⟶ Y` lifts along `f`.

## Main results

- `AlgebraicGeometry.exists_comp_eq_id_of_isFinite`: a nonempty finite scheme over an
  algebraically closed field `K` has a `K`-point.
- `AlgebraicGeometry.exists_comp_eq_of_isFinite_of_surjective`: a finite surjective morphism is
  surjective on points with values in an algebraically closed field.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- Blueprint `corollary-torsion-jacobian-field-extension--3`: Finite schemes over algebraically
closed fields.

A nonempty finite scheme `X` over an algebraically closed field `K` has a `K`-point: a closed
point of `X` has residue field `K`. -/
theorem exists_comp_eq_id_of_isFinite (f : X ⟶ Spec (.of K)) [IsFinite f] [Nonempty X] :
    ∃ s : Spec (.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := X) Set.univ_nonempty
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- Blueprint `corollary-torsion-jacobian-field-extension--3`: Finite flat surjections are
surjective on `K`-points.

Let `f : X ⟶ Y` be finite and surjective and `K` algebraically closed. Then every `K`-point
`y : Spec K ⟶ Y` lifts to a `K`-point of `X`: the fibre `X ×_Y Spec K` is a nonempty finite
`K`-scheme, so it has a `K`-point by `exists_comp_eq_id_of_isFinite`. (Flatness, assumed in the
blueprint, is not needed.) -/
theorem exists_comp_eq_of_isFinite_of_surjective (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (y : Spec (.of K) ⟶ Y) : ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by
  have : Nonempty ↥(pullback f y) :=
    ⟨((pullback.snd f y).surjective (IsLocalRing.closedPoint K)).choose⟩
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isFinite (pullback.snd f y)
  exact ⟨s ≫ pullback.fst f y, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩

/-- A global function on a reduced scheme `X` locally of finite type over an algebraically closed
field `K` vanishes if it vanishes at every `K`-point of `X`: the `K`-points are the closed points,
which are dense in every open subset of the Jacobson space `X`. -/
theorem eq_zero_of_forall_appTop_eq_zero [IsReduced X] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (a : Γ(X, ⊤))
    (h : ∀ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 _ → p.appTop a = 0) : a = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hxa, hx⟩ := nonempty_inter_closedPoints (Z := (X.basicOpen a : Set X))
    (not_not.1 ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).not.2 hne))
    (X.basicOpen a).isOpen.isLocallyClosed
  have hp := h _ (pointOfClosedPoint_comp f x hx)
  have hmem : IsLocalRing.closedPoint K ∈ pointOfClosedPoint f x hx ⁻¹ᵁ X.basicOpen a := by
    change pointOfClosedPoint f x hx (IsLocalRing.closedPoint K) ∈ X.basicOpen a
    rwa [pointOfClosedPoint_apply]
  rw [Scheme.preimage_basicOpen] at hmem
  change IsLocalRing.closedPoint K ∈
    (Spec (.of K)).basicOpen ((pointOfClosedPoint f x hx).appTop a)
    at hmem
  rw [hp, Scheme.basicOpen_zero] at hmem
  exact hmem

end AlgebraicGeometry
