/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Naturality of the underlying morphism of descent transport

Source: the naturality field of the transport descent datum, Stacks Project, Tag 0H8K.
(blueprint: lem-pd-transport-left-naturality).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Naturality of transport after taking the underlying scheme morphism.
Source: Stacks Project, Tag 0H8K, naturality of the cartesian descent datum.
(blueprint: lem-pd-transport-left-naturality).

Proof: Substitute the two equalities identifying the new maps with their composites
with g. Morphisms in Over are determined by their underlying maps, so ha identifies
a' with Over.homMk g followed by a. Apply the existing transport_homMk_comp field
of D and take underlying maps. This applies to arbitrary schemes, including empty
ones, and requires no finiteness, flatness or point assumptions. -/
theorem transport_left_naturality
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} (D : Over.DescentDatum p V)
    {T T' : Scheme.{u}} (g : T' ⟶ T) (f₁ f₂ : T ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V)
    (f₁' f₂' : T' ⟶ X) (h' : f₁' ≫ p = f₂' ≫ p) (a' : Over.mk f₁' ⟶ V)
    (hf₁ : f₁' = g ≫ f₁) (hf₂ : f₂' = g ≫ f₂) (ha : a'.left = g ≫ a.left) :
    (D.transport f₁' f₂' h' a').left = g ≫ (D.transport f₁ f₂ h a).left := by
  subst f₁' f₂'
  have ha' : a' = (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a := by
    ext
    exact ha
  rw [ha', D.transport_homMk_comp]
  rfl


end CategoryTheory.Over.DescentDatum
