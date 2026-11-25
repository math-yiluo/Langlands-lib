/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # A universal Noetherian base for N-invertible schemes

Source: the universal-base argument in the finite projective-line levelwise check,
blueprint main-20261015, smooth-purity tower construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every N-invertible scheme maps to an N-invertible Noetherian scheme.
Source: the universal-base argument in the finite projective-line levelwise check,
blueprint main-20261015, smooth-purity tower construction.
(auxiliary; not a blueprint node)

Proof: take the spectrum of the localization of the universe-lifted integers at N.
Localization preserves Noetherianity. The localization map makes N a unit, and the
spectrum/global-sections isomorphism makes it a unit on the spectrum. The universal
property of localization extends the integer map to the global functions of any
N-invertible scheme; the global-sections/spectrum adjunction gives its map to this base.
This works for N = 1 and the empty scheme as well. -/
theorem finiteP1_exists_noetherianBase (N : ℕ) :
    ∃ (U : Scheme.{u}) (_ : IsNoetherian U),
      IsUnit (N : Γ(U, ⊤)) ∧
      ∀ (S : Scheme.{u}), IsUnit (N : Γ(S, ⊤)) → Nonempty (S ⟶ U) := by
  let R := ULift.{u} ℤ
  let B := Localization.Away (N : R)
  let U := Spec (CommRingCat.of B)
  have : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsNoetherianRing B := inferInstance
  refine ⟨U, inferInstance, ?_, ?_⟩
  · have h : IsUnit (N : B) := by
      exact (map_natCast (algebraMap R B) N) ▸
        (IsLocalization.Away.algebraMap_isUnit (S := B) (N : R))
    exact (map_natCast (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom N) ▸
      h.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  · intro S hS
    let f : R →+* Γ(S, ⊤) :=
      (Int.castRingHom Γ(S, ⊤)).comp ULift.ringEquiv.toRingHom
    have hf : IsUnit (f (N : R)) := by
      rw [map_natCast]
      exact hS
    let g : B →+* Γ(S, ⊤) := IsLocalization.Away.lift (N : R) hf
    exact ⟨ΓSpec.adjunction.homEquiv S (Opposite.op (CommRingCat.of B))
      (CommRingCat.ofHom g).op⟩

end AlgebraicGeometry
