/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.KrullDimension.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.TraitEtaleExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso

/-!
# FiniteNormalTraitPurity

## References

* Stacks Project, Tags 0EYE and 0EYJ (trait case)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Purity for finite normal covers in the indicated local-base case. -/
theorem finite_normal_etale_of_trait_neighbourhood
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A]
    {L N : Scheme.{u}} (q : L ⟶ Spec (.of A))
    [QuasiCompact q] [QuasiSeparated q] [Smooth q] [GeometricallyConnected q]
    (V : (Spec (.of A)).Opens)
    (hV : ∀ t : Spec (.of A), t ∈ V ↔ t ≠ IsLocalRing.closedPoint A)
    (n : N ⟶ L) [IsFinite n]
    (hnormal : ∀ z : N, IsDomain (N.presheaf.stalk z) ∧
      IsIntegrallyClosed (N.presheaf.stalk z))
    (hdense : Dense (↑(n ⁻¹ᵁ (q ⁻¹ᵁ V)) : Set N))
    (het : Etale (n ∣_ (q ⁻¹ᵁ V)))
    (W : L.Opens) (x : L) (hx : x ∈ W)
    (hqx : q x = IsLocalRing.closedPoint A) (hW : Etale (n ∣_ W))
    (hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞)) : Etale n := by
  let : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨E, p, hpfin, hpet, henormal, hpdense, e, he⟩ :=
    exists_finite_etale_extension_of_trait_neighbourhood A q V hV n het W x hx hqx hW hdim
  let : IsFinite p := hpfin
  let : Etale p := hpet
  obtain ⟨e', he'⟩ :=
    finite_normal_iso_of_dense_open n p hnormal henormal (q ⁻¹ᵁ V) hdense hpdense e he
  rw [← he']
  infer_instance

end AlgebraicGeometry.Scheme
