/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import all WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine sections of recursive powers of a quasi-coherent ideal module

Source: Stacks Project, Properties, Lemma 01PQ, affine ideal powers.
(blueprint: lem-weil-pbc-general-ideal-power-affine-sections).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Recursive image powers are quasi-coherent, and their affine section ideals
are the powers of the original affine section ideal.

Source: Stacks Project, Properties, Lemma 01PQ, affine ideal powers; existing
proved helper Modules.powers_affine_sections in CoherentSupportVanishingIdealNilpotence.
(blueprint: lem-weil-pbc-general-ideal-power-affine-sections).

Proof: For powers zero and one the claims follow from the unit module and the
original module. For every later power, quasi-coherence of tensor products and
images gives quasi-coherence. The affine tensor-section isomorphism and the
image-section formula identify the new image with the product of the original
image ideal and the preceding power. Induction gives the stated ideal power.
The existing helper proves this for an arbitrary quasi-coherent ideal module;
no monicity or finite-type hypothesis is required. -/
theorem general_ideal_power_affine_sections {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [I.IsQuasicoherent] :
    ∀ n : ℕ, (idealSheafPower ι n).1.IsQuasicoherent ∧
      ∀ V : X.affineOpens,
        (LinearMap.range ((idealSheafPower ι n).2.val.app (op V.1)).hom :
          Ideal Γ(X, V.1)) =
          (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ^ n := by
  exact Modules.powers_affine_sections ι

end AlgebraicGeometry.Scheme
