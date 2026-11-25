/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Noetherianity of the strict henselization of a regular ring

## References

* Stacks Project, Tag 06LJ
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Noetherianity of the canonical strict henselization over a regular affine ring. -/
theorem strictHenselizationRing_noetherian_of_regular
    (R : CommRingCat.{u}) [IsRegularRing R]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    IsNoetherianRing (strictHenselization barY) := by
  let e : (R ⧸ Ideal.span ({0} : Set R)) ≃+* R := by
    rw [Ideal.span_singleton_zero]
    exact RingEquiv.quotientBot R
  letI : IsRegularRing (R ⧸ Ideal.span ({0} : Set R)) :=
    IsRegularRing.of_ringEquiv e.symm
  obtain ⟨hlocal, _⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  letI : IsLocalRing (strictHenselization barY) := hlocal
  have h := strictHenselizationRing_regular_divisor_quotient R 0 barY b hb (by
    intro hz
    have hz' : (0 : strictHenselization barY) = 1 := by simpa using hz
    exact zero_ne_one hz')
  letI : IsRegularRing
      (strictHenselization barY ⧸ Ideal.span {b.hom 0}) := h.1
  have hn : IsNoetherianRing
      (strictHenselization barY ⧸ Ideal.span {b.hom 0}) := inferInstance
  have ez : (strictHenselization barY ⧸ Ideal.span {b.hom 0}) ≃+*
      strictHenselization barY := by
    rw [show Ideal.span ({b.hom 0} : Set (strictHenselization barY)) = ⊥ by
      simp]
    exact RingEquiv.quotientBot _
  exact isNoetherianRing_of_ringEquiv _ ez
end AlgebraicGeometry.Scheme
