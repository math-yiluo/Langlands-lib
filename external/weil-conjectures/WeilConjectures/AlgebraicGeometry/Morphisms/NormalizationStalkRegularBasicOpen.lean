/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Localization.Defs

/-! # A function inverted on the source stays regular in relative normalization

## References

* Stacks Project, Tag 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A function inverted on the source is a nonzerodivisor on its relative normalization. -/
theorem normalization_stalk_regular_basicOpen
    (A : CommRingCat.{u}) (r : A) {P : Scheme.{u}}
    (p : P ⟶ Scheme.Opens.toScheme (X := Spec A) (PrimeSpectrum.basicOpen r))
    [QuasiCompact (p ≫ Scheme.Opens.ι (X := Spec A) (PrimeSpectrum.basicOpen r))]
    [QuasiSeparated (p ≫ Scheme.Opens.ι (X := Spec A) (PrimeSpectrum.basicOpen r))] :
    let a := p ≫ Scheme.Opens.ι (X := Spec A) (PrimeSpectrum.basicOpen r)
    ∀ (x : a.normalization),
      IsRegular ((a.fromNormalization.stalkMap x).hom
        (AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x) r)) := by
  dsimp only
  let a := p ≫ Scheme.Opens.ι (X := Spec A) (PrimeSpectrum.basicOpen r)
  intro x
  let d := a.fromNormalization
  let c := a.toNormalization
  let U := d ⁻¹ᵁ (⊤ : (Spec A).Opens)
  have hU : IsAffineOpen U := (isAffineOpen_top _).preimage d
  have hxU : x ∈ U := trivial
  let s : Γ(Spec A, ⊤) := (ΓSpecIso A).inv r
  let z : Γ(a.normalization, U) := (d.app ⊤).hom s
  have hc : Function.Injective (c.app U).hom := by
    rw [RingHom.injective_iff_ker_eq_bot, ← Hom.ker_apply c ⟨U, hU⟩,
      a.ker_toNormalization]
    rfl
  have hu : IsUnit ((c.app U).hom z) := by
    apply P.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    have hyV : a y ∈ (PrimeSpectrum.basicOpen r : (Spec A).Opens) := (p y).2
    have hcd : c ≫ d = a := a.toNormalization_fromNormalization
    have hcy : a y = d (c y) := congrArg (fun k : P ⟶ Spec A ↦ k y) hcd.symm
    rw [hcy] at hyV
    have hbunit : IsUnit ((Spec A).presheaf.germ ⊤ (d (c y)) trivial s) := by
      apply ((Spec A).mem_basicOpen s (d (c y)) trivial).mp
      simpa only [s, basicOpen_eq_of_affine] using hyV
    rw [← c.germ_stalkMap_apply U y hy]
    change IsUnit ((c.stalkMap y).hom
      ((a.normalization.presheaf.germ (d ⁻¹ᵁ ⊤) (c y) hy).hom ((d.app ⊤).hom s)))
    rw [← d.germ_stalkMap_apply ⊤ (c y) hy]
    exact (hbunit.map (d.stalkMap (c y)).hom).map (c.stalkMap y).hom
  have hz : IsRegular z := by
    refine ⟨?_, ?_⟩
    · intro v w hvw
      apply hc
      apply hu.isRegular.left
      simpa only [map_mul] using congrArg (c.app U).hom hvw
    · intro v w hvw
      apply hc
      apply hu.isRegular.right
      simpa only [map_mul] using congrArg (c.app U).hom hvw
  let := TopCat.Presheaf.algebra_section_stalk a.normalization.presheaf ⟨x, hxU⟩
  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  have hzloc : IsRegular (algebraMap Γ(a.normalization, U)
      (a.normalization.presheaf.stalk x) z) := by
    rw [isRegular_iff_mem_nonZeroDivisors]
    exact IsLocalization.map_nonZeroDivisors_le
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _
      ⟨z, hz.mem_nonZeroDivisors, rfl⟩
  convert hzloc using 1
  change (d.stalkMap x).hom ((AlgebraicGeometry.StructureSheaf.toStalk A (d x)).hom r) =
    (a.normalization.presheaf.germ U x hxU).hom z
  change (d.stalkMap x).hom ((Spec A).presheaf.germ ⊤ (d x) trivial s) = _
  exact d.germ_stalkMap_apply ⊤ x trivial s

end AlgebraicGeometry.Scheme
