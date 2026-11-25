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
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The divisor quotient of the strict henselization is a domain

## References

* Stacks Project, Tag 00NP
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The divisor quotient of the canonical strict henselization is a domain. -/
theorem strictHenselizationRing_divisor_quotient_domain_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsDomain (strictHenselization barY ⧸ Ideal.span {b.hom f}) := by
  obtain ⟨hlocal, _⟩ := (show ∃ (_ : IsLocalRing (Scheme.strictHenselization barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) from
      ⟨inferInstance, ⟨inferInstance⟩⟩)
  let := hlocal
  let := strictHenselizationRing_regular_divisor_quotient_part R f barY b hb hg
  have hproper : Ideal.span {b.hom f} ≠ ⊤ := fun h ↦
    hg (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial (strictHenselization barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let := IsRegularLocalRing.of_isRegularRing_of_isLocalRing
    (R := strictHenselization barY ⧸ Ideal.span {b.hom f})
  infer_instance

end AlgebraicGeometry.Scheme
