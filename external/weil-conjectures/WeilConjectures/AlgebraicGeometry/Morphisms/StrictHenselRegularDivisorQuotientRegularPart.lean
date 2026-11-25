/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux

/-! Regularity component of the canonical strict henselization divisor quotient.

## References

* Stacks Project, Tags 05WS and 06LN
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The quotient by the divisor remains regular after passage to the canonical strict henselization.
-/
theorem strictHenselizationRing_regular_divisor_quotient_part
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) := by
  let H := strictHenselization barY ⧸ Ideal.span {b.hom f}
  obtain ⟨_, hloc⟩ :=
    strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
      R f barY b hb hg
  let _ : ∀ (p : Ideal H) [p.IsPrime],
      IsRegularLocalRing (Localization.AtPrime p) := hloc
  exact ⟨fun p hp => hloc p⟩

end AlgebraicGeometry.Scheme
