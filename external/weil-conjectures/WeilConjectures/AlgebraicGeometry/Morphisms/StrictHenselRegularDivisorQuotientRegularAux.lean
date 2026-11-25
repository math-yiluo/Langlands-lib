/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.RegularLocalLocalization

/-! Local regularity and Noetherianity of the strict henselization divisor quotient.

## References

* Stacks Project, Tags 05WS and 06LN
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The divisor quotient of the strict henselization by a regular divisor `f` is Noetherian and
all its localizations at primes are regular local rings. -/
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselization barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨p, hp, K, hK, aK, hsep, aLK, hLK, aLH, hH⟩ :=
    strictHenselizationRing_divisor_quotient_presentation R f barY b hb hg
  let := hp
  let := hK
  let := aK
  let := hsep
  let := aLK
  let := hLK
  let := aLH
  have hregL : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  have hregH : IsRegularLocalRing
      (strictHenselization barY ⧸ Ideal.span {b.hom f}) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization
      (Localization.AtPrime p) K _ hH).mp hregL
  let := hregH
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  exact (IsRegularLocalRing.localization_at_prime_and_isRegularRing q).1

end AlgebraicGeometry.Scheme
