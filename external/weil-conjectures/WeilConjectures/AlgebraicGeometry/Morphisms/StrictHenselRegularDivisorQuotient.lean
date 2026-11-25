/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular

/-! # The regular divisor quotient of the canonical strict henselization

## References

* Stacks Project, Tag 0EYG, strict henselization paragraph
* Stacks Project, Tag 0EYG, strict henselization paragraph, using quotient compatibility (Tag 05WS)
  and regularity of strict henselizations (Tag 06LN)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical strict henselization is Noetherian and its nonempty divisor quotient
is a regular domain. -/
theorem strictHenselization_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselization barY) ∧
      IsRegularRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselization barY ⧸ Ideal.span {b.hom f}) := by
  have hN := strictHenselizationRing_noetherian_of_regular R barY b hb
  have hQ := strictHenselizationRing_regular_divisor_quotient R f barY b hb hg
  exact ⟨hN, hQ.1, hQ.2⟩

end AlgebraicGeometry.Scheme
