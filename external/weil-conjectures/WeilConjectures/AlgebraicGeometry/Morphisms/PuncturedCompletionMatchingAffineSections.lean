/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineSections

/-! # The principal-open section comparison for matching rings

## References

* Stacks Project, Tag 0BLH, proof, and the localized comparison in Tag 05ER
* Stacks Project, Tag 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- On a principal open contained in the punctured spectrum, the first projection of the
matching ring induces a bijection on the sections of the two restricted schemes.
-/
theorem puncturedMap_basicOpen_appTop_bijective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    Function.Bijective
      (D.puncturedMap ∣_ ((D.modelMap ∣_ U) ⁻¹ᵁ
        (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).appTop.hom := by
  obtain ⟨e, he⟩ := D.exists_puncturedMap_basicOpen_appTop_ringEquiv hU f hf
  rw [← he]
  exact e.bijective

end AlgebraicGeometry.Scheme.CompletionGluingData
