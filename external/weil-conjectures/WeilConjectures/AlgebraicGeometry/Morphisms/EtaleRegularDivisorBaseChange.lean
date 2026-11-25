/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Smooth.Flat

/-!
# Regular divisors under etale base change

## References

* Stacks Project, Tag 07NF and flat base change
* Stacks Project, Tags 07NF (regularity under smooth maps), 00TA (smooth flatness), 02GO (etale base
  change), and 039P (etale morphisms are smooth)
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Etale change of base preserves a regular ring and its regular divisor. -/
theorem etale_regular_divisor_base_change
    (R S : CommRingCat.{u}) (φ : R →+* S)
    [IsRegularRing R] (g : R) (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    (hφ : Etale (Spec.map (CommRingCat.ofHom φ))) :
    IsRegularRing S ∧ IsSMulRegular S (φ g) ∧
      IsRegularRing (S ⧸ Ideal.span {φ g}) := by
  let : Algebra R S := φ.toAlgebra
  have : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hφ)
  have hreg : IsRegularRing S := Algebra.isRegularRing_of_smooth R S
  have hsmul : IsSMulRegular S (φ g) := hg.of_flat
  let I : Ideal R := Ideal.span {g}
  let k := R ⧸ I
  have hT : IsRegularRing (TensorProduct R k S) :=
    Algebra.isRegularRing_of_smooth k (TensorProduct R k S)
  have hQ : IsRegularRing (S ⧸ I.map (algebraMap R S)) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toRingEquiv
  change IsRegularRing (S ⧸ (Ideal.span {g}).map φ) at hQ
  rw [Ideal.map_span, Set.image_singleton] at hQ
  exact ⟨hreg, hsmul, hQ⟩

end AlgebraicGeometry.Scheme
