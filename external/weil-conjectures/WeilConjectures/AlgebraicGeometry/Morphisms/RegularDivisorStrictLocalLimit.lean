/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-! # Strict local limits of regular divisors

## References

* Stacks Project, Tag 0EYG, strict henselization paragraph
* Tags 04GP, 04HX, 06LN and 05WS for strict henselization and passage to the quotient
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

-- Preserve the original existential instance binder name `hH`.
/-- A regular divisor has a pointed regular strict local ind-etale limit. -/
theorem regular_divisor_strict_local_limit
    (R : CommRingCat.{u}) (g : R) [IsRegularRing R]
    (hg : IsSMulRegular R g) [IsRegularRing (R ⧸ Ideal.span {g})]
    (y : Spec R) (hy : g ∈ y.asIdeal) :
    ∃ (H : CommRingCat.{u}) (ι : R →+* H),
      ι.IndEtale ∧
      ∃ (_ : IsStrictlyHenselianLocalRing H),
        IsRegularLocalRing H ∧ IsRegularLocalRing (H ⧸ Ideal.span {ι g}) ∧
        IsSMulRegular H (ι g) ∧
        ι g ∈ IsLocalRing.maximalIdeal H ∧
        ∃ x : Spec H, (Spec.map (CommRingCat.ofHom ι)) x = y := by
  classical
  let Ω := AlgebraicClosure ((Spec R).residueField y)
  let barY : Spec (.of Ω) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec R).residueField y) Ω)) ≫
      (Spec R).fromSpecResidueField y
  have hbarY : barY (IsLocalRing.closedPoint Ω) = y :=
    (Spec R).fromSpecResidueField_apply y _
  let : Algebra ((Spec R).residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo barY)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, hx, _⟩ :=
    AlgebraicGeometry.strictHenselizationResidue barY rfl
  let H := strictHenselization barY
  have : IsLocalRing H := hlocal
  let b : R ⟶ H := Spec.preimage (strictLocalizationToBase barY)
  have hb : Spec.map b = strictLocalizationToBase barY := Spec.map_preimage _
  have hi : b.hom.IndEtale := by
    have h := strictHenselization_indEtale_of_affine_chart barY R (𝟙 (Spec R))
      (by simp) (Iso.refl _) b.hom (by
        change Spec.map b ≫ 𝟙 (Spec R) = strictLocalizationToBase barY
        rw [Category.comp_id]
        exact hb)
    exact h
  have hpoint : (Spec.map b) (IsLocalRing.closedPoint H) = y := by
    rw [hb]
    exact hx.trans hbarY
  have hgm : b.hom g ∈ IsLocalRing.maximalIdeal H := by
    have h := congrArg PrimeSpectrum.asIdeal hpoint
    change (IsLocalRing.maximalIdeal H).comap b.hom = y.asIdeal at h
    change g ∈ (IsLocalRing.maximalIdeal H).comap b.hom
    rw [h]
    exact hy
  have hnunit : ¬ IsUnit (b.hom g) :=
    (IsLocalRing.mem_maximalIdeal _).mp hgm
  obtain ⟨_, hquot, hdomain⟩ :=
    strictHenselization_regular_divisor_quotient R g barY b hb hnunit
  have : IsRegularRing (H ⧸ Ideal.span {b.hom g}) := hquot
  have : IsDomain (H ⧸ Ideal.span {b.hom g}) := hdomain
  have : IsLocalRing (H ⧸ Ideal.span {b.hom g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hquotLocal : IsRegularLocalRing (H ⧸ Ideal.span {b.hom g}) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  -- The existing quotient comparison also handles zero, giving ambient regularity.
  have : IsRegularRing (R ⧸ Ideal.span {(0 : R)}) :=
    IsRegularRing.of_ringEquiv ((RingEquiv.quotientBot R).symm.trans
      (Ideal.quotEquivOfEq (Ideal.span_singleton_zero (α := R))).symm)
  obtain ⟨_, hzero, _⟩ :=
    strictHenselization_regular_divisor_quotient R 0 barY b hb (by simp)
  have : IsRegularRing (H ⧸ Ideal.span {b.hom (0 : R)}) := hzero
  let e0 : (H ⧸ Ideal.span {b.hom (0 : R)}) ≃+* H :=
    (Ideal.quotEquivOfEq (by rw [map_zero, Ideal.span_singleton_zero])).trans
      (RingEquiv.quotientBot H)
  have : IsRegularRing H := IsRegularRing.of_ringEquiv e0
  have hreg : IsRegularLocalRing H :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  let : Algebra R H := b.hom.toAlgebra
  have : Algebra.IndEtale R H := hi
  have hsmul : IsSMulRegular H (b.hom g) := hg.of_flat
  exact ⟨H, b.hom, hi, hstrict, hreg, hquotLocal, hsmul, hgm,
    IsLocalRing.closedPoint H, hpoint⟩

end AlgebraicGeometry.Scheme
