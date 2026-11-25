/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationLocalizedDivisorQuotient

/-! # Algebraic presentation of a strict henselization divisor quotient

## References

* Stacks Project, Tag 04HX (Lemma on stalks of the structure sheaf) and Tag 05WS (Lemma on strict
  henselization of a quotient)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The geometric strict henselization modulo a nonunit divisor is an algebraic strict
henselization of a prime localization of the divisor ring. No regularity hypothesis is used.
-/
theorem strictHenselizationRing_divisor_quotient_presentation
    (R : CommRingCat.{u}) (f : R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    ∃ (p : Ideal (R ⧸ Ideal.span {f})) (_ : p.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p) K)
      (_ : IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p)
        (strictHenselization barY ⧸ Ideal.span {b.hom f})),
      Algebra.IsStrictHenselization (Localization.AtPrime p) K
        (strictHenselization barY ⧸ Ideal.span {b.hom f}) := by
  obtain ⟨q, hq, K, hK, ares, hsep, aK, htower, aH, hbase, hH⟩ :=
    strictHenselizationRing_local_presentation R barY b hb
  let := hq
  let := hK
  let := ares
  let := hsep
  let := aK
  let := htower
  let := aH
  have hf : f ∈ q := by
    by_contra hf
    have hu : IsUnit (algebraMap R (Localization.AtPrime q) f) :=
      IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨f, hf⟩
    have hu' := hu.map (algebraMap (Localization.AtPrime q) (strictHenselization barY))
    rw [hbase f] at hu'
    exact hg hu'
  let J : Ideal R := Ideal.span {f}
  have hJ : J ≤ q := (Ideal.span_singleton_le_iff_mem q).2 hf
  let p : Ideal (R ⧸ J) := q.map (Ideal.Quotient.mk J)
  have hpprime : p.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hp : p.comap (Ideal.Quotient.mk J) = q := Ideal.comap_map_mk hJ
  let L := SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p))
  let aL : Algebra (Localization.AtPrime p) L :=
    ((algebraMap (IsLocalRing.ResidueField (Localization.AtPrime p)) L).comp
      (IsLocalRing.residue _)).toAlgebra
  have tL : IsScalarTower (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) L :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let ψ : R ⧸ J →+* strictHenselization barY ⧸ Ideal.span {b.hom f} :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp b.hom) (fun a ha ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  have hunit : ∀ s : p.primeCompl, IsUnit (ψ s) := by
    rintro ⟨s, hs⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hr : r ∈ q.primeCompl := fun hr ↦ hs (Ideal.mem_map_of_mem _ hr)
    have hu := (IsLocalization.map_units (Localization.AtPrime q) ⟨r, hr⟩).map
      (algebraMap (Localization.AtPrime q) (strictHenselization barY))
    rw [hbase r] at hu
    exact hu.map (Ideal.Quotient.mk _)
  let φ : Localization.AtPrime p →+* strictHenselization barY ⧸ Ideal.span {b.hom f} :=
    IsLocalization.lift hunit
  let aφ : Algebra (Localization.AtPrime p) (strictHenselization barY ⧸ Ideal.span {b.hom f}) :=
    φ.toAlgebra
  have hcomp : ∀ r : R, algebraMap (Localization.AtPrime p)
      (strictHenselization barY ⧸ Ideal.span {b.hom f})
      (algebraMap (R ⧸ J) _ (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (b.hom r) :=
    fun r ↦ IsLocalization.lift_eq hunit _
  exact ⟨p, hpprime, L, inferInstance, inferInstance, inferInstance, aL, tL, aφ,
    hH.localized_divisor_quotient R (strictHenselization barY) q K b.hom hbase f p hp L hcomp⟩

end AlgebraicGeometry.Scheme
