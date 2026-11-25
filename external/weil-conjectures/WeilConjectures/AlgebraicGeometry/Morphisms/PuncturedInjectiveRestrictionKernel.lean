/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Kernel of restriction to a punctured local spectrum

## References

* Stacks Project, Tag 0A6T, proof of Lemma 51.2.1
* Stacks Project, Tag 0A6T, proof of Lemma 51.2.1 (localization description)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of restriction to the puncture is maximal-ideal-power torsion,
without an injectivity assumption on the module. -/
theorem injective_punctured_restriction_kernel
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (M : ModuleCat.{u} R) :
    (tilde.toOpen M W).hom.ker = Ideal.primaryComponent M (IsLocalRing.maximalIdeal R) := by
  classical
  ext x
  have hzero : (tilde.toOpen M W).hom x = 0 ↔
      StructureSheaf.toOpenₗ R M W x = 0 := by
    change ((tilde.modulesSpecToSheafIso M).app (.op W)).inv
      (StructureSheaf.toOpenₗ R M W x) = 0 ↔ _
    constructor
    · intro h
      have hh := congrArg (((tilde.modulesSpecToSheafIso (R := .of R) M).app (.op W)).hom) h
      simpa only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
        ConcreteCategory.id_apply, map_zero] using hh
    · intro h
      rw [h, map_zero]
  rw [LinearMap.mem_ker, hzero, Ideal.primaryComponent_mem]
  let J := (Submodule.span R ({x} : Set M)).annihilator
  constructor
  · intro hx
    have hrad : IsLocalRing.maximalIdeal R ≤ J.radical := by
      rw [Ideal.radical_eq_sInf]
      apply le_sInf
      intro P hP
      let : P.IsPrime := hP.2
      let p : PrimeSpectrum R := ⟨P, hP.2⟩
      by_cases hp : p = IsLocalRing.closedPoint R
      · have he : P = IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
        exact he ▸ le_rfl
      · have hxW := (hW p).mpr hp
        have hz := congrArg (fun s ↦ s.val ⟨p, hxW⟩) hx
        change LocalizedModule.mk x (1 : P.primeCompl) = 0 at hz
        rw [← LocalizedModule.zero_mk (1 : P.primeCompl)] at hz
        obtain ⟨a, ha⟩ := LocalizedModule.mk_eq.mp hz
        have hax : (a : R) • x = 0 := by simpa [Submonoid.smul_def] using ha
        have haJ : (a : R) ∈ J := (Submodule.mem_annihilator_span_singleton x _).mpr hax
        exact False.elim (a.property (hP.1 haJ))
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    refine ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr ?_⟩
    intro a
    exact (Submodule.mem_annihilator_span_singleton x _).mp (hn a.property)
  · rintro ⟨n, hn⟩
    apply Subtype.ext
    funext p
    have hne : p.val.asIdeal ≠ IsLocalRing.maximalIdeal R := by
      intro h
      apply (hW p.val).mp p.property
      exact PrimeSpectrum.ext h
    have hnot : ¬ IsLocalRing.maximalIdeal R ≤ p.val.asIdeal := by
      intro h
      exact hne ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
        p.val.isPrime.ne_top h).symm
    obtain ⟨a, ham, hap⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have hak : a ^ n • x = 0 :=
      (Submodule.mem_torsionBySet_iff _ _).mp hn
        ⟨a ^ n, Ideal.pow_mem_pow ham n⟩
    change LocalizedModule.mk x (1 : p.val.asIdeal.primeCompl) = 0
    rw [← LocalizedModule.zero_mk (1 : p.val.asIdeal.primeCompl)]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨⟨a, hap⟩ ^ n, ?_⟩
    simpa [Submonoid.smul_def] using hak
end AlgebraicGeometry.Scheme
