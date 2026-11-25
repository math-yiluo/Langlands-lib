/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.GabberPrincipalClassLocallyZero
import WeilConjectures.AlgebraicGeometry.GabberPrincipalVanishingIdeal
import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The fixed-degree case of Gabber's criterion.

This is the induction step of the proof of Gabber's criterion: for a fixed positive
integer `q`, the hypotheses imply that the `q`-th cohomology group is subsingleton.
The proof follows the simultaneous induction on principal opens, using strict
henselian Zariski comparison, local vanishing, the degree-one kernel hypothesis,
and Mayer--Vietoris.  This intermediate statement is split from the parent theorem
so that the induction argument can be developed independently.
Source: Stacks Project, Etale Cohomology, Lemma 0GY0.
(blueprint: lem-weil-pbc-gabber-criterion-degree)

Proof: perform the simultaneous induction on principal opens from Lemma 0GY0;
strict henselian comparison gives local Zariski vanishing, the degree-one kernel
hypothesis gives addition closure in degree one, and Mayer--Vietoris gives it in
higher degrees.  The radical argument then forces the fixed class to vanish.
-/
theorem gabberCriterion_degree
    (R : Type u) [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsStrictlyHenselianLocalRing (Localization.AtPrime p))
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfg : ∀ (f g : R) (x : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1),
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right f (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right g (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
        x = 0)
    (q : ℕ) (hq : 0 < q) : Subsingleton (Sheaf.H F q) := by
  have hall : ∀ (n : ℕ), 0 < n → ∀ (h : R),
      Subsingleton (Sheaf.H
        (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
          (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn h
        refine ⟨fun ξ η ↦ ?_⟩
        have hz : ∀ ξ : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) n,
            ξ = 0 := by
          intro ξ
          obtain ⟨I, hI⟩ := gabber_principal_vanishing_ideal R F hfg n hn
            (fun m hm hmn a ↦ ih m hmn hm a) h ξ
          have hr : h ∈ I.radical := by
            rw [Ideal.radical_eq_sInf]
            rw [Submodule.mem_sInf]
            intro p hp
            let _ : Ideal.IsPrime p := hp.2
            by_contra hh
            obtain ⟨f, hf, hfp⟩ :=
              gabber_principal_class_locally_zero R hR F n hn h ξ p hh
            exact hfp (hp.1 ((hI f).mpr hf))
          obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hr
          have hzero := (hI (h ^ N)).mp hN
          have heq : PrimeSpectrum.basicOpen (h ^ N * h) = PrimeSpectrum.basicOpen h := by
            rw [← pow_succ, PrimeSpectrum.basicOpen_pow h (N + 1) (Nat.succ_pos N)]
          have hiso : IsIso (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right (h ^ N) h)) := by
            change IsIso (Scheme.homOfLE (X := Spec (CommRingCat.of R)) heq.le)
            rw [← Scheme.isoOfEq_hom _ heq]
            infer_instance
          exact (cohomologyMap_bijective _ _ n).injective
            (hzero.trans (map_zero _).symm)
        exact (hz ξ).trans (hz η).symm
  have htop : IsIso (Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen (1 : R))) := by
    rw [PrimeSpectrum.basicOpen_one]
    change IsIso (Spec (CommRingCat.of R)).topIso.hom
    infer_instance
  have := hall q hq 1
  exact (cohomologyMap_bijective
    (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen (1 : R)))
    F q).injective.subsingleton

end AlgebraicGeometry.Etale
