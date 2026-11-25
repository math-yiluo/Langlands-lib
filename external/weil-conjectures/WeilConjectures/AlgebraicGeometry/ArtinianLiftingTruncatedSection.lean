/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingFiniteKernel
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Truncated Artinian sections
Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1).
-/

@[expose] public section

universe u v

namespace Algebra

/-- The length-one Artinian lifting tests produce sections at every positive truncation.

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), paragraphs
beginning "Let N" and "Applying condition (4)" (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-artinian-lifting-truncated-section).

Proof in words:
Write C = P.Ring, S = A_q, J = P.ker, m = maximalIdeal C, and n = maximalIdeal S.
The surjection C -> S pulls n back to m, so J is contained in m, and the image of
m is n. For N >= 1 put E = C/(J^2 + m^N) and F = C/(J + m^N). Both defining
ideals contain m^N and lie in m. Thus these quotients are nonzero Artinian local
rings by the Noetherian local quotient lemma, and E -> F is a local surjection.
Its kernel K is the image of J and has square zero. The natural map A -> F has
preimage maximal ideal q, since F is canonically S/n^N.

Apply exists_ideal_filtration_length_one to K in E. For its increasing filtration
0 = K_0 <= ... <= K_r = K, use the surjections E/K_i -> E/K_(i+1).
Their kernels are K_(i+1)/K_i and have length one over E/K_i: restriction of
scalars along E -> E/K_i identifies submodule lattices and preserves length.
All quotients are nonzero Artinian local, since the K_i lie in the maximal ideal.
Start with A -> E/K_r = F and lift successively down this finite chain using hlift.
At each stage a local surjection pulls the maximal ideal back to the source
maximal ideal, so the inverse image in A remains q. The structural R-map is
induced from C, and each application preserves its composite with A. This gives
an R-compatible lift a' : A -> E.

The preimage under a' of the maximal ideal of E is q, by composing with E -> F.
Hence every element outside q maps to a unit, and a' extends uniquely to S.
This extension is local: a fraction with numerator in q maps into the maximal
ideal, while its denominator is a unit. The maximal ideal of E is the image of
m and its N-th power is zero. Thus the extension annihilates n^N and factors
uniquely through S/n^N = F as an R-algebra map sigma : F -> E.
The composite E -> F after sigma agrees with the identity on A. Uniqueness of
localization maps first gives equality on S, and surjectivity of S -> F gives
equality on F. This is the displayed section equation.

For tests in Type (max u v), replace the intermediate quotient rings by ULift
and transport their maps by its ring equivalence. Equivalences preserve local
and Artinian structures, kernel length, and the two compatibility equations;
transport each lift back before continuing the induction. This is only a choice
inside an existential proof, not a definition of an object from an unproved theorem.
For N = 1 the two quotients are C/m and the section is the identity; if J = 0
all quotient maps are identities. No finite presentation or assumption on the
residue characteristic is used. -/
theorem artinian_lifting_truncated_section
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime]
    (P : Extension.{u} R (Localization.AtPrime q))
    [IsLocalRing P.Ring] [IsNoetherianRing P.Ring]
    (hlift : ∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp (algebraMap R A) = φ.comp ρ →
          Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp (algebraMap R A) = ρ) :
    ∀ (N : ℕ), 1 ≤ N →
      ∃ σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
          (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)),
        (Ideal.Quotient.factorₐ R
          (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
            AlgHom.id R _ := by
  intro N hN
  let C := P.Ring
  let S := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal C
  let I : Ideal C := P.ker ^ 2 ⊔ m ^ N
  let L : Ideal C := P.ker ⊔ m ^ N
  let f : C →ₐ[R] S := IsScalarTower.toAlgHom R C S
  have hf : Function.Surjective f := P.algebraMap_surjective
  have hfLocal : IsLocalHom f.toRingHom := IsLocalHom.of_surjective _ hf
  have hJ : P.ker ≤ m := by
    intro x hx
    have hz : f x = 0 := hx
    change x ∈ IsLocalRing.maximalIdeal C
    rw [← IsLocalRing.maximalIdeal_comap f.toRingHom]
    change f x ∈ IsLocalRing.maximalIdeal S
    rw [hz]
    exact Ideal.zero_mem _
  have hIm : I ≤ m := sup_le
    ((Ideal.pow_le_self (by decide : 2 ≠ 0)).trans hJ)
    (Ideal.pow_le_self (by omega))
  have hLm : L ≤ m := sup_le hJ (Ideal.pow_le_self (by omega))
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top hIm
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top hLm
  have : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Nontrivial (C ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr hL
  have : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalRing (C ⧸ L) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have hnil : IsLocalRing.maximalIdeal (C ⧸ I) ^ N = ⊥ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
  have hnilL : IsLocalRing.maximalIdeal (C ⧸ L) ^ N = ⊥ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk L)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact le_sup_right)
  have : IsArtinianRing (C ⧸ I) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨N, hnil⟩
  have : IsArtinianRing (C ⧸ L) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr ⟨N, hnilL⟩
  let t : S →ₐ[R] (C ⧸ L) := AlgHom.liftOfSurjective f hf
    (Ideal.Quotient.mkₐ R L) (by
      change P.ker ≤ RingHom.ker (Ideal.Quotient.mk L)
      rw [Ideal.mk_ker]
      exact le_sup_left)
  have ht (x : C) : t (f x) = Ideal.Quotient.mk L x :=
    AlgHom.liftOfSurjective_apply _ _ _ _ x
  have htSurj : Function.Surjective t := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨f x, ht x⟩
  have htLocal : IsLocalHom t.toRingHom := IsLocalHom.of_surjective _ htSurj
  let φ : (C ⧸ I) →ₐ[R] (C ⧸ L) := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)
  have hφSurj : Function.Surjective φ := Ideal.Quotient.factor_surjective
    (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)
  have hφLocal : IsLocalHom φ.toRingHom := IsLocalHom.of_surjective _ hφSurj
  let a : A →+* (C ⧸ L) := t.toRingHom.comp (algebraMap A S)
  have ha : a.comp (algebraMap R A) = φ.toRingHom.comp (algebraMap R (C ⧸ I)) := by
    ext r
    change t ((algebraMap A S) ((algebraMap R A) r)) =
      φ ((algebraMap R (C ⧸ I)) r)
    rw [← IsScalarTower.algebraMap_apply R A S, t.commutes, φ.commutes]
  have haq : Ideal.comap a (IsLocalRing.maximalIdeal (C ⧸ L)) = q := by
    dsimp only [a]
    rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal S q
  obtain ⟨a', ha', hR⟩ := artinian_lifting_finite_kernel.{u, v} q hlift
    (C ⧸ I) (C ⧸ L) φ.toRingHom hφSurj (algebraMap R (C ⧸ I)) a ha haq
  have ha'q : Ideal.comap a' (IsLocalRing.maximalIdeal (C ⧸ I)) = q := by
    rw [← IsLocalRing.maximalIdeal_comap φ.toRingHom, Ideal.comap_comap, ha']
    exact haq
  have hu (y : q.primeCompl) : IsUnit (a' y) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    change y.1 ∉ Ideal.comap a' (IsLocalRing.maximalIdeal (C ⧸ I))
    rw [ha'q]
    exact y.2
  let b : S →+* (C ⧸ I) := IsLocalization.lift hu
  have hb : b.comp (algebraMap A S) = a' := IsLocalization.lift_comp hu
  have hbt : φ.toRingHom.comp b = t.toRingHom := by
    apply IsLocalization.ringHom_ext q.primeCompl
    rw [RingHom.comp_assoc, hb, ha']
  have hbLocal : IsLocalHom b := by
    have : IsLocalHom (φ.toRingHom.comp b) := hbt ▸ htLocal
    exact isLocalHom_of_comp b φ.toRingHom
  let bₐ : S →ₐ[R] (C ⧸ I) :=
    { toRingHom := b
      commutes' := by
        intro r
        change b ((algebraMap R S) r) = _
        rw [IsScalarTower.algebraMap_apply R A S]
        rw [show b ((algebraMap A S) ((algebraMap R A) r)) =
          a' ((algebraMap R A) r) from DFunLike.congr_fun hb ((algebraMap R A) r)]
        exact DFunLike.congr_fun hR r }
  let g : C →ₐ[R] (C ⧸ I) := bₐ.comp f
  have hgLocal : IsLocalHom g.toRingHom :=
    inferInstanceAs (IsLocalHom (b.comp f.toRingHom))
  have hm : m.map g.toRingHom ≤ IsLocalRing.maximalIdeal (C ⧸ I) :=
    IsLocalRing.map_maximalIdeal_le g.toRingHom
  have hpow : m ^ N ≤ RingHom.ker g.toRingHom := by
    apply (Ideal.map_eq_bot_iff_le_ker _).mp
    apply le_bot_iff.mp
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' hm N).trans hnil.le
  have hker : L ≤ RingHom.ker g.toRingHom := by
    apply sup_le _ hpow
    intro x hx
    change b (f x) = 0
    rw [show f x = 0 from hx, map_zero]
  let σ : (C ⧸ L) →ₐ[R] (C ⧸ I) := Ideal.Quotient.liftₐ L g hker
  refine ⟨σ, ?_⟩
  apply AlgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change φ (g x) = Ideal.Quotient.mk L x
  change φ (b (f x)) = _
  exact (DFunLike.congr_fun hbt (f x)).trans (ht x)

end Algebra
