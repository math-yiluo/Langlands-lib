/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Smooth.Kaehler

/-! # Conormal residue kernel comparison
Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1).
-/

@[expose] public section

universe u

namespace Algebra

private theorem truncated_factor_ker
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{u} R S) (J L : Ideal P.Ring) :
    RingHom.ker (Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L))) =
        J.map (Ideal.Quotient.mk (J ^ 2 ⊔ L)) := by
  change RingHom.ker (Ideal.Quotient.factor
    (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L))) = _
  rw [Ideal.Quotient.factor, Ideal.ker_quotient_lift, Ideal.mk_ker, Ideal.map_sup]
  have hL : L.map (Ideal.Quotient.mk (J ^ 2 ⊔ L)) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  rw [hL, sup_bot_eq]

private theorem truncated_factor_ker_sq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{u} R S) (J L : Ideal P.Ring) :
    (RingHom.ker (Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L)))) ^ 2 = ⊥ := by
  rw [truncated_factor_ker P, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact le_sup_left

private theorem truncated_kernel_to_residue_conormal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring] (N : ℕ)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker) :
    let f := Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0))
        (le_refl (IsLocalRing.maximalIdeal P.Ring ^ N)))
    ∃ l : RingHom.ker f →ₗ[P.Ring]
        (P.Cotangent ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S P.Cotangent))),
      ∀ (j : P.ker) (k : RingHom.ker f),
        (k : P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) =
          Ideal.Quotient.mk _ j.val →
        l k = Submodule.Quotient.mk (Extension.Cotangent.mk j) := by
  let L := IsLocalRing.maximalIdeal P.Ring ^ N
  let I := P.ker ^ 2 ⊔ L
  let f := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0)) (le_refl L))
  let p : Submodule S P.Cotangent := IsLocalRing.maximalIdeal S • ⊤
  let q : P.ker →ₗ[P.Ring] (P.Cotangent ⧸ p) :=
    (p.mkQ.restrictScalars P.Ring).comp Extension.Cotangent.mk
  let t : P.ker →ₗ[P.Ring] RingHom.ker f :=
    (((Ideal.Quotient.mkₐ P.Ring I).toLinearMap).comp P.ker.subtype).codRestrict
      ((RingHom.ker f).restrictScalars P.Ring) (by
        intro j
        change f (Ideal.Quotient.mk I j.val) = 0
        rw [Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact (show P.ker ≤ P.ker ⊔ L from le_sup_left) j.2)
  have ht : Function.Surjective t := by
    intro k
    have hk : k.val ∈ P.ker.map (Ideal.Quotient.mk I) := by
      simpa only [f, I, truncated_factor_ker P] using k.2
    obtain ⟨j, hj, he⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).mp hk
    exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  have hq : LinearMap.ker t ≤ LinearMap.ker q := by
    intro j hj
    have hji : j.val ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrArg Subtype.val hj
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hji
    have haJ : a ∈ P.ker := (Ideal.pow_le_self (I := P.ker)
      (by decide : 2 ≠ 0)) ha
    have hbJ : b ∈ P.ker := by
      have : b = j.val - a := by rw [← hab]; simp
      rw [this]
      exact P.ker.sub_mem j.2 haJ
    have hbAR : b ∈ IsLocalRing.maximalIdeal P.Ring • P.ker := by
      apply hAR
      constructor
      · change b ∈ ((IsLocalRing.maximalIdeal P.Ring ^ N) * ⊤ : Ideal P.Ring)
        simpa only [Ideal.mul_top] using hb
      · exact hbJ
    have hkill : IsLocalRing.maximalIdeal P.Ring •
        (⊤ : Submodule P.Ring P.ker) ≤ LinearMap.ker q := by
      let := IsLocalHom.of_surjective (algebraMap P.Ring S) P.algebraMap_surjective
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr z _
        rw [LinearMap.mem_ker, q.map_smul]
        change p.mkQ (r • Extension.Cotangent.mk z) = 0
        apply (Submodule.Quotient.mk_eq_zero p).mpr
        rw [← algebraMap_smul S r]
        apply Submodule.smul_mem_smul ?_ (Submodule.mem_top)
        change r ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap P.Ring S)
        rwa [IsLocalRing.maximalIdeal_comap]
      · intro x y hx hy
        exact (LinearMap.ker q).add_mem hx hy
    have hqb : q ⟨b, hbJ⟩ = 0 := hkill
      ((Submodule.mem_smul_top_iff _ _ ⟨b, hbJ⟩).mpr hbAR)
    have hqa : q ⟨a, haJ⟩ = 0 := by
      change p.mkQ (Extension.Cotangent.mk ⟨a, haJ⟩) = 0
      rw [(Extension.Cotangent.mk_eq_zero_iff _).mpr ha, map_zero]
    have hjab : j = ⟨a, haJ⟩ + ⟨b, hbJ⟩ := Subtype.ext hab.symm
    rw [LinearMap.mem_ker, hjab, q.map_add, hqa, hqb, add_zero]
  let e := t.quotKerEquivOfSurjective ht
  refine ⟨((LinearMap.ker t).liftQ q hq).comp e.symm.toLinearMap, ?_⟩
  intro j k hk
  have htk : t j = k := Subtype.ext hk.symm
  subst k
  change ((LinearMap.ker t).liftQ q hq) (e.symm (t j)) = q j
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- A section at a truncation satisfying the Artin--Rees bound detects the residue kernel.

Source: Stacks Project, Algebra, Tag 02HT, proof of (4) implies (1), paragraphs
beginning "Consider the presentation" through "Since a split injection", specialized
to reduction modulo the maximal ideal (https://stacks.math.columbia.edu/tag/02HT).
(blueprint: lem-weil-pbc-truncated-section-conormal-residue-kernel).

Proof in words:
Put C = P.Ring, J = P.ker, m = maximalIdeal C, n = maximalIdeal S, and k = S/n.
The surjection C -> S identifies S with C/J, pulls n back to m, and maps m onto n.
Set E = C/(J^2 + m^N) and F = C/(J + m^N). Its kernel K has square zero.
The given R-algebra section sigma of E -> F gives a retraction of
K -> F tensor_E Omega(E/R) by retractionOfSectionOfKerSqZero_comp_kerToTensor.
The retraction is F-linear: the action on K is independent of a lift from F,
since K^2 = 0; in particular the section gives that same action.
The quotient F -> k exists because J + m^N is contained in m. Tensor the
retraction over F with k. The resulting conormal map is a split injection.

The natural surjection J -> K has kernel J^2 + (m^N intersect J), by the modular
law, since J^2 is contained in J. Consequently its reduction over k is
J/(J^2 + (m^N intersect J) + mJ). The hypothesis hAR says m^N intersect J is
contained in mJ (m^N times top is m^N as a submodule of C), so this quotient is
J/(J^2 + mJ), canonically (P.Cotangent)/(n times P.Cotangent).
No Noetherian hypothesis is needed at this step; all of Artin--Rees is hAR.

For the other side, let D = C/J^2 and let m_D be the image of m in D. Then
E = D/(m_D)^N and k is a quotient of D/m_D. Apply the differential-mod-power
lemma to D, m_D, N-1 (positive because N >= 2) and then base change to k.
This identifies k tensor_E Omega(E/R) with k tensor_D Omega(D/R).
Apply the same lemma to C, J, exponent 1, and then base change C/J -> k;
it identifies this with k tensor_C Omega(C/R). Tensor cancellation identifies
the latter with (P.CotangentSpace)/(n times P.CotangentSpace).
Every identification is induced by a quotient map or tensor cancellation.
On a class represented by j in J the composite sends j to 1 tensor dj,
which is P.cotangentComplex_mk followed by reduction. These classes span the
source, so this identifies the split injection with the reduced cotangent map.
Its injectivity says that if P.cotangentComplex x is in n times the target,
then the class of x modulo n is zero, exactly the asserted membership.

For J = 0 the source is zero and the claim is immediate; N = 2 is allowed
and uses exponent 1 in both differential comparisons. The Artin--Rees bound
is essential: without it, e.g. J = (t^2) in k[t]_(t) at N = 2, reduction of
the kernel of E -> F need not identify with J/(J^2 + mJ). 
(blueprint: lem-weil-pbc-truncated-section-conormal-residue-kernel-comap)
-/
/- Structural form of the truncated-section residue-kernel comparison.
The proof is the Artin--Rees and square-zero conormal argument of Stacks Tag 02HT;
see the parent theorem for the complete mathematical reduction.
(blueprint: lem-weil-pbc-truncated-section-conormal-residue-kernel-comap) -/
theorem truncated_section_conormal_residue_kernel_comap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring]
    (N : ℕ) (hN : 2 ≤ N)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker)
    (σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
        (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)))
    (hσ : (Ideal.Quotient.factorₐ R
        (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
      AlgHom.id R _) :
    Submodule.comap P.cotangentComplex
      ((IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.CotangentSpace)) ≤
      (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.Cotangent) := by
  have _hN := hN
  let L := IsLocalRing.maximalIdeal P.Ring ^ N
  let f := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0)) (le_refl L))
  let p : Submodule S P.Cotangent := IsLocalRing.maximalIdeal S • ⊤
  obtain ⟨l, hl⟩ := truncated_kernel_to_residue_conormal P N hAR
  let d₀ := derivationOfSectionOfKerSqZero f (truncated_factor_ker_sq P P.ker L) σ hσ
  let d := l.compDer (d₀.compAlgebraMap P.Ring)
  let v : P.CotangentSpace →ₗ[S] (P.Cotangent ⧸ p) :=
    d.liftKaehlerDifferential.liftBaseChange S
  have hv : v.comp P.cotangentComplex = p.mkQ := by
    apply LinearMap.ext
    intro x
    obtain ⟨j, rfl⟩ := Extension.Cotangent.mk_surjective x
    rw [LinearMap.comp_apply, Extension.cotangentComplex_mk]
    dsimp only [v]
    rw [LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    apply hl j
    change Ideal.Quotient.mk _ j.val - σ (f (Ideal.Quotient.mk _ j.val)) = _
    rw [Ideal.Quotient.factorₐ_apply_mk]
    have hj : Ideal.Quotient.mk (P.ker ⊔ L) j.val = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((show P.ker ≤ P.ker ⊔ L from le_sup_left) j.2)
    rw [hj, map_zero, sub_zero]
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero p).mp
  have hkill : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P.CotangentSpace) ≤
      LinearMap.ker v := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z _
      rw [LinearMap.mem_ker, v.map_smul]
      obtain ⟨a, ha⟩ := p.mkQ_surjective (v z)
      rw [← ha, ← p.mkQ.map_smul]
      exact (Submodule.Quotient.mk_eq_zero p).mpr
        (Submodule.smul_mem_smul hr Submodule.mem_top)
    · intro a b ha hb
      exact (LinearMap.ker v).add_mem ha hb
  simpa only [LinearMap.comp_apply, Submodule.mkQ_apply] using
    (LinearMap.congr_fun hv x).symm.trans (hkill hx)


/-- (blueprint: lem-weil-pbc-truncated-section-conormal-residue-kernel) -/
theorem truncated_section_conormal_residue_kernel
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring]
    (N : ℕ) (hN : 2 ≤ N)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker)
    (σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
        (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)))
    (hσ : (Ideal.Quotient.factorₐ R
        (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
      AlgHom.id R _) :
    ∀ x : P.Cotangent,
      P.cotangentComplex x ∈
          (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.CotangentSpace) →
        x ∈ (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.Cotangent) := by
  intro x hx
  exact truncated_section_conormal_residue_kernel_comap P N hN hAR σ hσ hx


end Algebra
