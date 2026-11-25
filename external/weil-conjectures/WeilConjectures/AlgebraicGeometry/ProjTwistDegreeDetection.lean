/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Algebra.Module.DegreeZeroFractions
import all WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-!
# Detection of homogeneous degree on a Proj basic open

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- Clearing homogeneous denominators and projecting kills every component of the wrong degree. -/
private theorem twist_local_component_zero
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (p : HomogeneousIdeal 𝒜) [p.toIdeal.IsPrime]
    (k : ℤ) (a d : A) (n : ℕ) (hd : d ∈ 𝒜 n) (hdp : d ∈ p.toIdeal.primeCompl)
    (hz : IsLocalization.mk' (Localization.AtPrime p.toIdeal) a ⟨d, hdp⟩ ∈
      HomogeneousLocalization.degreePart 𝒜 p.toIdeal.primeCompl k)
    (i : ℕ) (hi : (i : ℤ) ≠ k + n) :
    algebraMap A (Localization.AtPrime p.toIdeal) (DirectSum.decompose 𝒜 a i : A) = 0 := by
  classical
  let R := Localization.AtPrime p.toIdeal
  let g := algebraMap A R
  have hproj {x : A} (hx : g x = 0) (j : ℕ) :
      g (DirectSum.decompose 𝒜 x j : A) = 0 :=
    localization_kernel_isHomogeneous 𝒜 p j hx
  rcases hz with hz | ⟨l, j, u, h, hp, hu, hh, hlj, hz⟩
  · apply hproj
    exact (IsLocalization.map_eq_zero_iff p.toIdeal.primeCompl R a).mpr
      ((IsLocalization.mk'_eq_zero_iff a ⟨d, hdp⟩).mp hz)
  · have heq : g (h * a - d * u) = 0 := by
      have hfrac : IsLocalization.mk' R a ⟨d, hdp⟩ =
          IsLocalization.mk' R u ⟨h, hp⟩ := hz.trans (Localization.mk_eq_mk'_apply _ _)
      have hcross := (IsLocalization.mk'_eq_iff_eq' (S := R)).mp hfrac
      simpa [g, map_sub, map_mul, mul_comm] using sub_eq_zero.mpr hcross
    have hcomp := hproj heq (j + i)
    have hne : n + l ≠ j + i := by omega
    have hdu : (DirectSum.decompose 𝒜 (d * u) (j + i) : A) = 0 :=
      DirectSum.decompose_of_mem_ne 𝒜 (SetLike.mul_mem_graded hd hu) hne
    have hha : (DirectSum.decompose 𝒜 (h * a) (j + i) : A) =
        h * (DirectSum.decompose 𝒜 a i : A) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hh
    have hmul : g h * g (DirectSum.decompose 𝒜 a i : A) = 0 := by
      simp only [DirectSum.decompose_sub, DirectSum.sub_apply,
        AddSubgroupClass.coe_sub, hha, hdu, sub_zero, map_mul] at hcomp
      exact hcomp
    exact (IsLocalization.map_units R (⟨h, hp⟩ : p.toIdeal.primeCompl)).mul_left_cancel
      (hmul.trans (mul_zero (g h)).symm)

/-- An ordinary fraction whose values at all homogeneous primes have degree k itself has
an equal-degree numerator and denominator for the shifted grading.
Source: Stacks Project, Tag 01MN, homogeneous localization of a graded module,
and Tag 01M7, Lemma 27.8.4 (injectivity on a basic open).
(blueprint: lem-sc-proj-twist-degree-detection)

Proof: represent z by a/f^r and decompose a into its finitely many homogeneous
components. This gives components of degrees i-r*b. At a homogeneous prime p away from f,
localize first at just the homogeneous elements outside p. This localization is Z-graded.
It injects into A_p: for an ordinary denominator outside p, some homogeneous component
is outside p and becomes a unit. The grading map sends that denominator to a Laurent
polynomial with a unit coefficient. McCoy's criterion makes this polynomial regular.
The grading map is multiplicative and injective (evaluation at 1 is a left inverse),
so the denominator acts injectively on the graded localization. Further localization
at all ordinary denominators outside p is consequently injective. The degree-k fraction
supplied by hz is already in this graded localization. Equality there and independence
of homogeneous components force every component of z of degree different from k to vanish.
For such a numerator component a_i, consider I = {x in A | some power of f kills x*a_i}.
If a_i/f^r is nonzero, I is proper, homogeneous, and disjoint from powers of f. Choose
an ordinary prime containing I and avoiding f, then take its homogeneous core; the core
is prime, still contains I, and avoids f. It is relevant because f has positive degree.
Vanishing of the component at this point supplies a homogeneous denominator outside the
core killing a_i after multiplication by a power of f. That denominator belongs to I,
a contradiction. Thus only the degree-k component survives globally. Increase r if
necessary until k+r*b is nonnegative, multiplying the numerator by the same power of f.
The resulting numerator and f^r have degree difference k and exhibit membership. If all
components vanish, use the zero numerator; if f is nilpotent, A_f is the zero module. -/
theorem twist_degree_detection
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (z : LocalizedModule.Away f A)
    (hz : ∀ p : basicOpen 𝒜 f,
      IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2) z ∈
        HomogeneousLocalization.degreePart 𝒜
          p.1.asHomogeneousIdeal.toIdeal.primeCompl k) :
    z ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set A))
      (fun n : ℕ ↦ {y : A | if 0 ≤ k + n then y ∈ 𝒜 (k + n).toNat else y = 0})
      (Submonoid.powers f) := by
  classical
  let S := LocalizedModule.Away f A
  obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) z
  obtain ⟨r, hr⟩ := s.prop
  have hsr : (s : A) = f ^ r := hr.symm
  have hsdeg : (s : A) ∈ 𝒜 (r * b) := by
    rw [hsr]
    simpa using SetLike.pow_mem_graded r hf
  have hcomp (i : ℕ) (hi : (i : ℤ) ≠ k + (r * b : ℕ)) :
      algebraMap A S (DirectSum.decompose 𝒜 a i : A) = 0 := by
    apply basicOpen_localization_detection 𝒜 f b hb hf _ 0
    intro p
    have hp := hz p
    rw [← has, IsLocalization.map_mk'] at hp
    have hi0 := twist_local_component_zero 𝒜 p.1.asHomogeneousIdeal k a s (r * b)
      hsdeg ((Submonoid.powers_le.mpr p.2) s.prop) hp i hi
    rw [map_zero, IsLocalization.map_eq, RingHom.id_apply]
    exact hi0
  by_cases hk : 0 ≤ k + (r * b : ℕ)
  · let i := (k + (r * b : ℕ)).toNat
    have hi : (i : ℤ) = k + (r * b : ℕ) := Int.toNat_of_nonneg hk
    have ha : algebraMap A S a = algebraMap A S (DirectSum.decompose 𝒜 a i : A) := by
      conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hcomp j (by intro h; exact hji (Int.natCast_inj.mp (h.trans hi.symm)))
      · intro hin
        have hzero := DFinsupp.notMem_support_iff.mp hin
        rw [hzero, ZeroMemClass.coe_zero, map_zero]
    refine ⟨r * b, (DirectSum.decompose 𝒜 a i : A), s, ?_, hsdeg, ?_⟩
    · change if 0 ≤ k + (r * b : ℕ) then _ else _
      rw [ite_eq_left hk]
      exact (DirectSum.decompose 𝒜 a i).prop
    · rw [← has]
      have heq : IsLocalization.mk' S (DirectSum.decompose 𝒜 a i : A) s =
          IsLocalization.mk' S a s := by
        apply IsLocalization.mk'_eq_iff_eq.mpr
        simpa only [map_mul] using congrArg (fun x : S ↦ algebraMap A S (s : A) * x) ha.symm
      rw [← heq]
      symm
      apply IsLocalization.mk'_eq_iff_eq_mul.mpr
      change LocalizedModule.mk (DirectSum.decompose 𝒜 a i : A) 1 =
        LocalizedModule.mk (DirectSum.decompose 𝒜 a i : A) s * LocalizedModule.mk (s : A) 1
      rw [LocalizedModule.mk_mul_mk, mul_one]
      simpa only [Submonoid.smul_def, smul_eq_mul, mul_comm] using
        (LocalizedModule.mk_cancel s (DirectSum.decompose 𝒜 a i : A)).symm
  · have ha : algebraMap A S a = 0 := by
      rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
      exact Finset.sum_eq_zero fun i _ ↦ hcomp i (by omega)
    have hz0 : z = 0 := by
      rw [← has]
      exact (IsLocalization.mk'_eq_zero_iff (S := S) a s).mpr
        ((IsLocalization.map_eq_zero_iff (Submonoid.powers f) S a).mp ha)
    refine ⟨r * b, 0, s, ?_, hsdeg, ?_⟩
    · change if 0 ≤ k + (r * b : ℕ) then _ else _
      rw [ite_eq_right hk]
    · rw [LocalizedModule.zero_mk, hz0]

end AlgebraicGeometry.Proj
