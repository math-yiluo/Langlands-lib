/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Detection of localized elements at homogeneous primes

Source: Stacks Project, Tag 01M7, basic-open localization argument.
-/

@[expose] public section

universe v
namespace AlgebraicGeometry.Proj

/-- Encode the homogeneous decomposition as a polynomial, preserving multiplication. -/
private noncomputable def gradingPolynomial
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] : A →+* Polynomial A := by
  classical
  let g : ∀ n, 𝒜 n →+ Polynomial A := fun n ↦
    (Polynomial.monomial n).toAddMonoidHom.comp (AddSubgroupClass.subtype (𝒜 n))
  refine (DirectSum.toSemiring g ?_ ?_).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom
  · simp [g, Polynomial.monomial_zero_left]
  · intro i j a b
    simp [g, Polynomial.monomial_mul_monomial]

/-- The coefficient in degree n is the degree-n homogeneous component. -/
private theorem gradingPolynomial_coeff
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (a : A) (n : ℕ) :
    (gradingPolynomial 𝒜 a).coeff n = (DirectSum.decompose 𝒜 a n : A) := by
  classical
  let g : ∀ n, 𝒜 n →+ Polynomial A := fun n ↦
    (Polynomial.monomial n).toAddMonoidHom.comp (AddSubgroupClass.subtype (𝒜 n))
  have h (x : DirectSum ℕ (fun i ↦ 𝒜 i)) : (DirectSum.toAddMonoid g x).coeff n = (x n : A) := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      by_cases hi : i = n
      · subst i
        simp [g]
      · simp [g, Polynomial.coeff_monomial, DirectSum.of_apply, hi]
    | add x y hx hy => simp [hx, hy]
  exact h (DirectSum.decompose 𝒜 a)

/-- McCoy's criterion applied over A_p makes the localization kernel homogeneous.
A denominator outside p has a homogeneous component outside p, hence a unit coefficient
in its grading polynomial. Its product with the numerator's grading polynomial is zero,
so every coefficient of the latter vanishes in A_p. -/
private theorem localization_kernel_isHomogeneous
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (p : HomogeneousIdeal 𝒜) [p.toIdeal.IsPrime] :
    (RingHom.ker (algebraMap A (Localization.AtPrime p.toIdeal))).IsHomogeneous 𝒜 := by
  classical
  let R := Localization.AtPrime p.toIdeal
  let g : A →+* Polynomial R :=
    (Polynomial.mapRingHom (algebraMap A R)).comp (gradingPolynomial 𝒜)
  have hg (a : A) (n : ℕ) :
      (g a).coeff n = algebraMap A R (DirectSum.decompose 𝒜 a n : A) := by
    simp [g, Polynomial.coeff_map, gradingPolynomial_coeff]
  intro n a ha
  have ha' : algebraMap A R a = 0 := ha
  obtain ⟨s, hsa⟩ := (IsLocalization.map_eq_zero_iff p.toIdeal.primeCompl R a).mp ha'
  have hs : ¬ ∀ k, (DirectSum.decompose 𝒜 (s : A) k : A) ∈ p.toIdeal := by
    intro h
    exact s.prop ((Ideal.IsHomogeneous.mem_iff 𝒜 p.isHomogeneous).mpr h)
  obtain ⟨k, hk⟩ := not_forall.mp hs
  have hunit : IsUnit ((g (s : A)).coeff k) := by
    rw [hg]
    exact IsLocalization.map_units (M := p.toIdeal.primeCompl) R
      ⟨(DirectSum.decompose 𝒜 (s : A) k : A), hk⟩
  have hregular := Polynomial.mem_nonZeroDivisors_of_coeff_mem k hunit.mem_nonZeroDivisors
  have hga : g a = 0 := hregular.1 _ (by rw [← map_mul, hsa, map_zero])
  change algebraMap A R (GradedRing.proj 𝒜 n a) = 0
  rw [GradedRing.proj_apply, ← hg, hga, Polynomial.coeff_zero]

/-- A homogeneous numerator vanishing at all relevant primes avoiding f vanishes in A_f.
Its homogeneous annihilator, if disjoint from powers of f, lies in a prime whose homogeneous
core is relevant and avoids f. Vanishing there gives an annihilator outside that core,
contradicting containment of the annihilator ideal. -/
private theorem homogeneous_localization_zero
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b) (u : A) (n : ℕ) (hu : u ∈ 𝒜 n)
    (h : ∀ p : basicOpen 𝒜 f,
      algebraMap A (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) u = 0) :
    algebraMap A (LocalizedModule.Away f A) u = 0 := by
  classical
  by_contra hzero
  let I : Ideal A := (⊥ : Ideal A).colon {u}
  have hI (a : A) : a ∈ I ↔ a * u = 0 := by
    simp [I, Submodule.mem_colon_singleton, smul_eq_mul]
  have hIhom : I.IsHomogeneous 𝒜 := by
    intro i a ha
    apply (hI _).mpr
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hu, (hI a).mp ha]
    simp
  have hdisj : Disjoint (I : Set A) (Submonoid.powers f : Set A) := by
    apply Set.disjoint_left.mpr
    intro s hs hsf
    apply hzero
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
      (LocalizedModule.Away f A) u).mpr ⟨⟨s, hsf⟩, (hI s).mp hs⟩
  obtain ⟨q, hq, hIq, hqdisj⟩ := I.exists_le_prime_disjoint (Submonoid.powers f) hdisj
  have hfq : f ∉ q := fun hmem ↦
    Set.disjoint_left.mp hqdisj hmem (Submonoid.mem_powers f)
  have hfp : f ∉ (q.homogeneousCore 𝒜).toIdeal := fun hmem ↦
    hfq (q.toIdeal_homogeneousCore_le 𝒜 hmem)
  let p : Proj 𝒜 :=
    ⟨q.homogeneousCore 𝒜, hq.homogeneousCore, fun hle ↦
      hfp (hle (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hb hf))⟩
  have hIp : I ≤ p.asHomogeneousIdeal.toIdeal := by
    change I ≤ (q.homogeneousCore 𝒜).toIdeal
    rw [← hIhom.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hIq
  let : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.asHomogeneousIdeal.toIdeal.primeCompl
    (Localization.AtPrime p.asHomogeneousIdeal.toIdeal) u).mp (h ⟨p, hfp⟩)
  exact s.prop (hIp ((hI (s : A)).mpr hs))

/-- Homogeneous primes of a positive-degree basic open detect equality in A_f.
Source: Stacks Project, Lemma 27.8.4, Tag 01M7, localization injectivity argument.
(blueprint: lem-sc-proj-basic-open-localization-detection)

Proof: first localize at the homogeneous elements outside a homogeneous prime p.
This localization B has a Z-grading and injects into the ordinary localization A_p.
To see injectivity, write an ordinary denominator s outside p as a finite sum of
homogeneous components. Some component is outside p, hence is a unit in B. The grading
map sends s to a Laurent polynomial over B with a unit coefficient. McCoy's polynomial
zero-divisor criterion says that this Laurent polynomial is regular: an annihilator
would annihilate every coefficient, including the unit. The grading map is injective
(evaluation at 1 is a left inverse), so s is regular in B. Thus further localization
at ordinary denominators outside p is injective, and vanishing in A_p implies that
each homogeneous component already vanishes in B.

Now write z-w over a common power of f. For a homogeneous component u of its numerator,
the ideal ann(u) is homogeneous: the homogeneous components of a*u have distinct
degrees, so a*u=0 implies that each component of a annihilates u. If no power of f
kills u, ann(u) is disjoint from the powers of f. The prime-existence theorem gives
a prime containing ann(u) and avoiding f. Its homogeneous core is prime, still contains
ann(u), and avoids f; it is relevant since f has positive degree. At this core, the
hypothesis and the preceding injectivity argument force u to vanish in B. Hence some
homogeneous denominator outside the core annihilates u, contradicting containment of
ann(u). A power of f therefore kills every component. A common power kills their sum,
proving z=w. If f is nilpotent, A_f is zero. -/
theorem basicOpen_localization_detection
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b) (z w : LocalizedModule.Away f A)
    (h : ∀ p : basicOpen 𝒜 f,
      IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2) z =
      IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2) w) : z = w := by
  classical
  apply sub_eq_zero.mp
  obtain ⟨a, s, has⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) (z - w)
  have ha (p : basicOpen 𝒜 f) :
      algebraMap A (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) a = 0 := by
    let F := IsLocalization.map (M := Submonoid.powers f) (S := LocalizedModule.Away f A)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2)
    have hz : F (IsLocalization.mk' (LocalizedModule.Away f A) a s) = 0 := by
      rw [has, map_sub]
      exact sub_eq_zero.mpr (h p)
    rw [IsLocalization.map_mk'] at hz
    exact (IsLocalization.map_eq_zero_iff p.1.asHomogeneousIdeal.toIdeal.primeCompl
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) a).mpr
      ((IsLocalization.mk'_eq_zero_iff
        (S := Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) a _).mp hz)
  have hcomp (i : ℕ) :
      algebraMap A (LocalizedModule.Away f A) (DirectSum.decompose 𝒜 a i : A) = 0 := by
    apply homogeneous_localization_zero 𝒜 f b hb hf _ i (DirectSum.decompose 𝒜 a i).prop
    intro p
    exact localization_kernel_isHomogeneous 𝒜 p.1.asHomogeneousIdeal i (ha p)
  have ha0 : algebraMap A (LocalizedModule.Away f A) a = 0 := by
    rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ hcomp i
  rw [← has]
  exact (IsLocalization.mk'_eq_zero_iff (S := LocalizedModule.Away f A) a s).mpr
    ((IsLocalization.map_eq_zero_iff (Submonoid.powers f)
      (LocalizedModule.Away f A) a).mp ha0)

end AlgebraicGeometry.Proj
