import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Local algebra of a finite map with one prime over a base prime -/

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommutativeAlgebra

/-- A principal base neighborhood on which a ring map, and every further
localization at a multiple of its defining element, is surjective. -/
structure PrincipalSurjectivityNeighborhood
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) where
  element : R
  not_mem : element ∉ p
  surjective : ∀ r, element ∣ r → Function.Surjective (Localization.awayMap f r)

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity of the local map spreads to a principal base neighborhood when
there is just one prime above the base prime. No condition on the kernel is needed. -/
theorem exists_awayMap_surjective_of_singleton
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    [q.LiesOver p] (hq : p.primesOver S = {q})
    (H : Function.Surjective
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' →
      Function.Surjective (Localization.awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : ∃ a, ∃ b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp
      (H (algebraMap S (Localization.AtPrime q) x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  refine ⟨∏ i ∈ s, b i, (show _ ∈ p.primeCompl from prod_mem fun _ _ ↦ hbp _), ?_⟩
  intro r' hr'
  have H : (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r'))).range ≤
      (Localization.awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top, Subalgebra.map_le, ← hs, Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * (∏ i ∈ s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [Localization.awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr', ← Finset.prod_erase_mul s b hxs, map_mul, map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Localization.Away.invSelf, Localization.mk_eq_mk', Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_mk', ← Algebra.smul_def,
    IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

/-- Choose principal neighborhood data from a surjective local map and a
singleton prime fiber of a finite algebra. -/
noncomputable def principalSurjectivityNeighborhood
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    [q.LiesOver p] (hq : p.primesOver S = {q})
    (H : Function.Surjective
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p))) :
    PrincipalSurjectivityNeighborhood (algebraMap R S) p :=
  let h := exists_awayMap_surjective_of_singleton hq H
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

end Langlands.CommutativeAlgebra
