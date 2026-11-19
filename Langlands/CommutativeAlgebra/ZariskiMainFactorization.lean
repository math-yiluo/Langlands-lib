import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType

/-! # A finite subalgebra that agrees with a quasi-finite algebra away from one element -/

namespace Langlands.CommutativeAlgebra.ZariskiMainFactorization

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Zariski's Main Theorem in factorization form. Let `f : A → B` be a quasi-finite map of
finite-type `K`-algebras and let `q` be a prime of `B`. Then `B` contains a `K`-subalgebra
`C` through which `f` factors, such that `A → C` is finite, `C` is of finite type over `K`,
and some `r ∈ C` with `r ∉ q` satisfies `r ^ m * b ∈ C` for every `b : B` and some `m`.
In particular `C[1/r] = B[1/r]`. -/
theorem exists_finite_subalgebra_pow_mul_mem [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (f : A →ₐ[K] B) (hf : f.toRingHom.QuasiFinite) (q : Ideal B) [q.IsPrime] :
    ∃ (C : Subalgebra K B) (hC : ∀ a, f a ∈ C),
      (f.codRestrict C hC).toRingHom.Finite ∧ Algebra.FiniteType K C ∧
      ∃ r ∈ C, r ∉ q ∧ ∀ b : B, ∃ m : ℕ, r ^ m * b ∈ C := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun k => (f.commutes k).symm
  have : Algebra.QuasiFinite A B := hf
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType K A B
  have : Algebra.QuasiFiniteAt A q := inferInstance
  obtain ⟨r, hrq, hr, hm⟩ := Algebra.zariskisMainProperty_iff.mp
    (Algebra.ZariskisMainProperty.of_finiteType (R := A) q)
  choose m hm using hm
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  let t : Set B := insert r ((fun x => r ^ m x * x) '' (s : Set B))
  let D : Subalgebra A B := Algebra.adjoin A t
  have hrD : r ∈ D := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hD : D.toSubmodule.FG := fg_adjoin_of_finite
    ((s.finite_toSet.image _).insert r) (by
      rintro _ (rfl | ⟨x, -, rfl⟩)
      exacts [hr, hm x])
  have hle : Submonoid.powers r ≤ D.toSubmonoid := Submonoid.powers_le.mpr hrD
  have htop : D.saturation (Submonoid.powers r) hle = ⊤ := by
    rw [eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro x hx
    exact ⟨r ^ m x, ⟨m x, rfl⟩, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)⟩
  have hsat : ∀ b : B, ∃ n : ℕ, r ^ n * b ∈ D := by
    intro b
    have hb : b ∈ D.saturation (Submonoid.powers r) hle := htop ▸ Algebra.mem_top
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := Subalgebra.mem_saturation_iff.mp hb
    exact ⟨n, hn⟩
  let C : Subalgebra K B := D.restrictScalars K
  have hC : ∀ a, f a ∈ C := fun a => D.algebraMap_mem a
  have hg : (f.codRestrict C hC).toRingHom = algebraMap A D := by
    ext a
    rfl
  have hfin : (f.codRestrict C hC).toRingHom.Finite := by
    have h : (algebraMap A D).Finite :=
      RingHom.finite_algebraMap.mpr ⟨(Submodule.fg_top _).mpr hD⟩
    rw [hg]
    exact h
  refine ⟨C, hC, hfin, ?_, r, hrD, hrq, hsat⟩
  have hKC : algebraMap K C = (f.codRestrict C hC).toRingHom.comp (algebraMap K A) := by
    ext k
    exact (f.commutes k).symm
  rw [← RingHom.finiteType_algebraMap, hKC]
  exact hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)

end Langlands.CommutativeAlgebra.ZariskiMainFactorization
