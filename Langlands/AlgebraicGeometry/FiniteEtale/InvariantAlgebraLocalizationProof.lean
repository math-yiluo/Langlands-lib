import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraStatements
import Mathlib.Data.Finset.Lattice.Fold

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

private theorem exists_common_pow_mul_eq {ι C : Type*} [Finite ι] [CommMonoid C]
    (x : C) (a b : ι → C)
    (h : ∀ i, ∃ n : ℕ, x ^ n * a i = x ^ n * b i) :
    ∃ n : ℕ, ∀ i, x ^ n * a i = x ^ n * b i := by
  classical
  let _ := Fintype.ofFinite ι
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
    (Finset.le_sup (f := k) (Finset.mem_univ i))
  rw [hm, pow_add]
  calc
    (x ^ k i * x ^ m) * a i = x ^ m * (x ^ k i * a i) := by ac_rfl
    _ = x ^ m * (x ^ k i * b i) := congrArg (x ^ m * ·) (hk i)
    _ = (x ^ k i * x ^ m) * b i := by ac_rfl

/-- Every fixed localized element has a fixed numerator after clearing a power
of the specified base-ring element. -/
theorem invariantAlgebraLocalization (R A B G : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (r : R) [IsLocalization.Away (algebraMap R A r) B]
    [Group G] [Finite G]
    [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G R A] [SMulCommClass G R B]
    (hequiv : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a) :
    InvariantAlgebraLocalization R A B G r hequiv := by
  intro b hb
  have hbase (m : ℕ) :
      algebraMap A B ((algebraMap R A r) ^ m) = algebraMap R B (r ^ m) := by
    rw [← map_pow, ← IsScalarTower.algebraMap_apply R A B]
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap R A r) b
  have ha' : algebraMap A B a = algebraMap R B (r ^ n) * b := by
    simpa only [← map_pow, ← IsScalarTower.algebraMap_apply R A B, mul_comm] using ha.symm
  have hfix (g : G) : algebraMap A B (g • a) = algebraMap A B a := by
    rw [hequiv, ha', smul_mul', smul_algebraMap, hb g]
  obtain ⟨m, hm⟩ := exists_common_pow_mul_eq (algebraMap R A r)
    (fun g : G => g • a) (fun _ => a)
    (fun g => IsLocalization.Away.exists_of_eq (algebraMap R A r) (hfix g))
  refine ⟨(algebraMap R A r) ^ m * a, ?_, m + n, ?_⟩
  · intro g
    rw [smul_mul', ← map_pow, smul_algebraMap, map_pow]
    exact hm g
  · rw [map_mul, hbase, ha', ← mul_assoc, ← map_mul, ← pow_add]

end Langlands.AlgebraicGeometry.FiniteEtale
