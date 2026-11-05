import Langlands.HarmonicAnalysis.TorusFourierInversion
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # Annihilators of finite-index sublattices in a finite product of circles

For a subgroup `Λ` of `ℤ^J` of finite index, its annihilator `Λ^⊥` in the torus `J → Circle`
is a finite subgroup, and the `n ∈ ℤ^J` whose character `χₙ` is trivial on `Λ^⊥` are exactly the
elements of `Λ`. Consequently the partial Fourier series of a function over `Λ` is the average of
the function over the cosets of `Λ^⊥`. In the proof of Waldspurger's Proposition VII.2.1, `Λ` is
the image of `A_G` in the lattice of `G` and `Λ^⊥` the kernel of `Im X(G) → Im X(A_G)`.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped ComplexConjugate

namespace Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J]

/-- The annihilator `Λ^⊥ = {z | χₘ(z) = 1 for all m ∈ Λ}` of a subgroup `Λ` of `ℤ^J` in the
torus `J → Circle`. -/
def latticeAnnihilator (Λ : AddSubgroup (J → ℤ)) : Subgroup (J → Circle) where
  carrier := {z | ∀ m ∈ Λ, torusCharacter m z = 1}
  one_mem' := fun m _ => by simp [torusCharacter]
  mul_mem' := fun {z w} hz hw m hm => by
    rw [torusCharacter_mul, hz m hm, hw m hm, one_mul]
  inv_mem' := fun {z} hz m hm => by
    rw [torusCharacter_inv, hz m hm, map_one]

variable (Λ : AddSubgroup (J → ℤ))

theorem mem_latticeAnnihilator {z : J → Circle} :
    z ∈ latticeAnnihilator Λ ↔ ∀ m ∈ Λ, torusCharacter m z = 1 :=
  Iff.rfl

/-- The annihilator of a finite-index subgroup is finite: its coordinates are `N`-th roots of
unity, `N` the index. -/
theorem finite_latticeAnnihilator [Λ.FiniteIndex] : Finite (latticeAnnihilator Λ) := by
  classical
  set N := Λ.index
  have hN : 0 < N := Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero
  have hsub : (latticeAnnihilator Λ : Set (J → Circle)) ⊆
      Set.univ.pi fun _ => {w : Circle | (w : ℂ) ∈ Polynomial.nthRoots N (1 : ℂ)} := by
    intro z hz j _
    have hmem : N • (Pi.single j 1 : J → ℤ) ∈ Λ := Λ.nsmul_index_mem _
    have h := hz _ hmem
    show ((z j : Circle) : ℂ) ∈ Polynomial.nthRoots N (1 : ℂ)
    rw [Polynomial.mem_nthRoots hN]
    rw [torusCharacter, Finset.prod_eq_single j] at h
    · simpa [Pi.single_apply] using h
    · intro i _ hij
      simp [hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hfin : (Set.univ.pi fun _ : J => {w : Circle | (w : ℂ) ∈ Polynomial.nthRoots N (1 : ℂ)}).Finite := by
    refine Set.Finite.pi fun _ => ?_
    exact ((Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.preimage
      (Circle.coe_injective.injOn)).subset fun w hw => by
        simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
        exact hw
  exact (hfin.subset hsub).to_subtype

/-- Every `m ∈ Λ` has `χₘ` trivial on `Λ^⊥`. -/
theorem isTrivialOn_latticeAnnihilator_of_mem {m : J → ℤ} (hm : m ∈ Λ) :
    IsTrivialOn (latticeAnnihilator Λ) m :=
  fun w => w.2 m hm

/-- **Double annihilator**: for `Λ` of finite index, `χₘ` is trivial on `Λ^⊥` only if `m ∈ Λ`.
A character of the finite group `ℤ^J / Λ` that is nontrivial at `m` gives a point of `Λ^⊥` where
`χₘ` is not `1`. -/
theorem mem_of_isTrivialOn_latticeAnnihilator [Λ.FiniteIndex] {m : J → ℤ}
    (h : IsTrivialOn (latticeAnnihilator Λ) m) : m ∈ Λ := by
  classical
  by_contra hm
  let π := QuotientAddGroup.mk' Λ
  have : Fintype ((J → ℤ) ⧸ Λ) := Fintype.ofFinite _
  have hne : π m ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ, hψ⟩ := AddChar.exists_apply_ne_zero.mpr hne
  have hnorm : ∀ q, ‖ψ q‖ = 1 := fun q => by
    refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card ((J → ℤ) ⧸ Λ)) ?_
      Fintype.card_ne_zero
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let z : J → Circle := fun j =>
    ⟨ψ (π (Pi.single j 1)), show ψ (π (Pi.single j 1)) ∈ Metric.sphere (0 : ℂ) 1 from
      mem_sphere_zero_iff_norm.2 (hnorm _)⟩
  have hsum : ∀ (s : Finset J) (a : J → (J → ℤ) ⧸ Λ),
      ψ (∑ j ∈ s, a j) = ∏ j ∈ s, ψ (a j) := by
    intro s a
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]
  have hz : ∀ k : J → ℤ, torusCharacter k z = ψ (π k) := by
    intro k
    have hdecomp : k = ∑ j, k j • (Pi.single j 1 : J → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hdecomp]
    rw [map_sum, hsum, torusCharacter]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zsmul, AddChar.map_zsmul_eq_zpow, Circle.coe_zpow]
  have hzmem : z ∈ latticeAnnihilator Λ := fun k hk => by
    rw [hz, show π k = 0 from (QuotientAddGroup.eq_zero_iff k).mpr hk, AddChar.map_zero_eq_one]
  exact hψ (by rw [← hz]; exact h ⟨z, hzmem⟩)

theorem isTrivialOn_latticeAnnihilator_iff [Λ.FiniteIndex] {m : J → ℤ} :
    IsTrivialOn (latticeAnnihilator Λ) m ↔ m ∈ Λ :=
  ⟨mem_of_isTrivialOn_latticeAnnihilator Λ, isTrivialOn_latticeAnnihilator_of_mem Λ⟩

/-- **Partial Fourier series over a finite-index sublattice**: for `f` continuous with absolutely
summable Fourier coefficients, `∑_{n ∈ Λ} f̂(n) conj(χₙ(z)) = μ(T) |Λ^⊥|⁻¹ ∑_{w ∈ Λ^⊥} f(z w)`. -/
theorem hasSum_torusFourierCoeff_mul_conj_mem (μ : Measure (J → Circle)) [IsFiniteMeasure μ]
    [μ.IsMulLeftInvariant] [Λ.FiniteIndex] [Fintype (latticeAnnihilator Λ)]
    [DecidablePred (· ∈ Λ)] {f : (J → Circle) → ℂ} (hf : Continuous f)
    (hs : Summable fun n => ‖torusFourierCoeff μ f n‖) (z : J → Circle) :
    HasSum (fun n => if n ∈ Λ then torusFourierCoeff μ f n * conj (torusCharacter n z) else 0)
      ((μ.real univ : ℂ) / Fintype.card (latticeAnnihilator Λ) *
        ∑ w : latticeAnnihilator Λ, f (z * w)) := by
  classical
  convert hasSum_torusFourierCoeff_mul_conj_isTrivialOn μ (latticeAnnihilator Λ) hf hs z using 1
  funext n
  exact if_congr (isTrivialOn_latticeAnnihilator_iff Λ).symm rfl rfl

end Langlands.HarmonicAnalysis.TorusFourier
