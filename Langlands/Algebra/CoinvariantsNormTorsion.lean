import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

/-! # Torsion-free permutation coinvariants and injectivity by a norm argument -/

noncomputable section

namespace Langlands.CoinvariantsNorm

open Representation

variable {G : Type*} [Group G]

section Permutation

variable {V ι : Type*} [AddCommGroup V] [Module ℤ V]
  (ρ : Representation ℤ G V) (b : Module.Basis ι ℤ V)

/-- The orbit relation of a basis permuted by a representation. -/
def orbitSetoid : Setoid ι where
  r i j := ∃ g : G, ρ g (b i) = b j
  iseqv :=
    { refl := fun i => ⟨1, by rw [map_one]; rfl⟩
      symm := fun {i j} ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, Representation.inv_self_apply]⟩
      trans := fun {i j l} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by
        rw [map_mul, Module.End.mul_apply, hg, hh]⟩ }

/-- **Coinvariants of a permutation lattice are torsion-free.** If a representation
permutes an integral basis, then a class in the coinvariants with a nonzero integral
multiple equal to zero is zero. -/
theorem eq_zero_of_smul_eq_zero_of_permuted
    (hb : ∀ (g : G) (i : ι), ∃ j, ρ g (b i) = b j)
    {n : ℕ} (hn : n ≠ 0) {x : Coinvariants ρ} (hx : n • x = 0) : x = 0 := by
  classical
  let s := orbitSetoid ρ b
  let rep : ι → ι := fun i => (Quotient.mk s i).out
  have hrep_rel : ∀ i, s (rep i) i := fun i => Quotient.mk_out (s := s) i
  have hrep_eq : ∀ i j, s i j → rep i = rep j := fun i j h =>
    congrArg Quotient.out (Quotient.sound (s := s) h)
  let φ : V →ₗ[ℤ] V := b.constr ℕ (fun i => b (rep i))
  have hφb : ∀ i, φ (b i) = b (rep i) := fun i => b.constr_basis ℕ _ i
  -- `v - φ v` lies in the augmentation submodule.
  have hle : Submodule.map (LinearMap.id - φ) (Submodule.span ℤ (Set.range b)) ≤
      Coinvariants.ker ρ := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hg⟩ := hrep_rel i
    rw [LinearMap.sub_apply, LinearMap.id_apply, hφb, ← hg]
    exact Coinvariants.sub_mem_ker g _
  have hsub : ∀ v, Coinvariants.mk ρ (v - φ v) = 0 := by
    intro v
    rw [Coinvariants.mk_eq_zero]
    exact hle (Submodule.mem_map_of_mem (b.span_eq ▸ Submodule.mem_top))
  -- `φ` is invariant, hence descends to the coinvariants.
  have hinv : ∀ g : G, φ ∘ₗ ρ g = φ := by
    intro g
    apply b.ext
    intro i
    obtain ⟨j, hj⟩ := hb g i
    change φ (ρ g (b i)) = φ (b i)
    rw [hj, hφb, hφb]
    exact congrArg b (hrep_eq i j ⟨g, hj⟩).symm
  let φbar := Coinvariants.lift ρ φ hinv
  induction x using Coinvariants.induction_on with
  | h v =>
    have hx' : Coinvariants.mk ρ (n • v) = 0 := by rw [map_nsmul]; exact hx
    have h0 : φ (n • v) = 0 := by
      have : φbar (Coinvariants.mk ρ (n • v)) = 0 := by rw [hx', map_zero]
      simpa [φbar] using this
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ] at h0
    have hφv : φ v = 0 :=
      ((b.smul_eq_zero).mp h0).resolve_left (by exact_mod_cast hn)
    have := hsub v
    rwa [hφv, sub_zero] at this

end Permutation

section Norm

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  (ρM : Representation ℤ G M) (ρN : Representation ℤ G N)

/-- **Injectivity on coinvariants by a norm argument.** Let `j : M → N` be an injective
equivariant map, suppose that `G` acts on `N` through finitely many operators and that
the coinvariants of `M` are torsion-free. Then every map of coinvariants descending `j`
is injective. -/
theorem injective_of_finite_range
    (j : M →ₗ[ℤ] N) (hj : Function.Injective j)
    (heq : ∀ (g : G) (x : M), j (ρM g x) = ρN g (j x))
    (hfin : (Set.range ρN).Finite)
    (htf : ∀ (n : ℕ) (x : Coinvariants ρM), n ≠ 0 → n • x = 0 → x = 0)
    (m : Coinvariants ρM →ₗ[ℤ] Coinvariants ρN)
    (hm : ∀ x, m (Coinvariants.mk ρM x) = Coinvariants.mk ρN (j x)) :
    Function.Injective m := by
  classical
  let S : Finset (Module.End ℤ N) := hfin.toFinset
  have hS : ∀ f, f ∈ S ↔ f ∈ Set.range ρN := fun f => Set.Finite.mem_toFinset hfin
  let sec : Module.End ℤ N → G := fun f =>
    if h : f ∈ Set.range ρN then h.choose else 1
  have hsec : ∀ f ∈ S, ρN (sec f) = f := by
    intro f hf
    have h : f ∈ Set.range ρN := (hS f).mp hf
    simp only [sec, h, ↓reduceDIte]
    exact h.choose_spec
  -- The norm on `N` is invariant.
  let NmN : N →ₗ[ℤ] N := ∑ f ∈ S, f
  have hNmN : ∀ y, NmN y = ∑ f ∈ S, f y := fun y => by
    simp only [NmN, LinearMap.sum_apply]
  have hinv : ∀ g : G, NmN ∘ₗ ρN g = NmN := by
    intro g
    apply LinearMap.ext
    intro y
    change NmN (ρN g y) = NmN y
    rw [hNmN, hNmN]
    refine Finset.sum_nbij' (fun f => f * ρN g) (fun f => f * ρN g⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro f hf
      obtain ⟨a, rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨a * g, map_mul ρN a g⟩
    · intro f hf
      obtain ⟨a, rfl⟩ := (hS f).mp hf
      exact (hS _).mpr ⟨a * g⁻¹, map_mul ρN a g⁻¹⟩
    · intro f _
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    · intro f _
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    · intro f _
      rfl
  let NmNbar := Coinvariants.lift ρN NmN hinv
  -- The norm on `M` through chosen lifts.
  let NmM : M →ₗ[ℤ] M := ∑ f ∈ S, ρM (sec f)
  have hNmM : ∀ x, NmM x = ∑ f ∈ S, ρM (sec f) x := fun x => by
    simp only [NmM, LinearMap.sum_apply]
  have hjNm : ∀ x, j (NmM x) = NmN (j x) := by
    intro x
    rw [hNmM, hNmN, map_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [heq, hsec f hf]
  have hdiff : ∀ x, Coinvariants.mk ρM (NmM x - S.card • x) = 0 := by
    intro x
    have : NmM x - S.card • x = ∑ f ∈ S, (ρM (sec f) x - x) := by
      rw [hNmM, Finset.sum_sub_distrib, Finset.sum_const]
    rw [this, map_sum]
    exact Finset.sum_eq_zero fun f _ =>
      (Coinvariants.mk_eq_zero _).mpr (Coinvariants.sub_mem_ker _ _)
  have hcard : S.card ≠ 0 := by
    have : (1 : Module.End ℤ N) ∈ S := (hS 1).mpr ⟨1, map_one ρN⟩
    exact (Finset.card_pos.mpr ⟨1, this⟩).ne'
  rw [injective_iff_map_eq_zero]
  intro c hc
  induction c using Coinvariants.induction_on with
  | h x =>
    rw [hm] at hc
    have h1 : NmN (j x) = 0 := by
      have : NmNbar (Coinvariants.mk ρN (j x)) = 0 := by rw [hc, map_zero]
      simpa [NmNbar] using this
    have h2 : NmM x = 0 := hj (by rw [hjNm, h1, map_zero])
    apply htf _ _ hcard
    have := hdiff x
    rw [h2, zero_sub, map_neg, neg_eq_zero, map_nsmul] at this
    exact this

end Norm

end Langlands.CoinvariantsNorm
