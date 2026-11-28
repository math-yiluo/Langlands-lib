import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Basic

/-! # Integrality at a finite place of coordinates in a finite-dimensional algebra -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open IsDedekindDomain Polynomial NumberField

universe u v w

section Finiteness

variable {F : Type u} [Field F] [NumberField F]

/-- Only finitely many finite places make one of finitely many elements non-integral. -/
theorem finite_setOf_exists_one_lt (s : Finset F) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ c ∈ s, 1 < v.valuation F c}.Finite := by
  have : {v : HeightOneSpectrum (𝓞 F) | ∃ c ∈ s, 1 < v.valuation F c} =
      ⋃ c ∈ s, HeightOneSpectrum.Support (𝓞 F) c := by
    ext v
    simp [HeightOneSpectrum.Support]
  rw [this]
  exact s.finite_toSet.biUnion fun c _ => HeightOneSpectrum.Support.finite (𝓞 F) c

/-- A nonzero element is a unit at all but finitely many finite places. -/
theorem finite_setOf_valuation_ne_one {c : F} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F c ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) c).union
    (HeightOneSpectrum.Support.finite (𝓞 F) c⁻¹)).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq, HeightOneSpectrum.Support, Set.mem_union] at hv ⊢
  rcases lt_or_gt_of_ne hv with h | h
  · right
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨by rwa [Valuation.pos_iff], h⟩
  · left
    exact h

end Finiteness

variable {F : Type u} [Field F] [NumberField F] {A : Type v} [Ring A] [Algebra F A]
  {ι : Type w} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F A)
  (v : HeightOneSpectrum (𝓞 F))

/-- All coordinates of `a` in the basis `β` are integral at `v`. -/
def IntAt (a : A) : Prop := ∀ i, v.valuation F (β.repr a i) ≤ 1

/-- The structure constants of `β` and the coordinates of `1` are integral at `v`. -/
def BasisIntAt : Prop :=
  (∀ i j k, v.valuation F (β.repr (β i * β j) k) ≤ 1) ∧ ∀ k, v.valuation F (β.repr 1 k) ≤ 1

variable {β v}

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_add {a b : A} (ha : IntAt β v a) (hb : IntAt β v b) : IntAt β v (a + b) :=
  fun i => by
    rw [map_add, Finsupp.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_neg {a : A} (ha : IntAt β v a) : IntAt β v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
  exact ha i

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_sub {a b : A} (ha : IntAt β v a) (hb : IntAt β v b) : IntAt β v (a - b) := by
  rw [sub_eq_add_neg]
  exact intAt_add ha (intAt_neg hb)

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_smul {c : F} (hc : v.valuation F c ≤ 1) {a : A} (ha : IntAt β v a) :
    IntAt β v (c • a) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (ha i)

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_zero : IntAt β v (0 : A) := fun i => by simp

omit [Fintype ι] in
theorem intAt_basis (j : ι) : IntAt β v (β j) := fun i => by
  rw [β.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_sum {κ : Type*} {s : Finset κ} {a : κ → A} (ha : ∀ i ∈ s, IntAt β v (a i)) :
    IntAt β v (∑ i ∈ s, a i) := fun k => by
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact Valuation.map_sum_le _ fun i hi => ha i hi k

omit [Fintype ι] [DecidableEq ι] in
theorem intAt_one (hB : BasisIntAt β v) : IntAt β v (1 : A) := hB.2

omit [DecidableEq ι] in
theorem intAt_mul (hB : BasisIntAt β v) {a b : A} (ha : IntAt β v a) (hb : IntAt β v b) :
    IntAt β v (a * b) := by
  have h : a * b = ∑ i, ∑ j, (β.repr a i * β.repr b j) • (β i * β j) := by
    conv_lhs => rw [← β.sum_repr a, ← β.sum_repr b]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  rw [h]
  exact intAt_sum fun i _ => intAt_sum fun j _ =>
    intAt_smul (by rw [map_mul]; exact mul_le_one' (ha i) (hb j)) (fun k => hB.1 i j k)

/-- If the structure constants of `β` and the coordinates of `1` are integral at `v`,
an element with integral coordinates is a root of a monic polynomial over `F` with
`v`-integral coefficients. The polynomial is the characteristic polynomial of left
multiplication by that element. -/
theorem exists_monic_of_intAt (hB : BasisIntAt β v) {a : A} (ha : IntAt β v a) :
    ∃ f : F[X], f.Monic ∧ (∀ i, v.valuation F (f.coeff i) ≤ 1) ∧ aeval a f = 0 := by
  classical
  have : Module.Finite F A := Module.Finite.of_basis β
  let φ := Algebra.lmul F A a
  let M := LinearMap.toMatrix β β φ
  have hM : ∀ k j, v.valuation F (M k j) ≤ 1 := fun k j => by
    simp only [M, LinearMap.toMatrix_apply]
    exact intAt_mul hB ha (intAt_basis j) k
  let O := (v.valuation F).integer
  let M' : Matrix ι ι O := fun k j => ⟨M k j, hM k j⟩
  have hMM' : M = M'.map O.subtype := by ext k j; rfl
  refine ⟨φ.charpoly, LinearMap.charpoly_monic φ, fun i => ?_, ?_⟩
  · rw [← LinearMap.charpoly_toMatrix φ β]
    change v.valuation F (M.charpoly.coeff i) ≤ 1
    rw [hMM', Matrix.charpoly_map, coeff_map]
    exact (M'.charpoly.coeff i).2
  · have h0 := LinearMap.aeval_self_charpoly φ
    have h1 : aeval φ φ.charpoly = Algebra.lmul F A (aeval a φ.charpoly) :=
      aeval_algHom_apply (Algebra.lmul F A) a φ.charpoly
    rw [h1] at h0
    have := congrArg (fun g : Module.End F A => g 1) h0
    simpa using this

end Langlands.CentralSimple.Landherr
