import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finset.Max

/-! # Separation of spans by triangularity with respect to character lines -/

noncomputable section

namespace Langlands

universe uK uV uI uR

variable {k : Type uK} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  {ι : Type uI} {R : Type uR} [LinearOrder R]

/-- A span of triangular vectors with distinct nonzero leading lines is
disjoint from the span of any set of other independent lines. -/
def TriangularSpanSeparationStatement : Prop :=
  ∀ (x y : ι → V) (rank : ι → R) (P Q : Set ι),
    LinearIndependent k x → Disjoint P Q →
    (∀ i ∈ Q, ∃ a : k, a ≠ 0 ∧
      y i - a • x i ∈ Submodule.span k (x '' {j | rank j < rank i})) →
    Disjoint (Submodule.span k (x '' P)) (Submodule.span k (y '' Q))

/-- Extract the coefficient of a leading line of maximal rank in a finite combination. -/
theorem triangularSpanSeparation :
    TriangularSpanSeparationStatement (k := k) (V := V) (ι := ι) (R := R) := by
  classical
  intro x y rank P Q hx hPQ hTri
  let L := Finsupp.linearCombination k x
  obtain ⟨I, hI⟩ := L.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hx.finsuppLinearCombination_injective)
  let coeff (i : ι) := (Finsupp.lapply i : (ι →₀ k) →ₗ[k] k).comp I
  have hCoeff (i j : ι) : coeff i (x j) = if j = i then 1 else 0 := by
    change I (x j) i = _
    have hL : L (Finsupp.single j 1) = x j := by simp [L]
    rw [← hL]
    change (I.comp L) (Finsupp.single j 1) i = _
    rw [hI, LinearMap.id_apply, Finsupp.single_apply]
  have hZero (i : ι) (S : Set ι) (hS : ∀ j ∈ S, j ≠ i)
      (v : V) (hv : v ∈ Submodule.span k (x '' S)) : coeff i v = 0 := by
    apply LinearMap.mem_ker.mp
    apply (Submodule.span_le.mpr ?_) hv
    rintro _ ⟨j, hj, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [hCoeff, ite_eq_right (hS j hj)])
  apply Submodule.disjoint_def.mpr
  intro v hv hv'
  have hRange : y '' Q = Set.range (fun j : Q => y j.val) := by
    ext w
    exact ⟨fun ⟨j, hj, he⟩ => ⟨⟨j, hj⟩, he⟩,
      fun ⟨j, he⟩ => ⟨j.val, j.property, he⟩⟩
  rw [hRange] at hv'
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv'
  by_contra hv₀
  have hNonempty : c.support.Nonempty := by
    by_contra hEmpty
    have hc₀ : c = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
    exact hv₀ (by simpa [hc₀] using hc.symm)
  obtain ⟨i, hi, hMax⟩ := c.support.exists_max_image (fun j => rank j.val) hNonempty
  have hCoeffV : coeff i.val v = 0 :=
    hZero i.val P (fun j hj he => (Set.disjoint_left.mp hPQ (he ▸ hj) i.property)) v hv
  have hLead : coeff i.val (y i.val) ≠ 0 := by
    obtain ⟨a, ha, h⟩ := hTri i.val i.property
    have hz := hZero i.val {j | rank j < rank i.val}
      (fun j hj he => by subst j; exact lt_irrefl _ hj) _ h
    rw [map_sub, map_smul, hCoeff, ite_eq_left rfl, smul_eq_mul, mul_one, sub_eq_zero] at hz
    rwa [hz]
  have hOther (j : Q) (hj : j ∈ c.support) (hne : j ≠ i) :
      coeff i.val (y j.val) = 0 := by
    obtain ⟨a, _, h⟩ := hTri j.val j.property
    have hz := hZero i.val {b | rank b < rank j.val}
      (fun b hb he => by subst b; exact not_lt_of_ge (hMax j hj) hb) _ h
    rw [map_sub, map_smul, hCoeff, ite_eq_right (fun he => hne (Subtype.ext he)),
      smul_zero, sub_zero] at hz
    exact hz
  rw [← hc, Finsupp.sum, map_sum, Finset.sum_eq_single_of_mem i hi] at hCoeffV
  · rw [map_smul, smul_eq_mul] at hCoeffV
    exact (mul_ne_zero (Finsupp.mem_support_iff.mp hi) hLead) hCoeffV
  · intro j hj hne
    rw [map_smul, hOther j hj hne, smul_zero]

end Langlands
