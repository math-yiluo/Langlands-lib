import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Mathlib.Algebra.Group.Submonoid.Finsupp

/-! # Pointedness of the positive root monoid -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- The additive closure of a linearly independent integral family is pointed. -/
theorem eq_zero_of_mem_closure_of_neg_mem {ι M : Type*} [Fintype ι] [AddCommGroup M]
    {v : ι → M} (hv : LinearIndependent ℤ v) {x : M}
    (hx : x ∈ AddSubmonoid.closure (Set.range v))
    (hnx : -x ∈ AddSubmonoid.closure (Set.range v)) : x = 0 := by
  classical
  obtain ⟨a, ha⟩ := (AddSubmonoid.mem_closure_range_iff_of_fintype).mp hx
  obtain ⟨c, hc⟩ := (AddSubmonoid.mem_closure_range_iff_of_fintype).mp hnx
  have hsum : ∑ i, ((a i + c i : ℕ) : ℤ) • v i = 0 := by
    have : ∑ i, ((a i + c i : ℕ) : ℤ) • v i = (∑ i, a i • v i) + ∑ i, c i • v i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [natCast_zsmul, add_smul]
    rw [this, ← ha, ← hc, add_neg_cancel]
  have hzero := (Fintype.linearIndependent_iff.mp hv) _ hsum
  rw [ha]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hzero i
  have : a i = 0 := by omega
  rw [this, zero_smul]

/-- The positive root monoid of a split pinning is pointed. -/
theorem SplitPinning.eq_zero_of_mem_positiveRootMonoid_of_neg_mem {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (p : SplitPinning G)
    {x : characterLattice p.torus} (hx : x ∈ p.positiveRootMonoid)
    (hnx : -x ∈ p.positiveRootMonoid) : x = 0 := by
  have hb : LinearIndependent ℤ (fun a : p.base.support => p.rootDatum.root a) :=
    p.base.linearIndepOn_root
  exact eq_zero_of_mem_closure_of_neg_mem hb hx hnx

end Langlands.GroupScheme
