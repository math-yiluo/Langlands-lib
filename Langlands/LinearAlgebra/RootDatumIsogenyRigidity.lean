import Langlands.LinearAlgebra.RootDatumIsogeny
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.GroupTheory.OrderOfElement

/-! # Rigidity of isogenies of root data on roots -/

noncomputable section

namespace Langlands.LinearAlgebra

namespace RootDatumIsogeny

/-- A module carrying a perfect integral pairing is torsion free: multiplication by a
nonzero natural number is injective. -/
theorem nsmul_injective_of_isPerfPair {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) [B.IsPerfPair] {n : ℕ} (hn : n ≠ 0) {x y : M}
    (h : n • x = n • y) : x = y := by
  apply (LinearMap.IsPerfPair.bijective_left B).injective
  apply LinearMap.ext
  intro c
  have h' := congrArg (fun z => B z c) h
  simp only [map_nsmul, LinearMap.smul_apply] at h'
  exact nsmul_right_injective hn h'

/-- Two integral linear maps into a module with injective multiplication by nonzero natural
numbers agree everywhere once they agree on a submodule of finite index. -/
theorem linearMap_eq_of_eqOn_finite_quotient {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (hN : ∀ {n : ℕ}, n ≠ 0 → ∀ {x y : N}, n • x = n • y → x = y)
    (L : Submodule ℤ M) [Finite (M ⧸ L)] (f g : M →ₗ[ℤ] N)
    (h : ∀ x ∈ L, f x = g x) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_of_finite (L.mkQ x)).exists_nsmul_eq_zero
  have hmem : n • x ∈ L := by
    apply (Submodule.Quotient.mk_eq_zero L).mp
    change L.mkQ (n • x) = 0
    rw [map_nsmul]
    exact hnx
  apply hN hn.ne'
  rw [← map_nsmul, ← map_nsmul]
  exact h _ hmem

/-- In a reduced integral root datum, if a positive multiple of a root equals a natural
multiple of a root, then the two roots and the two multiples are equal. -/
theorem root_eq_of_smul_eq {ι₂ X₂ Y₂ : Type*} [AddCommGroup X₂] [AddCommGroup Y₂]
    (Q : RootDatum ι₂ X₂ Y₂) [Q.IsReduced] {a b : ℕ} (ha : 0 < a) {i j : ι₂}
    (h : (a : ℤ) • Q.root i = (b : ℤ) • Q.root j) :
    i = j ∧ a = b := by
  have htf : ∀ {n : ℕ}, n ≠ 0 → ∀ {x y : X₂}, n • x = n • y → x = y :=
    fun hn _ _ hxy => nsmul_injective_of_isPerfPair Q.toLinearMap hn hxy
  have h' : a • Q.root i = b • Q.root j := by simpa only [natCast_zsmul] using h
  have hdep : ¬ LinearIndependent ℤ ![Q.root i, Q.root j] := by
    rw [LinearIndependent.pair_iff]
    intro hind
    have := (hind (a : ℤ) (-(b : ℤ)) (by rw [neg_smul, h, add_neg_cancel])).1
    omega
  have hij : i = j := by
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := Q) i j hdep with hij | hij
    · exact Q.root.injective hij
    · exfalso
      apply Q.ne_zero j
      apply htf (Nat.add_pos_left ha b).ne'
      rw [hij, smul_neg] at h'
      rw [smul_zero, add_nsmul, ← h', add_neg_cancel]
  subst hij
  refine ⟨rfl, ?_⟩
  by_contra hab
  apply Q.ne_zero i
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · apply htf (Nat.sub_pos_of_lt hlt).ne'
    rw [smul_zero, sub_nsmul _ hlt.le, ← h', add_neg_cancel]
  · apply htf (Nat.sub_pos_of_lt hlt).ne'
    rw [smul_zero, sub_nsmul _ hlt.le, h', add_neg_cancel]

variable {p : ℕ} {ι X Y ι₂ X₂ Y₂ : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
  [Finite ι] [Finite ι₂]
  [Module.Finite ℤ X] [Module.Finite ℤ Y]
  [Module.Finite ℤ X₂] [Module.Finite ℤ Y₂]
  {P : RootDatum ι X Y} {Q : RootDatum ι₂ X₂ Y₂} [P.IsReduced] [Q.IsReduced]

/-- Two isogenies of reduced integral root data whose weight maps agree on the roots of the
domain have the same root correspondence and the same root factors. -/
theorem indexEquiv_eq_and_rootFactor_eq (f g : RootDatumIsogeny p P Q)
    (h : ∀ i, f.weightMap (P.root i) = g.weightMap (P.root i)) (i : ι) :
    f.indexEquiv i = g.indexEquiv i ∧ f.rootFactor i = g.rootFactor i := by
  have hi := h i
  rw [f.root_weightMap, g.root_weightMap] at hi
  exact root_eq_of_smul_eq Q (f.rootFactor_pos i) hi

/-- Two isogenies of reduced integral root data whose weight maps agree on the roots of the
domain have coweight maps that agree on the coroots of the codomain. -/
theorem coweightMap_coroot_eq (f g : RootDatumIsogeny p P Q)
    (h : ∀ i, f.weightMap (P.root i) = g.weightMap (P.root i)) (j : ι₂) :
    f.coweightMap (Q.coroot j) = g.coweightMap (Q.coroot j) := by
  obtain ⟨i, rfl⟩ := f.indexEquiv.surjective j
  obtain ⟨hidx, hfac⟩ := indexEquiv_eq_and_rootFactor_eq f g h i
  rw [f.coroot_coweightMap, hidx, g.coroot_coweightMap, hfac]

/-- If the roots of the domain span a subgroup of finite index, two isogenies of reduced
integral root data whose weight maps agree on these roots have the same weight map. -/
theorem weightMap_eq_of_finite_rootSpan (f g : RootDatumIsogeny p P Q)
    [Finite (X ⧸ P.rootSpan ℤ)]
    (h : ∀ i, f.weightMap (P.root i) = g.weightMap (P.root i)) :
    f.weightMap = g.weightMap := by
  apply linearMap_eq_of_eqOn_finite_quotient
    (fun hn _ _ hxy => nsmul_injective_of_isPerfPair Q.toLinearMap hn hxy) (P.rootSpan ℤ)
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact h i
  · simp
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x _ hx
    rw [map_smul, map_smul, hx]

/-- If the coroots of the codomain span a subgroup of finite index, two isogenies of reduced
integral root data whose weight maps agree on the roots of the domain have the same weight
map. -/
theorem weightMap_eq_of_finite_corootSpan (f g : RootDatumIsogeny p P Q)
    [Finite (Y₂ ⧸ Q.corootSpan ℤ)]
    (h : ∀ i, f.weightMap (P.root i) = g.weightMap (P.root i)) :
    f.weightMap = g.weightMap := by
  have hco : f.coweightMap = g.coweightMap := by
    apply linearMap_eq_of_eqOn_finite_quotient
      (fun hn _ _ hxy => nsmul_injective_of_isPerfPair P.toLinearMap.flip hn hxy)
      (Q.corootSpan ℤ)
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      exact coweightMap_coroot_eq f g h j
    · simp
    · intro x y _ _ hx hy
      rw [map_add, map_add, hx, hy]
    · intro a x _ hx
      rw [map_smul, map_smul, hx]
  apply LinearMap.ext
  intro x
  apply (LinearMap.IsPerfPair.bijective_left Q.toLinearMap).injective
  apply LinearMap.ext
  intro y
  rw [f.pairing_apply, g.pairing_apply, hco]

end RootDatumIsogeny

end Langlands.LinearAlgebra
