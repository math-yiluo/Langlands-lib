import Langlands.Group.RootPairingCoxeterProof
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear

/-! # Trivial Weyl stabilizers of regular weights and coweights -/

noncomputable section

universe u₁ u₂ u₃ u₄

namespace Langlands.LinearAlgebra

open IsAddIndecomposable

variable {ι : Type u₁} {R : Type u₂} {M : Type u₃} {N : Type u₄}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

/-- A Weyl element preserving the positive roots of a regular functional is
the identity. No reducedness or spanning hypothesis is needed. -/
theorem weyl_eq_one_of_preserves_positive_roots
    (f : Module.Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) (w : P.weylGroup)
    (hpos : ∀ i, 0 < f (P.root i) → 0 < f (w • P.root i)) : w = 1 := by
  obtain ⟨_, C, cs, _, _, hLength⟩ :=
    Langlands.Group.rootPairingWeylCoxeterStatement_proof ι R M N P f hf
  by_contra hw
  obtain ⟨b, hb⟩ := cs.exists_rightDescent_of_ne_one hw
  have hi : cs.length w < cs.length (w * cs.simple b) :=
    (hLength w b).mpr (hpos b (baseOf_subset_pos P.root (f : M →+ R) b.2))
  exact (not_lt_of_gt hi) hb

/-- A regular functional has trivial stabilizer for pullback along the
natural Weyl action on the weight space. -/
theorem weyl_eq_one_of_fixed_regular_functional
    (f : Module.Dual R M) (hf : ∀ i, f (P.root i) ≠ 0) (w : P.weylGroup)
    (hfixed : ∀ x : M, f (w • x) = f x) : w = 1 := by
  apply weyl_eq_one_of_preserves_positive_roots P f hf w
  intro i hi
  rwa [hfixed]

/-- The contravariant Weyl action on a root-regular coweight has trivial
stabilizer. -/
theorem weyl_eq_one_of_fixed_regular_coweight
    (x : N) (hx : ∀ i, P.root' i x ≠ 0) (w : P.weylGroup)
    (hfixed : w.val.coweightEquiv x = x) : w = 1 := by
  let f : Module.Dual R M := P.flip.toLinearMap x
  apply weyl_eq_one_of_fixed_regular_functional P f hx w
  intro y
  have h := w.val.toLinearMap_weightEquiv y x
  change f (w • y) = P.toLinearMap y (w.val.coweightEquiv x) at h
  rw [hfixed] at h
  exact h

section FiniteIndex

variable [Fintype ι]

omit [Finite ι] [P.IsCrystallographic] in
/-- The canonical root form is strictly positive on each root. -/
theorem rootForm_root_pos (i : ι) :
    0 < P.RootForm (P.root i) (P.root i) := by
  rw [P.rootForm_apply_apply]
  apply Finset.sum_pos'
  · intro j _
    exact mul_self_nonneg _
  · exact ⟨i, Finset.mem_univ _, by simp⟩

omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
/-- Pairing with a root under the canonical form is a positive multiple of
evaluation by the corresponding coroot. -/
theorem two_mul_rootForm_root (i : ι) (x : M) :
    2 * P.RootForm x (P.root i) =
      P.RootForm (P.root i) (P.root i) * P.coroot' i x := by
  have h := congrArg (fun y : N => P.toLinearMap x y)
    (P.rootForm_self_smul_coroot i)
  have hs : P.RootForm (P.root i) x = P.RootForm x (P.root i) :=
    P.rootForm_symmetric.eq _ _
  simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul] at h
  rw [P.toLinearMap_apply_apply_Polarization, hs] at h
  exact h.symm

/-- The natural Weyl action on a coroot-regular weight has trivial stabilizer.
In particular this applies to any weight with strictly positive or strictly
negative value on every positive coroot, once that regularity is proved. -/
theorem weyl_eq_one_of_fixed_regular_weight
    (x : M) (hx : ∀ i, P.coroot' i x ≠ 0) (w : P.weylGroup)
    (hfixed : w • x = x) : w = 1 := by
  let f : Module.Dual R M := P.RootForm x
  have hf : ∀ i, f (P.root i) ≠ 0 := by
    intro i hi
    have he := two_mul_rootForm_root P i x
    change 2 * f (P.root i) = _ at he
    rw [hi, mul_zero] at he
    exact (mul_ne_zero (ne_of_gt (rootForm_root_pos P i)) (hx i)) he.symm
  let B : P.InvariantForm :=
    { form := P.RootForm
      symm := P.rootForm_symmetric
      ne_zero := fun i => ne_of_gt (rootForm_root_pos P i)
      isOrthogonal_reflection := P.rootForm_reflection_reflection_apply }
  apply weyl_eq_one_of_fixed_regular_functional P f hf w
  intro y
  have he := RootPairing.InvariantForm.apply_weylGroup_smul P (B := B) w x y
  rw [hfixed] at he
  exact he

/-- Evaluation at a coroot-regular weight identifies the Weyl group with
that weight's orbit; in particular each orbit point has a unique representative. -/
def regularWeightOrbitEquiv (x : M) (hx : ∀ i, P.coroot' i x ≠ 0) :
    P.weylGroup ≃ MulAction.orbit P.weylGroup x :=
  Equiv.ofBijective (fun w => ⟨w • x, ⟨w, rfl⟩⟩) (by
    constructor
    · intro w v h
      have he : w • x = v • x := congrArg Subtype.val h
      have hfixed : (v⁻¹ * w) • x = x := by
        rw [mul_smul, he, inv_smul_smul]
      have hone := weyl_eq_one_of_fixed_regular_weight P x hx (v⁻¹ * w) hfixed
      exact (inv_mul_eq_one.mp hone).symm
    · rintro ⟨y, w, rfl⟩
      exact ⟨w, rfl⟩)

theorem regularWeightOrbitEquiv_apply (x : M) (hx : ∀ i, P.coroot' i x ≠ 0)
    (w : P.weylGroup) :
    (regularWeightOrbitEquiv P x hx w : M) = w • x :=
  rfl

end FiniteIndex

end Langlands.LinearAlgebra
