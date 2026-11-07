import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Roots with equal finite orbit sums lie in one orbit -/

noncomputable section

namespace RootPairing

variable {J : Type*} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootDatum J M N) {Γ : Type*} [Group Γ] [Fintype Γ] (ρ : Γ →* P.Aut)

/-- The sum, over a finite group acting by root-datum automorphisms, of the roots in the
orbit of a root index. -/
def rootOrbitSum (i : J) : M :=
  ∑ g : Γ, P.root (ρ g • i)

theorem rootOrbitSum_eq_sum_smul (i : J) :
    P.rootOrbitSum ρ i = ∑ g : Γ, ρ g • P.root i := by
  unfold rootOrbitSum
  refine Finset.sum_congr rfl fun g _ => ?_
  exact RootPairing.Equiv.root_indexEquiv_eq_smul (i := i) (g := ρ g)

/-- The orbit sum is constant along the orbit. -/
theorem rootOrbitSum_smul (g : Γ) (i : J) :
    P.rootOrbitSum ρ (ρ g • i) = P.rootOrbitSum ρ i := by
  unfold rootOrbitSum
  simp_rw [← mul_smul, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl

/-- Orbit sums are additive along actual root differences. -/
theorem rootOrbitSum_eq_sub_of_root_eq_sub {m a b : J}
    (h : P.root m = P.root a - P.root b) :
    P.rootOrbitSum ρ m = P.rootOrbitSum ρ a - P.rootOrbitSum ρ b := by
  simp only [rootOrbitSum_eq_sum_smul, h, smul_sub, Finset.sum_sub_distrib]

/-- Root-datum automorphisms preserve pairings. -/
theorem pairing_smul_smul (w : P.Aut) (i j : J) :
    P.pairing (w • i) (w • j) = P.pairing i j :=
  w.toHom.pairing

/-- Pairing the orbit sum of `i` with the coroot of `j` sums the pairings of `i` with
the orbit of `j`. -/
theorem sum_pairing_smul_right (i j : J) :
    ∑ g : Γ, P.pairing i (ρ g • j) = P.toLinearMap (P.rootOrbitSum ρ i) (P.coroot j) := by
  unfold rootOrbitSum
  rw [map_sum, LinearMap.sum_apply]
  simp only [root_coroot_eq_pairing]
  refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
  rw [← P.pairing_smul_smul (ρ g⁻¹) i (ρ g • j), ← mul_smul, ← map_mul, inv_mul_cancel,
    map_one, one_smul]
  rfl

/-- The orbit sum of a root pairs with the coroot of the root itself as the sum of the
pairings of the orbit with that coroot, for every member of the orbit. -/
theorem toLinearMap_rootOrbitSum_coroot_smul (g : Γ) (j : J) :
    P.toLinearMap (P.rootOrbitSum ρ j) (P.coroot (ρ g • j)) =
      P.toLinearMap (P.rootOrbitSum ρ j) (P.coroot j) := by
  rw [← P.sum_pairing_smul_right, ← P.sum_pairing_smul_right]
  simp_rw [← mul_smul, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl

/-- **Orbit-sum transitivity.** Let a finite group act on a finite root datum by
automorphisms. If no root has orbit sum zero, then two roots with the same orbit sum lie in
the same orbit. -/
theorem exists_smul_eq_of_rootOrbitSum_eq [Finite J] {i j : J}
    (hsum : P.rootOrbitSum ρ i = P.rootOrbitSum ρ j)
    (hne : ∀ m, P.rootOrbitSum ρ m ≠ 0) :
    ∃ g : Γ, ρ g • j = i := by
  classical
  have _ : Fintype J := Fintype.ofFinite J
  by_contra! hcon
  -- No member of the orbit of `j` pairs positively with `i`.
  have hle : ∀ g : Γ, P.pairing i (ρ g • j) ≤ 0 := by
    intro g
    by_contra! hpos
    have hpos' : 0 < P.pairingIn ℤ i (ρ g • j) := by
      have h := P.algebraMap_pairingIn ℤ i (ρ g • j)
      simp only [Algebra.algebraMap_self_apply] at h
      rwa [h]
    obtain ⟨m, hm⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos' (hcon g).symm
    apply hne m
    rw [P.rootOrbitSum_eq_sub_of_root_eq_sub ρ hm, P.rootOrbitSum_smul, hsum, sub_self]
  -- The orbit sum of `j` pairs positively with the coroot of `j`.
  set x := P.rootOrbitSum ρ j with hx
  set c := P.toLinearMap x (P.coroot j) with hc
  have hxspan : x ∈ P.rootSpan ℤ :=
    Submodule.sum_mem _ fun g _ => Submodule.subset_span ⟨_, rfl⟩
  have hBx : 0 < P.RootForm x x := P.rootForm_pos_of_ne_zero hxspan (hne j)
  have hterm : ∀ g : Γ, 2 * P.RootForm (P.root (ρ g • j)) x =
      P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j)) * c := by
    intro g
    have h := congrArg (fun y => P.toLinearMap x y) (P.rootForm_self_smul_coroot (ρ g • j))
    simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul,
      toLinearMap_apply_apply_Polarization] at h
    rw [P.toLinearMap_rootOrbitSum_coroot_smul] at h
    push_cast at h
    linarith
  have hxx : 2 * P.RootForm x x =
      (∑ g : Γ, P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j))) * c := by
    have hx' : P.RootForm x x = ∑ g : Γ, P.RootForm (P.root (ρ g • j)) x := by
      change P.RootForm (∑ g : Γ, P.root (ρ g • j)) x = _
      rw [map_sum, LinearMap.sum_apply]
    rw [hx', Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _ => hterm g
  have hS : 0 ≤ ∑ g : Γ, P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j)) :=
    Finset.sum_nonneg fun g _ => P.zero_le_rootForm _
  have hcpos : 0 < c := by
    by_contra! hc'
    nlinarith
  -- But the same pairing is a sum of nonpositive pairings.
  have hsum2 : ∑ g : Γ, P.pairing i (ρ g • j) = c := by
    rw [P.sum_pairing_smul_right, hsum]
  have hnonpos : ∑ g : Γ, P.pairing i (ρ g • j) ≤ 0 :=
    Finset.sum_nonpos fun g _ => hle g
  linarith

end RootPairing
