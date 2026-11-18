import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.Representation.Whittaker.GelfandGraevJacquetOrbits

/-! Field-general double-coset representatives for finite Harish–Chandra induction. -/

noncomputable section

namespace Langlands.FiniteGeneralLinear

open GeneralLinear Geometric

variable {k : Type*} [Field k] {n : ℕ}

/-- Over any field, inverse minimal permutation matrices represent the double cosets of two
standard parabolics. -/
theorem parabolicDoubleCoset_bijective (B C : BlockShape n) :
    Function.Bijective (Geometric.parabolicDoubleCoset k B C) := by
  apply parabolicDoubleCoset_bijective_of_matrix_conditions k B C
  · exact weylDoubleCoset_bijective B C
  · intro g
    obtain ⟨a, b, w, ha, hb, hg⟩ := fieldUpperBruhatFactorizationTheorem k n g
    exact ⟨w⁻¹, inverse_permutation_doubleCoset_of_upper_factorization B C g a b w ha hb hg⟩
  · intro v w h
    exact weyl_doubleCoset_eq_of_inverse_permutation_eq B C h

private theorem singletonLevi_conj_mem_parabolic (B : BlockShape n)
    (m : (BlockShape.singletons n).Levi k) (w : Equiv.Perm (Fin n)) :
    permutation n k w * (BlockShape.singletons n).leviEmbedding k m *
        (permutation n k w)⁻¹ ∈ B.parabolic k := by
  apply B.mem_parabolic_of_isUpperTriangular
  intro i j hji
  rw [permutation_conjugate_entry]
  have hij : w⁻¹ i ≠ w⁻¹ j := fun h => (ne_of_gt hji) (w.symm.injective h)
  have he :=
    (BlockShape.singletons n).leviEmbedding_apply_ne k m (0 : Fin 1) (0 : Fin 1) hij
  rw [BlockShape.singletons_index (w⁻¹ i) 0, BlockShape.singletons_index (w⁻¹ j) 0] at he
  exact he

private theorem singletonParabolic_factor
    (b : (BlockShape.singletons n).parabolic k) :
    ∃ (m : (BlockShape.singletons n).Levi k) (u : upperUnipotent n k),
      b.val = (BlockShape.singletons n).leviEmbedding k m * u.val := by
  let C := BlockShape.singletons n
  let m := C.leviProjection k b
  let d := C.leviInParabolic k m
  let v : C.unipotentRadical k := ⟨d⁻¹ * b, by
    change C.leviProjection k (d⁻¹ * b) = 1
    simp [d, m]⟩
  refine ⟨m, (BlockShape.upperUnipotentEquivRadical k).symm v, ?_⟩
  change b.val = d.val * (d.val⁻¹ * b.val)
  simp

private theorem parabolic_upperUnipotent_bijective (B : BlockShape n) :
    Function.Bijective
      (fun w : MinimalRepresentatives B (BlockShape.singletons n) =>
        DoubleCoset.mk (B.parabolic k) (upperUnipotent n k) (permutation n k w.val)⁻¹) := by
  let C := BlockShape.singletons n
  have h := parabolicDoubleCoset_bijective (k := k) B C
  constructor
  · intro v w hvw
    apply h.1
    obtain ⟨a, ha, b, hb, heq⟩ := DoubleCoset.eq.mp hvw
    apply DoubleCoset.eq.mpr
    exact ⟨a, ha, b, (BlockShape.singletons_mem_parabolic_iff k b).mpr hb.1, heq⟩
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, hw⟩ := h.2 (DoubleCoset.mk (B.parabolic k) (C.parabolic k) g)
    obtain ⟨a, ha, b, hb, heq⟩ := DoubleCoset.eq.mp hw
    obtain ⟨m, u, hfactor⟩ := singletonParabolic_factor (⟨b, hb⟩ : C.parabolic k)
    change b = C.leviEmbedding k m * u.val at hfactor
    refine ⟨w, DoubleCoset.eq.mpr ?_⟩
    refine ⟨a * ((permutation n k w.val)⁻¹ * C.leviEmbedding k m * permutation n k w.val),
      (B.parabolic k).mul_mem ha ?_, u.val, u.property, ?_⟩
    · simpa only [map_inv, inv_inv] using singletonLevi_conj_mem_parabolic B m w.val⁻¹
    · rw [heq, hfactor]
      simp only [mul_assoc, mul_inv_cancel_left]

/-- The permutation representative for the upper-unipotent left coset and parabolic right coset. -/
def unipotentParabolicRepresentative (B : BlockShape n)
    (w : MinimalRepresentatives B (BlockShape.singletons n)) : GeneralLinear n k :=
  permutation n k w.val

/-- The minimal permutations parametrize the upper-unipotent and parabolic double cosets. -/
theorem unipotentParabolicDoubleCoset_bijective (B : BlockShape n) :
    Function.Bijective (fun w => DoubleCoset.mk (upperUnipotent n k) (B.parabolic k)
      (unipotentParabolicRepresentative (k := k) B w)) := by
  have h := parabolic_upperUnipotent_bijective (k := k) B
  constructor
  · intro v w hvw
    apply h.1
    exact (Whittaker.doubleCoset_mk_inv_eq_iff _ _ _ _).mpr hvw
  · intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨w, hw⟩ := h.2 (DoubleCoset.mk (B.parabolic k) (upperUnipotent n k) g⁻¹)
    exact ⟨w, (Whittaker.doubleCoset_mk_inv_eq_iff (upperUnipotent n k)
      (B.parabolic k) (permutation n k w.val) g).mp hw⟩

end Langlands.FiniteGeneralLinear
