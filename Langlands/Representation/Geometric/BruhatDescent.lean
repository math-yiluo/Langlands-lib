import Langlands.Representation.Geometric.WeylDefinitions

/-! The actual map from Weyl double cosets to parabolic double cosets. -/

namespace Langlands.Geometric

open GeneralLinear

universe u

variable {n : ℕ} (R : Type u) [CommRing R]

/-- A block-preserving permutation gives an actual element of the upper block parabolic. -/
theorem permutation_mem_parabolic_of_mem_blockWeyl (B : BlockShape n)
    {w : Equiv.Perm (Fin n)} (hw : w ∈ blockWeyl B) :
    permutation n R w ∈ B.parabolic R := by
  apply (B.mem_parabolic_iff R _).mpr
  intro i j a b hji
  rw [permutation_entry]
  split_ifs with he
  · have h := hw (B.index j b)
    rw [he, blockIndex_index, blockIndex_index] at h
    exact False.elim ((ne_of_lt hji) h.symm)
  · rfl

/-- Inverting permutation matrices respects the two double-coset relations.
The inverse exchanges the source and target block subgroups. -/
theorem inverse_permutation_doubleCoset_eq_of_weyl_eq (B C : BlockShape n)
    {v w : Equiv.Perm (Fin n)}
    (h : DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) w) :
    DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R v)⁻¹ =
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹ := by
  obtain ⟨c, hc, b, hb, hw⟩ := DoubleCoset.eq.mp h
  apply DoubleCoset.eq.mpr
  refine ⟨(permutation n R b)⁻¹,
    (B.parabolic R).inv_mem (permutation_mem_parabolic_of_mem_blockWeyl R B hb),
    (permutation n R c)⁻¹,
    (C.parabolic R).inv_mem (permutation_mem_parabolic_of_mem_blockWeyl R C hc), ?_⟩
  simp only [hw, map_mul, mul_inv_rev, mul_assoc]

/-- The actual inverse permutation matrix map on Weyl double cosets.
Its construction needs no field or Bruhat decomposition hypothesis. -/
def weylToParabolicDoubleCoset (B C : BlockShape n) :
    DoubleCoset.Quotient (blockWeyl C : Set (Equiv.Perm (Fin n))) (blockWeyl B) →
      DoubleCoset.Quotient (B.parabolic R : Set (GeneralLinear n R)) (C.parabolic R) :=
  Quotient.lift
    (fun w => DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹)
    (fun _ _ h => inverse_permutation_doubleCoset_eq_of_weyl_eq R B C
      (Quotient.sound h))

@[simp]
theorem weylToParabolicDoubleCoset_mk (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    weylToParabolicDoubleCoset R B C (DoubleCoset.mk (blockWeyl C) (blockWeyl B) w) =
      DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w)⁻¹ := rfl

/-- The published map on minimal representatives factors through the actual Weyl quotient. -/
theorem parabolicDoubleCoset_factorization (B C : BlockShape n) :
    parabolicDoubleCoset R B C = weylToParabolicDoubleCoset R B C ∘ weylDoubleCoset B C := rfl

end Langlands.Geometric
