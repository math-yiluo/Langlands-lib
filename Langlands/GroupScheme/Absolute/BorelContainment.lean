import Langlands.GroupScheme.Absolute.BorelContaining

/-! # A Borel overgroup of a given admissible subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelExistence

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Among admissible overgroups of a given admissible subgroup, one has minimal
coordinate-kernel height. -/
theorem exists_minimal_height_admissible_over
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (j : H ⟶ G) (hj : IsAdmissible j) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsAdmissible i ∧ (∃ f : H ⟶ B, f ≫ i = j) ∧
      ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i' : B' ⟶ G),
        IsAdmissible i' → (∃ f' : H ⟶ B', f' ≫ i' = j) →
          (coordinateKernel i).height ≤ (coordinateKernel i').height := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsAdmissible i ∧ (∃ f : H ⟶ B, f ≫ i = j) ∧
        (coordinateKernel i).height.toNat = n
  have hP : ∃ n, P n := by
    exact ⟨_, H, j, hj, ⟨𝟙 H, by simp⟩, rfl⟩
  obtain ⟨B, i, hi, hf, hheight⟩ := Nat.find_spec hP
  refine ⟨B, i, hi, hf, ?_⟩
  intro B' i' hi' hf'
  have := hi.2.1
  have := hi.2.2.1
  have := hi'.2.1
  have := hi'.2.2.1
  have hmin : (coordinateKernel i).height.toNat ≤ (coordinateKernel i').height.toNat := by
    rw [hheight]
    exact Nat.find_min' hP ⟨B', i', hi', hf', rfl⟩
  have hfinite := coordinateKernel_height_ne_top i
  have hfinite' := coordinateKernel_height_ne_top i'
  rw [← ENat.natCast_toNat hfinite, ← ENat.natCast_toNat hfinite']
  exact_mod_cast hmin

/-- An actual Borel embedding together with a factor of the given embedding. -/
structure BorelOverData (j : H ⟶ G) where
  subgroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup ⟶ G
  factor : H ⟶ subgroup
  isBorelSubgroup : IsBorelSubgroup inclusion
  factorization : factor ≫ inclusion = j

/-- Choose a Borel containing the given admissible subgroup. -/
def borelOverData [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (j : H ⟶ G) (hj : IsAdmissible j) : BorelOverData j :=
  Classical.choice (by
    obtain ⟨B, i, f, hi, hf⟩ := exists_isBorelSubgroup_containing j hj
    exact ⟨⟨B, i, f, hi, hf⟩⟩)

end BorelExistence

end Langlands.GroupScheme
