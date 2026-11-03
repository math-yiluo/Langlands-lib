import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates

/-! # Borel existence by finite prime-kernel height -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BorelExistence

variable {k : Type u} [Field k]

/-- An actual closed smooth connected solvable subgroup, before maximality is imposed. -/
def IsAdmissible {B G : GroupScheme (Spec (CommRingCat.of k))} (i : B ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth B.X.hom ∧ ConnectedSpace B.X.left ∧ IsSolvableGroupScheme B

/-- The terminal group scheme remains terminal after base change, so its geometric points
form a solvable group. -/
theorem trivial_isSolvable :
    IsSolvableGroupScheme (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  let hterm : IsTerminal
      (((GroupScheme.baseChange (toAlgebraicClosure k)).obj
        (Grp.trivial (Over (Spec (CommRingCat.of k))))).X) :=
    isTerminalTensorUnit.isTerminalObj (Over.pullback (toAlgebraicClosure k)) _
  unfold IsSolvableGroupScheme
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj
        (Grp.trivial (Over (Spec (CommRingCat.of k))))).X) := ⟨hterm.hom_ext⟩
  infer_instance

/-- The unit inclusion gives an admissible subgroup of every group scheme over a field. -/
theorem exists_admissible (G : GroupScheme (Spec (CommRingCat.of k))) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsAdmissible i := by
  refine ⟨Grp.trivial _, 0, ?_, ?_, ?_, trivial_isSolvable⟩
  · exact isClosedImmersion_of_comp_eq_id G.X.hom _ (Over.w _)
  · change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  · change ConnectedSpace (Spec (CommRingCat.of k))
    infer_instance

/-- A globally minimal finite prime-kernel height occurs among admissible subgroups. -/
theorem exists_minimal_height_admissible (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsAdmissible i ∧
      ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i' : B' ⟶ G), IsAdmissible i' →
        (coordinateKernel i).height ≤ (coordinateKernel i').height := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsAdmissible i ∧ (coordinateKernel i).height.toNat = n
  have hP : ∃ n, P n := by
    obtain ⟨B, i, hi⟩ := exists_admissible G
    exact ⟨_, B, i, hi, rfl⟩
  obtain ⟨B, i, hi, hheight⟩ := Nat.find_spec hP
  refine ⟨B, i, hi, ?_⟩
  intro B' i' hi'
  have := hi.2.1
  have := hi.2.2.1
  have := hi'.2.1
  have := hi'.2.2.1
  have hmin : (coordinateKernel i).height.toNat ≤ (coordinateKernel i').height.toNat := by
    rw [hheight]
    exact Nat.find_min' hP ⟨B', i', hi', rfl⟩
  have hfinite := coordinateKernel_height_ne_top i
  have hfinite' := coordinateKernel_height_ne_top i'
  rw [← ENat.natCast_toNat hfinite, ← ENat.natCast_toNat hfinite']
  exact_mod_cast hmin

/-- A subgroup with globally minimal coordinate-kernel height is a Borel subgroup. -/
theorem exists_isBorelSubgroup_minimal_height
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i ∧
      ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i' : B' ⟶ G), IsAdmissible i' →
        (coordinateKernel i).height ≤ (coordinateKernel i').height := by
  obtain ⟨B, i, hi, hmin⟩ := exists_minimal_height_admissible G
  obtain ⟨hclosed, hsmooth, hconnected, hsolvable⟩ := hi
  refine ⟨B, i, ⟨hclosed, hsmooth, hconnected, hsolvable, ?_⟩, hmin⟩
  intro B' i' f hclosed' hsmooth' hconnected' hsolvable' hfactor
  have := hsmooth'
  have := hconnected'
  exact isIso_of_coordinateKernel_height_le i i' f hclosed hclosed' hfactor
    (hmin B' i' ⟨hclosed', hsmooth', hconnected', hsolvable'⟩)

/-- Every affine group scheme locally of finite type over a field has a Borel subgroup
in the published sense of maximality among subgroups defined over that field. -/
theorem exists_isBorelSubgroup (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i := by
  obtain ⟨B, i, hB, _⟩ := exists_isBorelSubgroup_minimal_height G
  exact ⟨B, i, hB⟩

/-- An actual Borel subgroup together with its embedding into the ambient group. -/
structure BorelData (G : GroupScheme (Spec (CommRingCat.of k))) where
  subgroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup ⟶ G
  isBorelSubgroup : IsBorelSubgroup inclusion
  minimalHeight : ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i' : B' ⟶ G),
    IsAdmissible i' → (coordinateKernel inclusion).height ≤ (coordinateKernel i').height

/-- A choice of an actual Borel embedding supplied by prime-height minimization. -/
def borelData (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] : BorelData G := by
  classical
  let B := Classical.choose (exists_isBorelSubgroup_minimal_height G)
  have hB := Classical.choose_spec (exists_isBorelSubgroup_minimal_height G)
  exact ⟨B, Classical.choose hB, (Classical.choose_spec hB).1, (Classical.choose_spec hB).2⟩

end Langlands.GroupScheme.BorelExistence
