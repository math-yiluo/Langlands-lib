import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Torus.Geometry

/-! # Tori are smooth and connected, and maximal tori exist by coordinate-kernel height -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Smoothness, connectedness and solvability of tori -/

section Geometry

variable {k : Type u} [Field k] {T : GroupScheme (Spec (CommRingCat.of k))}

/-- A commutative group scheme over a field is solvable: its geometric points form a
commutative group. -/
theorem CommGroupScheme.isSolvableGroupScheme (T : CommGroupScheme (Spec (CommRingCat.of k))) :
    IsSolvableGroupScheme T.toGrp :=
  isSolvableGroupScheme_of_isCommMonObj T.toGrp

end Geometry

/-! ### The trivial torus -/

section Trivial

variable (S : Scheme.{u})

/-- The trivial group scheme is the split torus on the empty index type: both have exactly one
point over every test scheme. -/
def trivialSplitTorusIso : Grp.trivial (Over S) ≅ splitTorus S PEmpty.{u + 1} :=
  letI : ∀ U : Over S, Unique (U ⟶ (Grp.trivial (Over S)).X) := fun U =>
    ⟨⟨toUnit U⟩, fun x => toUnit_unique x _⟩
  isoOfPointModels (fun U : Over S => PEmpty.{u + 1} → (Γ(U.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict PEmpty.{u + 1} a) (fun _ => MulEquiv.ofUnique)
    (splitTorus.pointsEquiv PEmpty.{u + 1}) (fun _ _ => Subsingleton.elim _ _)
    (fun a y => splitTorus.pointsEquiv_naturality PEmpty.{u + 1} a y)

/-- The trivial group scheme is a split torus. -/
theorem isSplitTorus_trivial : IsSplitTorus (Grp.trivial (Over S)) :=
  ⟨PEmpty, inferInstance, ⟨trivialSplitTorusIso S⟩⟩

/-- The trivial group scheme, as a commutative group scheme. -/
abbrev trivialCommGroupScheme : CommGroupScheme S where
  toGrp := Grp.trivial (Over S)
  comm := (isCommMonObj_iff_isMulCommutative _).2 fun _ => ⟨⟨fun _ _ => toUnit_unique _ _⟩⟩

end Trivial

/-! ### Existence of maximal tori -/

section Existence

open BorelExistence

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The unit section is a closed torus of every group scheme over a field. -/
theorem exists_isTorus_isClosedSubgroup :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsTorus T.toGrp ∧ IsClosedSubgroup i := by
  refine ⟨trivialCommGroupScheme _, 0, (isSplitTorus_trivial _).isTorus, ?_⟩
  exact isClosedImmersion_of_comp_eq_id G.X.hom _ (Over.w _)

/-- A closed torus whose coordinate kernel has minimal height among all closed tori exists, and
it is a maximal torus. -/
theorem exists_isMaximalTorus_minimal_height :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsMaximalTorus i ∧
      ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
        IsTorus T'.toGrp → IsClosedSubgroup i' →
          (coordinateKernel i).height ≤ (coordinateKernel i').height := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsTorus T.toGrp ∧ IsClosedSubgroup i ∧ (coordinateKernel i).height.toNat = n
  have hP : ∃ n, P n := by
    obtain ⟨T, i, hT, hi⟩ := exists_isTorus_isClosedSubgroup G
    exact ⟨_, T, i, hT, hi, rfl⟩
  obtain ⟨T, i, hT, hi, hheight⟩ := Nat.find_spec hP
  have hmin : ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
      IsTorus T'.toGrp → IsClosedSubgroup i' →
        (coordinateKernel i).height ≤ (coordinateKernel i').height := by
    intro T' i' hT' hi'
    have := hT.smooth
    have := hT.connectedSpace
    have := hT'.smooth
    have := hT'.connectedSpace
    have h : (coordinateKernel i).height.toNat ≤ (coordinateKernel i').height.toNat := by
      rw [hheight]
      exact Nat.find_min' hP ⟨T', i', hT', hi', rfl⟩
    rw [← ENat.natCast_toNat (coordinateKernel_height_ne_top i),
      ← ENat.natCast_toNat (coordinateKernel_height_ne_top i')]
    exact_mod_cast h
  refine ⟨T, i, ⟨hT, hi, ?_⟩, hmin⟩
  intro T' i' f hT' hi' hf
  have := hT'.smooth
  have := hT'.connectedSpace
  exact isIso_of_coordinateKernel_height_le i i' f hi hi' hf (hmin T' i' hT' hi')

/-- Every affine group scheme locally of finite type over a field has a maximal torus defined
over that field. -/
theorem exists_isMaximalTorus :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsMaximalTorus i := by
  obtain ⟨T, i, hi, -⟩ := exists_isMaximalTorus_minimal_height G
  exact ⟨T, i, hi⟩

end Existence

end Langlands.GroupScheme
