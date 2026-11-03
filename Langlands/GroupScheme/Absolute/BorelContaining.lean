import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Extending a prescribed solvable subgroup to a Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelExistence

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- A prescribed admissible subgroup lies in a Borel. The factorization is
retained as an actual homomorphism of group schemes. -/
theorem exists_isBorelSubgroup_containing (a : H ⟶ G) (ha : IsAdmissible a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (f : H ⟶ B),
      IsBorelSubgroup i ∧ f ≫ i = a := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (f : H ⟶ B),
      IsAdmissible i ∧ f ≫ i = a ∧ (coordinateKernel i).height.toNat = n
  have hQ : ∃ n, Q n := ⟨_, H, a, 𝟙 H, ha, Category.id_comp a, rfl⟩
  obtain ⟨B, i, f, hi, hf, hheight⟩ := Nat.find_spec hQ
  obtain ⟨hclosed, hsmooth, hconnected, hsolvable⟩ := hi
  refine ⟨B, i, f, ⟨hclosed, hsmooth, hconnected, hsolvable, ?_⟩, hf⟩
  intro B' i' g hclosed' hsmooth' hconnected' hsolvable' hg
  have := hsmooth
  have := hconnected
  have := hsmooth'
  have := hconnected'
  apply isIso_of_coordinateKernel_height_le i i' g hclosed hclosed' hg
  have hmin : (coordinateKernel i).height.toNat ≤ (coordinateKernel i').height.toNat := by
    rw [hheight]
    apply Nat.find_min' hQ
    exact ⟨B', i', f ≫ g, ⟨hclosed', hsmooth', hconnected', hsolvable'⟩,
      by rw [Category.assoc, hg, hf], rfl⟩
  rw [← ENat.natCast_toNat (coordinateKernel_height_ne_top i),
    ← ENat.natCast_toNat (coordinateKernel_height_ne_top i')]
  exact_mod_cast hmin

/-- An actual Borel containing a prescribed smooth connected solvable subgroup. -/
structure BorelContainingData (a : H ⟶ G) where
  subgroup : GroupScheme (Spec (CommRingCat.of k))
  inclusion : subgroup ⟶ G
  factor : H ⟶ subgroup
  isBorelSubgroup : IsBorelSubgroup inclusion
  factor_comp : factor ≫ inclusion = a

/-- Choose a Borel without losing the specified subgroup or its inclusion. -/
def borelContainingData (a : H ⟶ G) (ha : IsAdmissible a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] : BorelContainingData a := by
  let B := Classical.choose (exists_isBorelSubgroup_containing a ha)
  have hB := Classical.choose_spec (exists_isBorelSubgroup_containing a ha)
  let i := Classical.choose hB
  have hi := Classical.choose_spec hB
  let f := Classical.choose hi
  have hf := Classical.choose_spec hi
  exact ⟨B, i, f, hf.1, hf.2⟩

end BorelExistence

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- A commutative group scheme is solvable in the published geometric-point sense. -/
theorem isSolvableGroupScheme_of_commutative :
    IsSolvableGroupScheme T.toGrp := by
  change Group.IsSolvable
    (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
      ((CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T).X)
  infer_instance

/-- A prescribed closed split torus lies in a Borel defined over the original field. -/
theorem exists_isBorelSubgroup_containing_splitTorus (a : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (ha : IsClosedSubgroup a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (f : T.toGrp ⟶ B),
      IsBorelSubgroup i ∧ f ≫ i = a :=
  BorelExistence.exists_isBorelSubgroup_containing a
    ⟨ha, hT.smooth, hT.connectedSpace, isSolvableGroupScheme_of_commutative⟩

/-- A split torus in a closed subgroup lies in a Borel of that subgroup.
This does not assert that this Borel is a Borel of the ambient group. -/
theorem exists_isBorelSubgroup_containing_splitTorus_in_closedSubgroup
    (a : T.toGrp ⟶ G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (ha : IsClosedSubgroup a)
    (hi : IsClosedSubgroup i) (hf : f ≫ i = a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ P) (t : T.toGrp ⟶ B),
      IsBorelSubgroup b ∧ t ≫ b = f ∧ (t ≫ b) ≫ i = a := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hfclosed : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hi (by rwa [hf])
  obtain ⟨B, b, t, hb, ht⟩ :=
    exists_isBorelSubgroup_containing_splitTorus f hT hfclosed
  exact ⟨B, b, t, hb, ht, by rw [ht, hf]⟩

/-- The specified split maximal torus belongs to a Borel pair inside each
closed subgroup through which it factors. -/
theorem exists_isBorelPair_in_closedSubgroup
    (a : T.toGrp ⟶ G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (ha : IsMaximalTorus a)
    (hi : IsClosedSubgroup i) (hf : f ≫ i = a)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ P),
      IsBorelPair b f := by
  obtain ⟨B, b, t, hb, ht, _⟩ :=
    exists_isBorelSubgroup_containing_splitTorus_in_closedSubgroup
      a i f hT ha.2.1 hi hf
  refine ⟨B, b, hb, ?_, t, ht⟩
  exact IsMaximalTorus.of_comp hi (by rwa [hf])

end Langlands.GroupScheme
