import Langlands.GroupScheme.SchemeActionAffineOrbitClosure
import Langlands.GroupScheme.SchemeActionReducedClosed
import Langlands.GroupScheme.SolvableProperFixedPointStatement
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable

/-! # Conditional fixedness for proper actions with invariant affine neighborhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Solvability of every test-scheme point group implies geometric solvability
for an affine locally finite type unipotent group. -/
theorem isSolvableGroupScheme_of_isUnipotent {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G) :
    IsSolvableGroupScheme G := by
  let E := baseChangePointsEquiv (toAlgebraicClosure k) G (Over.mk (𝟙 _))
  have : Group.IsSolvable
      ((Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 _)) ⟶ G.X) :=
    isSolvable_points_of_isUnipotent hG _
  exact Group.isSolvable_of_isSolvable_injective (f := E.toMonoidHom) E.injective

namespace SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

/-- Every rational orbit closure contains an all-test fixed rational section. -/
def HasFixedPointInOrbitClosures : Prop :=
  ∀ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X,
    ∃ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y ∧
      y.left (IsLocalRing.closedPoint k) ∈ closure (a.orbit x)

/-- The proper solvable fixed-point theorem applies to the reduced orbit closure. -/
theorem hasFixedPointInOrbitClosures_of_solvableProperFixedPoint
    (hFP : SolvableProperFixedPointStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsSolvableGroupScheme G) [IsProper X.hom] :
    a.HasFixedPointInOrbitClosures := by
  intro x
  obtain ⟨O, j, b, _, hj, hjrange, hb⟩ := a.exists_reduced_orbitClosure x
  have : IsClosedImmersion j.left := hj
  have : IsProper O.hom := by
    rw [← Over.w j]
    infer_instance
  have : Nonempty O.left := by
    let w := (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X).left
      (IsLocalRing.closedPoint k)
    have hw : (a.orbitMap x).left w ∈ closure (a.orbit x) :=
      subset_closure ⟨w, rfl⟩
    rw [← hjrange] at hw
    obtain ⟨z, _⟩ := hw
    exact ⟨z⟩
  obtain ⟨y, hy⟩ := hFP k G inferInstance hG O inferInstance inferInstance b
  refine ⟨y ≫ j, ?_, ?_⟩
  · intro T t g
    have h := (hb T g (t ≫ y)).symm.trans
      (congrArg (fun f => f ≫ j) (hy T t g))
    simpa only [Category.assoc] using h
  · change j.left (y.left (IsLocalRing.closedPoint k)) ∈ closure (a.orbit x)
    rw [← hjrange]
    exact ⟨_, rfl⟩

/-- KR and the proper solvable fixed-point theorem imply all-test fixedness
for a smooth connected affine unipotent action with invariant affine neighborhoods. -/
theorem isFixed_of_invariantAffineNeighborhoods_of_geometric_inputs
    (hKR : UnipotentAffineOrbitClosedStatement.{u})
    (hFP : SolvableProperFixedPointStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsUnipotent G) [IsProper X.hom]
    (hcover : a.HasInvariantAffineNeighborhoods)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : a.IsFixed x := by
  have hclosure := a.hasFixedPointInOrbitClosures_of_solvableProperFixedPoint hFP
    (isSolvableGroupScheme_of_isUnipotent hG)
  exact a.isFixed_of_invariantAffineCover_of_closure_fixedPoint hKR hG hcover hclosure x

end SchemeAction

end Langlands.GroupScheme
