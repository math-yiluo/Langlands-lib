import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.AlgebraicGeometry.Fiber

/-! # The underlying relative identity set and the all-test criterion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The union in `G` of the identity connected components of its residue fibres. -/
def underlyingSet : Set G.X.left :=
  {x | ∃ (s : S) (y : (residueFiber G s).X.left),
    y ∈ IdentityComponent.identitySet (residueFiber G s) ∧ G.X.hom.fiberι s y = x}

/-- The projection of a residue-fibre point lies over its indexing point. -/
theorem structure_fiberι (s : S) (y : (residueFiber G s).X.left) :
    G.X.hom (G.X.hom.fiberι s y) = s :=
  (G.X.hom.fiberHomeo s y).property

/-- On each residue fibre the relative union is exactly its identity component. -/
theorem fiberι_mem_underlyingSet_iff (s : S) (y : (residueFiber G s).X.left) :
    G.X.hom.fiberι s y ∈ underlyingSet G ↔
      y ∈ IdentityComponent.identitySet (residueFiber G s) := by
  constructor
  · rintro ⟨t, z, hz, h⟩
    have ht : t = s := by
      simpa only [structure_fiberι] using congrArg G.X.hom h
    subst t
    have hz' : z = y := (G.X.hom.fiberι s).isEmbedding.injective h
    simpa only [hz'] using hz
  · intro hy
    exact ⟨s, y, hy, rfl⟩

/-- Pulling back a test map commutes with the residue-fibre projections. -/
@[reassoc (attr := simp)]
theorem residueFiberPoint_fiberι {T : Over S} (x : T ⟶ G.X) (s : S) :
    (residueFiberPoint G x s).left ≫ G.X.hom.fiberι s = T.hom.fiberι s ≫ x.left := by
  simp [residueFiberPoint, Scheme.Hom.fiberι, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- The all-test residue-fibre criterion is the range condition in the relative union. -/
theorem inRelativeIdentityComponent_iff_range_subset {T : Over S} (x : T ⟶ G.X) :
    InRelativeIdentityComponent G x ↔ Set.range x.left ⊆ underlyingSet G := by
  constructor
  · intro hx z hz
    obtain ⟨t, rfl⟩ := hz
    let s : S := T.hom t
    let y : ((Over.pullback (S.fromSpecResidueField s)).obj T).left := T.hom.asFiber t
    refine ⟨s, (residueFiberPoint G x s).left y, hx s ⟨y, rfl⟩, ?_⟩
    have he := congrArg (fun f : T.hom.fiber s ⟶ G.X.left => f y)
      (residueFiberPoint_fiberι G x s)
    change G.X.hom.fiberι s ((residueFiberPoint G x s).left y) =
      x.left (T.hom.fiberι s y) at he
    exact he.trans (congrArg x.left (T.hom.fiberι_asFiber t))
  · intro hx s z hz
    obtain ⟨y, rfl⟩ := hz
    apply (fiberι_mem_underlyingSet_iff G s _).mp
    have he := congrArg (fun f : T.hom.fiber s ⟶ G.X.left => f y)
      (residueFiberPoint_fiberι G x s)
    change G.X.hom.fiberι s ((residueFiberPoint G x s).left y) =
      x.left (T.hom.fiberι s y) at he
    rw [he]
    exact hx ⟨_, rfl⟩

/-- A supplied open representative factors exactly the maps with image in the union. -/
theorem factors_iff_range_subset {H : GroupScheme S} {i : H ⟶ G}
    (hi : IsRelativeIdentityComponent G i) (T : Over S) (x : T ⟶ G.X) :
    (∃ y : T ⟶ H.X, y ≫ i.hom.hom = x) ↔ Set.range x.left ⊆ underlyingSet G :=
  (hi.factors_iff T x).trans (inRelativeIdentityComponent_iff_range_subset G x)

end Langlands.GroupScheme.RelativeIdentityComponent
