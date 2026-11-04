import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.SchemeActionFiniteTarget
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.Topology.KrullDimension

/-! # Dominant nonfixed orbits on schemes of dimension at most one -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

namespace Topology

/-- An irreducible subset containing two distinct points, one of them closed,
is dense in an irreducible space of dimension at most one. -/
theorem dense_of_isIrreducible_of_two_points_of_dimension_le_one
    {X : Type v} [TopologicalSpace X] [IrreducibleSpace X]
    {s : Set X} (hs : IsIrreducible s)
    (hdim : topologicalKrullDim X ≤ 1) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) (hxc : IsClosed ({x} : Set X))
    (hxy : x ≠ y) : Dense s := by
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure s, hs.closure, isClosed_closure⟩
  let P : TopologicalSpace.IrreducibleCloseds X :=
    ⟨{x}, isIrreducible_singleton, hxc⟩
  have hPZ : P ≤ Z := by
    intro z hz
    change z ∈ ({x} : Set X) at hz
    rcases hz with rfl
    exact subset_closure hx
  have hnotmin : ¬ IsMin Z := by
    intro hm
    have he : Z ≤ P := hm hPZ
    have hyx : y = x := he (subset_closure hy)
    exact hxy hyx.symm
  have hm : IsMax Z :=
    ((Order.krullDim_le_one_iff.mp hdim) Z).resolve_left hnotmin
  let W : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hWZ : W ≤ Z := hm (show Z ≤ W from Set.subset_univ _)
  exact dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset hWZ)

end Topology

namespace GroupScheme.SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))}
    (a : SchemeAction H X)

/-- A chosen rational translate distinct from a supplied nonfixed section. -/
def nonfixedRationalTranslate
    [Smooth H.X.hom] [LocallyOfFiniteType X.hom] [IsSeparated X.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (hx : ¬ a.IsFixed x) :
    {h : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X // a.act h x ≠ x} := by
  classical
  have hex : ∃ h : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X,
      a.act h x ≠ x := by
    by_contra! h
    exact hx ((a.isFixed_iff_rationalPoints x).2 h)
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- A nonfixed orbit of a smooth irreducible group is dominant on an
irreducible separated scheme of dimension at most one. -/
theorem isDominant_orbitMap_of_not_isFixed_of_dimension_le_one
    [Smooth H.X.hom] [IrreducibleSpace H.X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [IrreducibleSpace X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (hx : ¬ a.IsFixed x) :
    IsDominant (a.orbitMap x).left := by
  classical
  obtain ⟨h, hh⟩ := a.nonfixedRationalTranslate x hx
  have hxr : x.left (IsLocalRing.closedPoint k) ∈
      Set.range (a.orbitMap x).left :=
    (a.mem_rationalOrbit_iff x x).mp ⟨1, a.act_one x⟩
  have hyr : (a.act h x).left (IsLocalRing.closedPoint k) ∈
      Set.range (a.orbitMap x).left :=
    (a.mem_rationalOrbit_iff x (a.act h x)).mp ⟨h, rfl⟩
  have hxc : IsClosed ({x.left (IsLocalRing.closedPoint k)} : Set X.left) :=
    (rationalPointEquivClosedPoint X x).property
  have hxy : x.left (IsLocalRing.closedPoint k) ≠
      (a.act h x).left (IsLocalRing.closedPoint k) := by
    intro he
    apply hh
    apply (rationalPointEquivClosedPoint X).injective
    exact Subtype.ext he.symm
  have hirr : IsIrreducible (Set.range (a.orbitMap x).left) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ H.X.left).image (a.orbitMap x).left
        (a.orbitMap x).left.continuous.continuousOn
  exact ⟨Topology.dense_of_isIrreducible_of_two_points_of_dimension_le_one
    hirr hdim hxr hyr hxc hxy⟩

/-- Nonfixed orbits of smooth connected affine groups on an irreducible
separated curve are dominant and quasi-compact. -/
theorem dominant_quasiCompact_orbitMap_of_not_isFixed_of_dimension_le_one
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [IrreducibleSpace X.left]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (hx : ¬ a.IsFixed x) :
    IsDominant (a.orbitMap x).left ∧ QuasiCompact (a.orbitMap x).left := by
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IrreducibleSpace H.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.X.hom
  have : QuasiCompact ((a.orbitMap x).left ≫ X.hom) := by
    rw [Over.w]
    infer_instance
  exact ⟨a.isDominant_orbitMap_of_not_isFixed_of_dimension_le_one hdim x hx,
    QuasiCompact.of_comp _ X.hom⟩

end GroupScheme.SchemeAction

end Langlands
