import Langlands.GroupScheme.Torus.OrderedProjectorChartImage

/-! # Disjoint affine opens in the moduli of subtori of a general linear group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]
variable {M : Over (Spec R)} {K : GroupScheme M.left}
variable (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R))
  (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
  (hu : TorusSubgroupModuli.IsUniversal j)

include hj hK in
private theorem chartMap_range_subset (C D : SplitChart.{u})
    (e : WeightEquivalence C.weights D.weights) :
    Set.range (D.map j hu).left ⊆ Set.range (C.map j hu).left := by
  classical
  let : Fintype C.index := Fintype.ofFinite C.index
  let : Fintype D.index := Fintype.ofFinite D.index
  have h : relabelMap e.labels ≫ C.map j hu = D.map j hu :=
    relabelMap_comp_chartMap hj hK hu C.generates D.generates
      (Diagonalizable.isSplitTorus R (AddEquiv.refl (C.index → ℤ)))
      (Diagonalizable.isSplitTorus R (AddEquiv.refl (D.index → ℤ))) e
  rintro _ ⟨y, rfl⟩
  exact ⟨(relabelMap e.labels).left y, congrArg (fun a => a.left y) h⟩

/-- Any two chart images with a common point are equal. A point on the overlap selects a
matching of the weights, and relabelling by the matching and its inverse identifies the images. -/
theorem SplitChart.image_eq_of_mem (C D : SplitChart.{u}) {x : M.left}
    (hx : x ∈ C.image j hj hK hu) (hy : x ∈ D.image j hj hK hu) :
    C.image j hj hK hu = D.image j hj hK hu := by
  classical
  obtain ⟨y, hy'⟩ := hx
  obtain ⟨z, hz'⟩ := hy
  obtain ⟨t, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (C.map j hu).left) (g := (D.map j hu).left) y z (hy'.trans hz'.symm)
  let : Fintype C.index := Fintype.ofFinite C.index
  let : Fintype D.index := Fintype.ofFinite D.index
  let h := overlapIso hj hK hu C.generates D.generates
    (Diagonalizable.isSplitTorus R (AddEquiv.refl (C.index → ℤ)))
    (Diagonalizable.isSplitTorus R (AddEquiv.refl (D.index → ℤ))) C.injective D.injective
  let X : WeightEquivalence C.weights D.weights → Scheme.{u} := fun _ => (D.scheme n R).left
  let t' : ↥(∐ X : Scheme.{u}) := h.inv t
  obtain ⟨e, _, _⟩ := (sigmaOpenCover X).exists_eq t'
  let e' : WeightEquivalence D.weights C.weights :=
    ⟨e.lattice.symm, e.labels.symm, fun i => by
      apply e.lattice.injective
      rw [e.lattice.apply_symm_apply, e.weight_eq, e.labels.apply_symm_apply]⟩
  apply Opens.ext
  exact Set.Subset.antisymm (chartMap_range_subset j hj hK hu D C e')
    (chartMap_range_subset j hj hK hu C D e)

/-- Index the distinct chart images by their underlying opens. -/
def ChartImageIndex : Type u := {U : M.left.Opens // ∃ C : SplitChart.{u}, C.image j hj hK hu = U}

include j hj hK hu in
/-- The universal moduli of closed subtori of a general linear group is covered by a family of
pairwise disjoint affine opens. -/
theorem exists_disjoint_affineOpen_cover :
    ∃ (ι : Type u) (U : ι → M.left.Opens),
      (∀ k, IsAffineOpen (U k)) ∧ Pairwise (Function.onFun Disjoint U) ∧ iSup U = ⊤ := by
  refine ⟨ChartImageIndex j hj hK hu, Subtype.val, ?_, ?_, ?_⟩
  · rintro ⟨U, C, rfl⟩
    exact C.isAffineOpen_image j hj hK hu
  · rintro ⟨U, C, rfl⟩ ⟨W, D, rfl⟩ hne
    apply Opens.coe_disjoint.mp
    rw [Set.disjoint_left]
    intro x hx hy
    exact hne (Subtype.ext (C.image_eq_of_mem j hj hK hu D hx hy))
  · apply eq_top_iff.mpr
    intro x _
    obtain ⟨C, V, p, _, y, hy⟩ := exists_etale_factorization_through_splitChart j hj hK hu x
    refine Opens.mem_iSup.mpr ⟨⟨C.image j hj hK hu, C, rfl⟩, ?_⟩
    exact ⟨p.left y, hy⟩

end Langlands.GroupScheme.OrderedProjectorScheme
