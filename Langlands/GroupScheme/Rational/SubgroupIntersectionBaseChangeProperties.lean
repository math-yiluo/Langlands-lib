import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Geometric properties of base-changed subgroup intersections -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Intersection

variable {S S' : Scheme.{u}} {V C U : GroupScheme S}

/-- The actual intersection is affine if the first subgroup is affine and the
second subgroup inclusion is closed. -/
theorem isAffineHom_subgroupIntersection [IsAffineHom V.X.hom]
    (j : V ⟶ U) (c : C ⟶ U) (hc : IsClosedSubgroup c) :
    IsAffineHom (subgroupIntersection j c).X.hom := by
  let i := subgroupIntersectionFst j c
  let : IsClosedImmersion i.hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst j hc
  rw [← i.hom.hom.w]
  infer_instance

/-- Smoothness of the actual intersection persists after arbitrary base change,
through its canonical comparison with the intersection of the pullbacks. -/
theorem smooth_subgroupIntersection_baseChange
    (b : S' ⟶ S) (j : V ⟶ U) (c : C ⟶ U)
    [Smooth (subgroupIntersection j c).X.hom] :
    Smooth (subgroupIntersection ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map c)).X.hom := by
  apply smooth_of_over_iso
    ((Grp.forget _).mapIso (subgroupIntersectionBaseChangeIso b j c).symm)
  change Smooth (pullback.snd (subgroupIntersection j c).X.hom b)
  infer_instance

end Intersection

section Field

variable {k K : Type u} [Field k] [Field K]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}

/-- Connectedness of a smooth affine intersection persists over a field
extension on the actual intersection of the pulled-back subgroup maps. -/
theorem connectedSpace_subgroupIntersection_baseChange
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (j : V ⟶ U) (c : C ⟶ U)
    [Smooth (subgroupIntersection j c).X.hom]
    [IsAffineHom (subgroupIntersection j c).X.hom]
    [ConnectedSpace (subgroupIntersection j c).X.left] :
    ConnectedSpace (subgroupIntersection ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map c)).X.left := by
  have h := (subgroupIntersection j c).connectedSpace_baseChange_of_smooth_affine b
  exact (Scheme.homeoOfIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
    (subgroupIntersectionBaseChangeIso b j c)))).connectedSpace_iff.1 h

end Field

namespace Lie

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- An actual group-scheme isomorphism induces a linear equivalence on the
original dual-number identity kernels over the ground field. -/
def linearEquivOfIso (e : G ≅ H) :
    Additive (lieKernel G k) ≃ₗ[k] Additive (lieKernel H k) :=
  { targetMapLinear e.hom k with
    invFun := targetMapLinear e.inv k
    left_inv x := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x.toMul.val ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x.toMul.val
      simp only [Category.assoc,
        ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
    right_inv x := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x.toMul.val ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x.toMul.val
      simp only [Category.assoc,
        ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] }

/-- The actual Lie dimension is invariant under a group-scheme isomorphism. -/
theorem dimension_eq_of_iso (e : G ≅ H) : dimension G = dimension H :=
  (linearEquivOfIso e).finrank_eq

end Lie

end Langlands.GroupScheme
