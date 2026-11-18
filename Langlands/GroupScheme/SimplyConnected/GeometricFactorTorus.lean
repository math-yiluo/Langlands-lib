import Langlands.GroupScheme.SimplyConnected.NormalFactorTorus
import Langlands.GroupScheme.SimplyConnected.FactorProjectionUnique
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing

/-! # Geometric factor tori from original-field normal-subgroup projections -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  (D : SimplyConnectedAlmostSimpleProduct C)

/-- Transport an actual product presentation along an actual ambient isomorphism. -/
def ofIso (e : G ≅ C) : SimplyConnectedAlmostSimpleProduct G where
  Index := D.Index
  factor := D.factor
  isSimplyConnected := D.isSimplyConnected
  isAlmostSimple := D.isAlmostSimple
  iso := e ≪≫ D.iso

@[simp] theorem ofIso_inclusion (e : G ≅ C) (i : D.Index) :
    (D.ofIso e).inclusion i = D.inclusion i ≫ e.inv := by
  simp only [ofIso, inclusion, Iso.trans_inv, Category.assoc]

@[simp] theorem ofIso_projection (e : G ≅ C) (i : D.Index) :
    (D.ofIso e).projection i = e.hom ≫ D.projection i := by
  simp only [ofIso, projection, Iso.trans_hom, Category.assoc]

end SimplyConnectedAlmostSimpleProduct
namespace NormalFactorTorusProjection

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : H ⟶ G} {t : T.toGrp ⟶ G} (F : NormalFactorTorusProjection j t)
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
  (i : D.Index)
  (r : (GroupScheme.baseChange (algebraBaseMap k L)).obj H ≅ D.factor i)
  (hr : (GroupScheme.baseChange (algebraBaseMap k L)).map j = r.hom ≫ D.inclusion i)

include hr

/-- The base-changed original-field group retraction is the canonical
projection of the recovered actual geometric factor. -/
theorem retraction_baseChange :
    (GroupScheme.baseChange (algebraBaseMap k L)).map F.retraction ≫ r.hom = D.projection i := by
  apply D.retraction_eq_projection i
  let B := GroupScheme.baseChange (algebraBaseMap k L)
  have hi : r.inv ≫ B.map j = D.inclusion i := by rw [hr, Iso.inv_hom_id_assoc]
  calc
    D.inclusion i ≫ B.map F.retraction ≫ r.hom =
        (r.inv ≫ B.map j) ≫ B.map F.retraction ≫ r.hom :=
      congrArg (fun f => f ≫ B.map F.retraction ≫ r.hom) hi.symm
    _ = 𝟙 (D.factor i) := by
      rw [Category.assoc, ← Category.assoc (B.map j), ← B.map_comp,
        F.inclusion_retraction, B.map_id, Category.id_comp, Iso.inv_hom_id]

/-- Use the literal scalar extension of the original-field torus and torus
projection as actual compatible data for the recovered geometric factor. -/
def geometricFactorTorus (hH : IsConnectedReductive H)
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) :
    D.FactorMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map t) i := by
  let B := GroupScheme.baseChange (algebraBaseMap k L)
  let BC := CommGroupScheme.baseChange (algebraBaseMap k L)
  have hq : B.map F.retraction ≫ r.hom = D.projection i :=
    F.retraction_baseChange D i r hr
  have hjmax : IsMaximalTorus (T := BC.obj F.torus) (B.map F.subgroupHom) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq L F.isMaximalTorus.1 F.isMaximalTorus.2.1
      (maximalTorusCentralizer k H hH F.torus F.subgroupHom F.isMaximalTorus)
  refine {
    torus := BC.obj F.torus
    subgroupHom := B.map F.subgroupHom ≫ r.hom
    torusHom := BC.map F.torusHom
    isMaximalTorus := hjmax.comp_iso r
    isClosedSubgroup := F.isClosedSubgroup.baseChange (algebraBaseMap k L)
    comp_eq := ?_
    split := F.isSplitTorus_baseChange L hsplit
    projection := B.map F.projection
    projection_comp := ?_
    projection_section := ?_ }
  · change B.map (CommGroupScheme.groupHom F.torusHom) ≫ B.map t = _
    rw [← B.map_comp, F.comp_eq, B.map_comp, hr, Category.assoc]
  · rw [← Category.assoc, ← B.map_comp, F.projection_comp, B.map_comp, Category.assoc, hq]
  · change B.map (CommGroupScheme.groupHom F.torusHom) ≫ B.map F.projection = _
    rw [← B.map_comp, F.projection_section, B.map_id]
    rfl

/-- The geometric torus projection is literally the scalar extension of the
original-field projection, retaining its character Galois naturality. -/
theorem geometricFactorTorus_projection (hH : IsConnectedReductive H)
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp) :
    (F.geometricFactorTorus D i r hr hH hsplit).projection =
      (GroupScheme.baseChange (algebraBaseMap k L)).map F.projection := rfl

end NormalFactorTorusProjection
end Langlands.GroupScheme
