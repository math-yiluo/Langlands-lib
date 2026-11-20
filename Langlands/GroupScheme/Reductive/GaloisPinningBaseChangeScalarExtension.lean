import Langlands.GroupScheme.Reductive.GaloisPinningBaseChange

/-! # Canonical scalar-extension data for a Galois pinning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (E : Type u) [Field E] [Algebra k E] [Algebra E K] [IsScalarTower k E K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical base-change pinning gives scalar-extension data with the
same actual torus and weight transport used in the Tits transfer formulas. -/
def baseChangeScalarExtension : ScalarExtension (E := E) d where
  pinning := d.baseChange E
  rootEquiv := d.baseChangeRootDatumEquiv E
  base_eq := d.mem_baseChange_base_support_iff E
  star_eq := d.baseChangeRootDatumEquiv_comp_starAction E
  groupIso := (groupTowerIso k E K G).symm
  groupIso_eq := rfl
  torusIso := (torusTowerIso k E K d.torus).symm
  inclusion_comp := by
    change (GroupScheme.baseChange (algebraBaseMap E K)).map
        ((GroupScheme.baseChange (algebraBaseMap k E)).map d.inclusion) ≫
        (groupTowerIso k E K G).inv =
      CommGroupScheme.groupHom (torusTowerIso k E K d.torus).inv ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map d.inclusion
    rw [baseChange_map_eq_groupTowerIso, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
    rfl
  weight_eq := fun χ => d.baseChangeRootDatumEquiv_weightMap E χ

end Langlands.GroupScheme.GaloisPinningData
