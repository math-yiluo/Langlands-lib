import Langlands.GroupScheme.SimplyConnected.TypeCDistinguishedVerticesStatement
import Langlands.GroupScheme.SimplyConnected.TypeCIndexFromBlockTorus

/-! # The distinguished vertices of a type C antihermitian group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option maxHeartbeats 800000 in
/-- The exact distinguished-vertices statement, over every field. -/
theorem typeCDistinguishedVertices : TypeCDistinguishedVerticesStatement.{u} := by
  intro K _ G _ _ d n e hn _hsc _has hcart degree m _ D _ _ _ _ hd hmn hD σ hσ H hH hu hform
  classical
  obtain ⟨c⟩ := hform
  obtain ⟨hrn, sQ, ΦQ, hsQ, hsqQ⟩ :=
    Quaternionic.DegreeSplitting.exists_wittTorus_splitting σ hD hσ H hH hu hmn
  let b := algebraBaseMap K (SeparableClosure K)
  let F := GroupScheme.baseChange b
  let s := sQ ≫ c.inv
  let Φ := F.mapIso c ≪≫ ΦQ
  have hs : IsMaximalSplitTorus s := hsQ.comp_iso c.symm
  have hsq : F.map s ≫ Φ.hom =
      CommGroupScheme.groupHom
        ((splitTorus.commBaseChangeIso b (ULift.{u} (Fin (σ.wittIndex H)))).hom ≫
          Quaternionic.DegreeSplitting.blockTorusHom (SeparableClosure K) degree
            (σ.wittIndex H) n) ≫
        SymplecticMatrix.diagonalTorus (Fin n) (CommRingCat.of (SeparableClosure K)) := by
    have hcancel :
        F.map s ≫ Φ.hom = F.map sQ ≫ ΦQ.hom := by
      simp only [s, Φ, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      rw [← F.map_comp_assoc c.inv c.hom, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
    rw [hcancel]
    change (splitTorus.baseChangeIso b (ULift.{u} (Fin (σ.wittIndex H)))).inv ≫
      F.map sQ ≫ ΦQ.hom = _ at hsqQ
    have h := congrArg
      (fun z => (splitTorus.baseChangeIso b (ULift.{u} (Fin (σ.wittIndex H)))).hom ≫ z) hsqQ
    change F.map sQ ≫ ΦQ.hom =
      (splitTorus.baseChangeIso b (ULift.{u} (Fin (σ.wittIndex H)))).hom ≫
        CommGroupScheme.groupHom
          (Quaternionic.DegreeSplitting.blockTorusHom (SeparableClosure K) degree
            (σ.wittIndex H) n) ≫
        SymplecticMatrix.diagonalTorus (Fin n) (CommRingCat.of (SeparableClosure K))
    simpa only [Iso.hom_inv_id_assoc, Category.assoc] using h
  obtain ⟨d', hcoords⟩ := exists_typeCIndex_of_blockTorus d.isSemisimple hd s hs Φ hsq
  exact fun a => typeC_distinguished_of_coordinates d d' hn e hcart hcoords hd hrn a

end Langlands.GroupScheme
