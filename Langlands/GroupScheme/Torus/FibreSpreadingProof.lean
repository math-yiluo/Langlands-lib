import Langlands.GroupScheme.Torus.FibreSpreadingStatement
import Langlands.GroupScheme.Torus.FibreSpreadingSmoothness
import Langlands.GroupScheme.Torus.SmoothFibreSpreading
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.BaseChange

/-! # A torus fibre spreads to an open neighbourhood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A torus fibre of an fppf affine group with connected fibres spreads to a
Zariski neighbourhood of the given point. -/
theorem torusFibreSpreading : TorusFibreSpreadingStatement.{u} := by
  intro S G _ _ _ hconn s hs
  have : GeometricallyConnected G.X.hom :=
    geometricallyConnected_of_connected_residueFibres G hconn
  obtain ⟨U, hsU, hsm⟩ := exists_smooth_nhd_of_smooth_residueFiber G s hs.smooth
  let GU := (baseChange U.ι).obj G
  let t : U := ⟨s, hsU⟩
  have : Smooth GU.X.hom := hsm
  have : IsAffineHom GU.X.hom := MorphismProperty.pullback_snd G.X.hom U.ι inferInstance
  have : GeometricallyConnected GU.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom U.ι))
  let a := S.fromSpecResidueField s
  let b := (U : Scheme).fromSpecResidueField t
  let c := Spec.map (U.ι.residueFieldMap t)
  let : Algebra (S.residueField s) ((U : Scheme).residueField t) :=
    (U.ι.residueFieldMap t).hom.toAlgebra
  have hbc : c ≫ a = b ≫ U.ι := U.ι.SpecMap_residueFieldMap_fromSpecResidueField t
  let e : (baseChange b).obj GU ≅
      (baseChange c).obj (RelativeIdentityComponent.residueFiber G s) :=
    (baseChangeCompIso U.ι b G).symm ≪≫
      eqToIso (congrArg (fun f => (baseChange f).obj G) hbc.symm) ≪≫
        baseChangeCompIso a c G
  have hbase : IsTorus ((baseChange c).obj
      (RelativeIdentityComponent.residueFiber G s)) := by
    change IsTorus ((baseChange (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) ((U : Scheme).residueField t))))).obj
        (RelativeIdentityComponent.residueFiber G s))
    exact IsTorus.baseChange (k := S.residueField s)
      (K := (U : Scheme).residueField t) hs
  have hst : IsTorus (RelativeIdentityComponent.residueFiber GU t) :=
    IsTorus.of_iso (k := (U : Scheme).residueField t)
      (G := RelativeIdentityComponent.residueFiber GU t)
      (H := (baseChange c).obj (RelativeIdentityComponent.residueFiber G s)) e hbase
  obtain ⟨V, q, hq, htq, hsplit⟩ := exists_etale_split_of_torus_residueFibre GU t hst
  let : Etale q := hq
  have hsplit' : IsSplitTorus ((baseChange (q ≫ U.ι)).obj G) :=
    IsSplitTorus.of_iso (baseChangeCompIso U.ι q G) hsplit
  obtain ⟨W, hW, htorus⟩ := relativeTorus_etaleImage_of_split G (q ≫ U.ι) hsplit'
  refine ⟨W, ?_, htorus⟩
  rw [← SetLike.mem_coe, hW]
  obtain ⟨v, hv⟩ := htq
  exact ⟨v, by change U.ι (q v) = s; rw [hv]; rfl⟩

end Langlands.GroupScheme
