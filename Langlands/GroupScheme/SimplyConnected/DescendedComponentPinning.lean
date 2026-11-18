import Langlands.GroupScheme.SimplyConnected.GaloisFactorPinning
import Langlands.GroupScheme.SimplyConnected.ScalarExtensionFactorIndex
import Langlands.GroupScheme.Reductive.TitsComponentFromPinning
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection

/-! # The actual descended factor realizes the prescribed entire Cartan component -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

private theorem original_maximalTorus_of_pinning {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : GaloisPinningData k L G) : IsMaximalTorus p.inclusion := by
  have hT : IsTorus p.torus.toGrp := ⟨L, inferInstance, inferInstance, p.isSplitTorus⟩
  let : IsAffine p.torus.X.left := SplittingAssembly.isAffine_of_isTorus _ hT
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Flat (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.1
  let : Surjective (algebraBaseMap k L) := (fieldExtension_fpqc k L).1
  have hi := IsClosedSubgroup.of_baseChange_of_isAffine (algebraBaseMap k L) p.isMaximalTorus.2.1
  exact IsMaximalTorus.of_baseChange hi p.isMaximalTorus

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  (d : TitsIndexData G)
  (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))
  (hG : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G))

local instance descendedComponentPinning_geometricAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance descendedComponentPinning_geometricSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

/-- The exact selected stabilizer-field group model has a genuine Galois
pinning realizing the whole prescribed original Cartan component, with every
ordered Cartan entry and every relative full-star element retained. -/
theorem nonempty_descendedComponentPinning (hSC : IsSimplyConnected G) (a : d.Vertex) :
    Nonempty (d.PinningComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1) := by
  let L := SeparableClosure k
  let i := d.geometricFactorIndex D hG a
  let E := D.factorStabilizerField i
  let A := D.factorStabilizerDescent i
  let H := A.1
  let j := A.2.1
  let GE := (GroupScheme.baseChange (algebraBaseMap k E)).obj G
  let S := GaloisPinningData.scalarExtension (E := E) d.pinning
  let DG := D.ofIso S.groupIso
  have hGE : IsSimplyConnected GE := isSimplyConnectedFieldExtension k E G hSC
  let : IsAffineHom GE.X.hom := hGE.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth GE.X.hom := hGE.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom H.X.hom := inferInstanceAs (IsAffineHom A.1.X.hom)
  let : LocallyOfFiniteType H.X.hom := inferInstanceAs (LocallyOfFiniteType A.1.X.hom)
  have hH : IsAlmostSimple H := D.isAlmostSimple_factorStabilizerDescent i
  let DE := hGE.almostSimpleProduct
  let F := DE.normalFactorTorusProjection hH j A.2.2.2.2.1
    (D.isNormal_factorStabilizerDescent i) hGE.isSemisimple.isConnectedReductive
    S.pinning.inclusion (original_maximalTorus_of_pinning S.pinning)
  let r := A.2.2.1
  have hr : (GroupScheme.baseChange (algebraBaseMap E L)).map j = r.hom ≫ DG.inclusion i := by
    rw [SimplyConnectedAlmostSimpleProduct.ofIso_inclusion, S.groupIso_eq]
    exact A.2.2.2.2.2
  obtain ⟨C⟩ := F.nonempty_galoisFactorPinning S.pinning DG (hG.of_iso S.groupIso) i r hr
    hH.isSemisimple.isConnectedReductive
  let ev : d.Vertex ≃ S.pinning.base.support := S.rootEquiv.indexEquiv.subtypeEquiv S.base_eq
  let ef : {b : d.Vertex // d.geometricFactorIndex D hG b = i} ≃
      {b : S.pinning.base.support // DG.rootDatumFactorIndex (hG.of_iso S.groupIso)
        S.pinning.isSplitTorus _ S.pinning.isMaximalTorus S.pinning.isRootDatum b.val = i} :=
    ev.subtypeEquiv (fun b => by
      change d.geometricFactorIndex D hG b = i ↔
        DG.rootDatumFactorIndex (hG.of_iso S.groupIso) S.pinning.isSplitTorus _
          S.pinning.isMaximalTorus S.pinning.isRootDatum (S.rootEquiv.indexEquiv b.val) = i
      rw [S.rootDatumFactorIndex_eq D hG b.val]
      rfl)
  let v : C.pinning.base.support ≃ d.CartanComponent a :=
    C.vertices.trans (ef.symm.trans (d.geometricFactorFibreComponentEquiv D hG a))
  have hv (b : C.pinning.base.support) : ev (v b).val = (C.vertices b).val :=
    congrArg Subtype.val (ef.apply_symm_apply (C.vertices b))
  refine ⟨{
    pinning := C.pinning
    vertices := v
    cartan_eq := ?_
    star_eq := ?_ }⟩
  · intro b c
    calc
      d.cartan (v b).val (v c).val = S.pinning.rootDatum.pairing
          (ev (v b).val).val (ev (v c).val).val := S.rootEquiv.toHom.pairing.symm
      _ = S.pinning.rootDatum.pairing (C.vertices b).val.val (C.vertices c).val.val := by
        rw [hv b, hv c]
      _ = C.pinning.rootDatum.pairing b.val c.val := C.cartan_eq b c
  · intro ρ b
    apply Subtype.ext
    apply S.rootEquiv.indexEquiv.injective
    have hval (b : C.pinning.base.support) : S.rootEquiv.indexEquiv (v b).val.val =
        (C.vertices b).val.val := congrArg Subtype.val (hv b)
    have hs := congrArg (fun z => z.indexEquiv (v b).val.val) (S.star_eq ρ)
    calc
      S.rootEquiv.indexEquiv (v (C.pinning.simpleStar ρ b)).val.val =
          (C.vertices (C.pinning.simpleStar ρ b)).val.val := hval _
      _ = (S.pinning.starAction ρ).val.indexEquiv (C.vertices b).val.val := C.star_eq ρ b
      _ = (S.pinning.starAction ρ).val.indexEquiv (S.rootEquiv.indexEquiv (v b).val.val) :=
        congrArg (S.pinning.starAction ρ).val.indexEquiv (hval b).symm
      _ = S.rootEquiv.indexEquiv (d.star (ρ.restrictScalars k) (v b).val).val := hs.symm

/-- Choose the actual stabilizer-field pinning comparison whose existence was
proved above, retaining the exact field, descended group and whole component. -/
def descendedComponentPinning (hSC : IsSimplyConnected G) (a : d.Vertex) :
    d.PinningComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1 :=
  Classical.choice (d.nonempty_descendedComponentPinning D hG hSC a)

end TitsIndexData
end Langlands.GroupScheme
