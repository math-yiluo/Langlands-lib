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

/-- An actual component comparison over an intermediate field, retaining the
retraction and the same vertices for simple-root inflation. -/
structure ComponentPinningWithProjection (E : IntermediateField k (SeparableClosure k))
    (a : d.Vertex) {H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (S : GaloisPinningData.ScalarExtension (E := E) d.pinning)
    (j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj G) where
  comparison : d.PinningComponentComparison E a H
  projection : S.pinning.FactorProjection comparison.pinning
  inclusion_eq : projection.inclusion = j
  vertices_eq : ∀ b, projection.vertices b =
    (S.rootEquiv.indexEquiv.subtypeEquiv S.base_eq) (comparison.vertices b).val

private def componentPinningWithProjectionOfFactor
    {E : IntermediateField k (SeparableClosure k)} (a : d.Vertex)
    {H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (S : GaloisPinningData.ScalarExtension (E := E) d.pinning)
    {j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj G}
    (CP : S.pinning.FactorPinningWithProjection (D.ofIso S.groupIso)
      (hG.of_iso S.groupIso) (d.geometricFactorIndex D hG a) j) :
    d.ComponentPinningWithProjection E a S j := by
  let i := d.geometricFactorIndex D hG a
  let DG := D.ofIso S.groupIso
  let C := CP.comparison
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
  let comp : d.PinningComponentComparison E a H := {
    pinning := C.pinning
    vertices := v
    cartan_eq := by
      intro b c
      calc
        d.cartan (v b).val (v c).val = S.pinning.rootDatum.pairing
            (ev (v b).val).val (ev (v c).val).val := S.rootEquiv.toHom.pairing.symm
        _ = S.pinning.rootDatum.pairing (C.vertices b).val.val (C.vertices c).val.val := by
          rw [hv b, hv c]
        _ = C.pinning.rootDatum.pairing b.val c.val := C.cartan_eq b c
    star_eq := by
      intro ρ b
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
        _ = S.rootEquiv.indexEquiv (d.star (ρ.restrictScalars k) (v b).val).val := hs.symm }
  exact ⟨comp, CP.projection, CP.inclusion_eq,
    fun b => (CP.vertices_eq b).trans (hv b).symm⟩

omit [Smooth G.X.hom] in
private theorem nonempty_componentPinningWithProjectionOfRecovered
    {E : IntermediateField k (SeparableClosure k)} (a : d.Vertex)
    {H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (S : GaloisPinningData.ScalarExtension (E := E) d.pinning)
    {j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj G}
    (hSC : IsSimplyConnected G) (hH : IsAlmostSimple H) (hj : IsClosedSubgroup j)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (r : (GroupScheme.baseChange (algebraBaseMap E (SeparableClosure k))).obj H ≅
      D.factor (d.geometricFactorIndex D hG a))
    (hr : (GroupScheme.baseChange (algebraBaseMap E (SeparableClosure k))).map j =
      r.hom ≫ (D.inclusion (d.geometricFactorIndex D hG a) ≫
        (GaloisPointComparison.towerBaseChangeIso k E (SeparableClosure k) G).inv)) :
    Nonempty (d.ComponentPinningWithProjection E a S j) := by
  let GE := (GroupScheme.baseChange (algebraBaseMap k E)).obj G
  have hGE : IsSimplyConnected GE := isSimplyConnectedFieldExtension k E G hSC
  let : IsAffineHom GE.X.hom := hGE.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth GE.X.hom := hGE.isSemisimple.isConnectedReductive.smooth
  let F := hGE.almostSimpleProduct.normalFactorTorusProjection hH j hj hn
    hGE.isSemisimple.isConnectedReductive S.pinning.inclusion
    (original_maximalTorus_of_pinning S.pinning)
  have hr' : (GroupScheme.baseChange (algebraBaseMap E (SeparableClosure k))).map j =
      r.hom ≫ (D.ofIso S.groupIso).inclusion (d.geometricFactorIndex D hG a) := by
    rw [SimplyConnectedAlmostSimpleProduct.ofIso_inclusion, S.groupIso_eq]
    exact hr
  obtain ⟨CP⟩ := F.nonempty_galoisFactorPinningWithProjection S.pinning (D.ofIso S.groupIso)
    (hG.of_iso S.groupIso) (d.geometricFactorIndex D hG a) r hr' hH.isSemisimple.isConnectedReductive
  exact ⟨d.componentPinningWithProjectionOfFactor D hG a S CP⟩

private theorem nonempty_componentPinningWithProjectionOfDescentData
    (a : d.Vertex) (A : type_of% (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)))
    [IsAffineHom A.1.X.hom] [LocallyOfFiniteType A.1.X.hom]
    (hSC : IsSimplyConnected G) (hH : IsAlmostSimple A.1)
    (hn : (SubgroupFunctor.range A.2.1).IsNormal) :
    Nonempty (d.ComponentPinningWithProjection
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (GaloisPinningData.scalarExtension
        (E := D.factorStabilizerField (d.geometricFactorIndex D hG a)) d.pinning) A.2.1) :=
  d.nonempty_componentPinningWithProjectionOfRecovered D hG a
    (GaloisPinningData.scalarExtension
      (E := D.factorStabilizerField (d.geometricFactorIndex D hG a)) d.pinning)
    hSC hH A.2.2.2.2.1 hn A.2.2.1 A.2.2.2.2.2

/-- The exact selected stabilizer-field group model has a genuine Galois
pinning realizing the whole prescribed original Cartan component and the
compatible factor projection. -/
theorem nonempty_descendedComponentPinningWithProjection
    (hSC : IsSimplyConnected G) (a : d.Vertex) :
    -- Retain the instance arguments of the recovery lemma in the specialized type.
    type_of% (d.nonempty_componentPinningWithProjectionOfDescentData D hG a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)) hSC
      (D.isAlmostSimple_factorStabilizerDescent (d.geometricFactorIndex D hG a))
      (D.isNormal_factorStabilizerDescent (d.geometricFactorIndex D hG a))) :=
  d.nonempty_componentPinningWithProjectionOfDescentData D hG a
    (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)) hSC
    (D.isAlmostSimple_factorStabilizerDescent (d.geometricFactorIndex D hG a))
    (D.isNormal_factorStabilizerDescent (d.geometricFactorIndex D hG a))

/-- The exact selected stabilizer-field group model has a genuine Galois
pinning realizing the whole prescribed original Cartan component, with every
ordered Cartan entry and every relative full-star element retained. -/
theorem nonempty_descendedComponentPinning (hSC : IsSimplyConnected G) (a : d.Vertex) :
    Nonempty (d.PinningComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1) := by
  obtain ⟨C⟩ := d.nonempty_descendedComponentPinningWithProjection D hG hSC a
  exact ⟨C.comparison⟩

/-- Choose the actual stabilizer-field pinning comparison whose existence was
proved above, retaining the exact field, descended group and whole component. -/
def descendedComponentPinning (hSC : IsSimplyConnected G) (a : d.Vertex) :
    d.PinningComponentComparison
      (D.factorStabilizerField (d.geometricFactorIndex D hG a)) a
      (D.factorStabilizerDescent (d.geometricFactorIndex D hG a)).1 :=
  Classical.choice (d.nonempty_descendedComponentPinning D hG hSC a)

end TitsIndexData
end Langlands.GroupScheme
