import Langlands.GroupScheme.Dynamic.ConnectedPresentation
import Langlands.GroupScheme.RelativeLevi.BorelResidueCocharacter
import Langlands.GroupScheme.RelativeLevi.CentralizerNeighbourhood
import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof

/-! # Global dynamic presentations of Borels through split maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Over a connected base, equality of a split torus with a cocharacter
centralizer on one residue fibre holds over the whole base. -/
theorem centralizer_eq_splitTorus_of_residue_of_connected
    {S : Scheme.{u}} [ConnectedSpace S] {G : GroupScheme S} {T : CommGroupScheme S}
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t) (ν : cocharacterLattice T)
    (s : S)
    (hs : Dynamic.centralizer
      (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
        (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom t s)) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) = SubgroupFunctor.range t := by
  let := hG.smooth
  let := hG.isAffineHom
  let : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hG.isConnectedReductive_baseChange b).connectedSpace)
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w t.hom.hom]
    infer_instance
  let : GeometricallyConnected T.toGrp.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hT.baseChange b).connectedSpace)
  obtain ⟨Z, z, hzc, -, hz⟩ :=
    (dynamicBaseRepresentability S G (CommGroupScheme.groupHom ν ≫ t)).2.2
  let : IsClosedImmersion z.hom.hom.left := hzc
  let : Smooth Z.X.hom := (dynamicBaseSmoothConnected S G
    (CommGroupScheme.groupHom ν ≫ t) Z z).2.2 hz |>.1
  let : GeometricallyConnected Z.X.hom := ((dynamicBaseSmoothConnected S G
    (CommGroupScheme.groupHom ν ≫ t) Z z).2.2 hz).2 inferInstance
  let : IsAffineHom Z.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let f := RelativeCocharacterCentralizerNeighbourhood.comparison t ν z hz
  have hfac : f ≫ z = t :=
    RelativeCocharacterCentralizerNeighbourhood.comparison_comp t ν z hz
  have : Mono (f.hom.hom ≫ z.hom.hom) := by
    change Mono (f ≫ z).hom.hom
    rw [hfac]
    infer_instance
  let : Mono f.hom.hom := mono_of_mono f.hom.hom z.hom.hom
  have hfs : IsIso ((baseChange (S.fromSpecResidueField s)).map f) := by
    let : IsIso (((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left) :=
      RelativeCocharacterCentralizerNeighbourhood.isIso_comparison_residueFiber
        t ν z hz ht s hs
    exact TorusIsomorphismLocus.isIso_of_underlying _
  let : IsIso f := SmoothIsomorphismLocus.isIso_of_fieldIso_of_connected
    f (S.residueField s) (S.fromSpecResidueField s) hfs
  rw [← hz.2, ← hfac]
  exact (SubgroupFunctor.range_iso_comp (asIso f) z).symm

namespace RelativeLevi

/-- One cocharacter of the original split torus globally presents the
supplied Borel and has precisely that torus as its centralizer. -/
structure GlobalBorelCocharacterData
    {S : Scheme.{u}} {G B : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) (i : B ⟶ G) where
  cocharacter : cocharacterLattice T
  parabolic_eq : SubgroupFunctor.range i =
    Dynamic.parabolic (CommGroupScheme.groupHom cocharacter ≫ t)
  centralizer_eq : Dynamic.centralizer (CommGroupScheme.groupHom cocharacter ≫ t) =
    SubgroupFunctor.range t

end RelativeLevi

/-- Every Borel through a split maximal torus over a connected base has a
single global dynamic presentation by a cocharacter of that same torus. -/
def globalBorelCocharacter
    {S : Scheme.{u}} [ConnectedSpace S] {G B : GroupScheme S} {T : CommGroupScheme S}
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    RelativeLevi.GlobalBorelCocharacterData t i := by
  let := hG.smooth
  let := hG.isAffineHom
  let : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hG.isConnectedReductive_baseChange b).connectedSpace)
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : GeometricallyConnected B.X.hom := hi.isRelativeParabolicSubgroup.geometricallyConnected hG
  have hic : IsClosedSubgroup i := relativeParabolicClosed S G B i hG hi.isRelativeParabolicSubgroup
  let : IsClosedImmersion i.hom.hom.left := hic
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let s : S := Classical.choice inferInstance
  let d := residueBorelCocharacter hG hT t hmax i hi hti s
  let hir : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let l := hir.liftOfLE t hti
  let χ := CommGroupScheme.groupHom d.cocharacter ≫ l
  have hχ : χ ≫ i = CommGroupScheme.groupHom d.cocharacter ≫ t := by
    rw [Category.assoc, hir.liftOfLE_comp]
  refine ⟨d.cocharacter, ?_, ?_⟩
  · rw [← hχ]
    exact Dynamic.range_eq_parabolic_of_field_presentation i hic χ
      (S.residueField s) (S.fromSpecResidueField s) (by rw [hχ]; exact d.parabolic_eq)
  · exact centralizer_eq_splitTorus_of_residue_of_connected hG hT t ht d.cocharacter s
      d.centralizer_eq

end Langlands.GroupScheme
