import Langlands.GroupScheme.SmoothMonoLocalIso
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Reductive.BaseChange

/-! # A torus centralizer equality near a regular residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeCocharacterCentralizerNeighbourhood

variable {S : Scheme.{u}} {G Z : GroupScheme S} {T : CommGroupScheme S}
    (t : T.toGrp ⟶ G) (ν : cocharacterLattice T) (z : Z ⟶ G)
    (hz : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy z)

/-- The given torus maps to the represented centralizer of its cocharacter. -/
def comparison : T.toGrp ⟶ Z :=
  hz.liftOfLE t (range_le_centralizer_groupHom_comp t ν)

/-- The comparison is compatible with the original torus inclusion. -/
theorem comparison_comp : comparison t ν z hz ≫ z = t :=
  hz.liftOfLE_comp t (range_le_centralizer_groupHom_comp t ν)

/-- Equality of the centralizer and torus on one residue fibre makes the
comparison on that fibre an actual scheme isomorphism. -/
theorem isIso_comparison_residueFiber
    (ht : IsClosedSubgroup t) (s : S)
    (hs : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map t)) :
    IsIso (((GroupScheme.baseChange (S.fromSpecResidueField s)).map
      (comparison t ν z hz)).hom.hom.left) := by
  let b := S.fromSpecResidueField s
  have hzr := Dynamic.isRepresentedBy_centralizer_baseChange b _ hz
  have : IsClosedImmersion ((GroupScheme.baseChange b).map t).hom.hom.left :=
    ht.baseChange b
  have htr : (Dynamic.centralizer
      (Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ t))).IsRepresentedBy
      ((GroupScheme.baseChange b).map t) :=
    ⟨Over.mono_of_mono_left _, hs.symm⟩
  let e := htr.isoOfIsRepresentedBy hzr
  have heq : (GroupScheme.baseChange b).map (comparison t ν z hz) = e.hom := by
    apply hzr.hom_ext
    rw [← Functor.map_comp, comparison_comp]
    exact (htr.isoOfIsRepresentedBy_hom_comp hzr).symm
  rw [heq]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- A split torus that is the centralizer on one residue fibre remains the
centralizer on some open neighbourhood of that base point. -/
theorem exists_open_centralizer_eq_range
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t) (s : S)
    (hs : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map t)) :
    ∃ V : S.Opens, s ∈ V ∧
      Dynamic.centralizer
          (Dynamic.baseChangeCocharacter V.ι (CommGroupScheme.groupHom ν ≫ t)) =
        SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map t) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have hGc : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hG.isConnectedReductive_baseChange b).connectedSpace)
  have : Smooth T.toGrp.X.hom := hT.smooth
  obtain ⟨Z, z, _, _, hz⟩ :=
    (dynamicBaseRepresentability S G (CommGroupScheme.groupHom ν ≫ t)).2.2
  obtain ⟨hZsm, hZconn⟩ :=
    (dynamicBaseSmoothConnected S G (CommGroupScheme.groupHom ν ≫ t) Z z).2.2 hz
  have : Smooth Z.X.hom := hZsm
  have : GeometricallyConnected Z.X.hom := hZconn hGc
  have : IsClosedImmersion t.hom.hom.left := ht
  let f := comparison t ν z hz
  have hfac : f ≫ z = t := comparison_comp t ν z hz
  have : Mono (f.hom.hom.left ≫ z.hom.hom.left) := by
    change Mono (f ≫ z).hom.hom.left
    rw [hfac]
    infer_instance
  have : Mono f.hom.hom.left := mono_of_mono f.hom.hom.left z.hom.hom.left
  obtain ⟨V, hsV, hfV⟩ := SmoothMonoLocalIso.isIsoNear_of_residueFiber f s
    (isIso_comparison_residueFiber t ν z hz ht s hs)
  refine ⟨V, hsV, ?_⟩
  let fV := (GroupScheme.baseChange V.ι).map f
  let zV := (GroupScheme.baseChange V.ι).map z
  have : IsIso fV.hom.hom.left := hfV
  have : IsIso ((Over.forget (V : Scheme.{u})).map fV.hom.hom) :=
    inferInstanceAs (IsIso fV.hom.hom.left)
  have : IsIso fV.hom.hom := isIso_of_reflects_iso fV.hom.hom (Over.forget _)
  have hfacV : fV ≫ zV = (GroupScheme.baseChange V.ι).map t := by
    rw [← Functor.map_comp, hfac]
  rw [Dynamic.centralizer_baseChange, ← (hz.baseChange V.ι).2, ← hfacV]
  apply le_antisymm
  · intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ inv fV.hom.hom, by
      change (y ≫ inv fV.hom.hom) ≫ (fV.hom.hom ≫ zV.hom.hom) = y ≫ zV.hom.hom
      rw [Category.assoc, IsIso.inv_hom_id_assoc]⟩
  · exact SubgroupFunctor.range_comp_le fV zV

end Langlands.GroupScheme.RelativeCocharacterCentralizerNeighbourhood
