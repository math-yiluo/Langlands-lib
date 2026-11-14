import Langlands.GroupScheme.RelativeLevi.CentralizerNeighbourhood
import Langlands.GroupScheme.RelativeLevi.BorelOfTorusCentralizer
import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeLevi.OppositeBorelOverlap
import Langlands.GroupScheme.Dynamic.LocalPresentation
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Local dynamic Borel data from a prescribed regular residue cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeLevi

/-- Actual open neighbourhood data for a local dynamic Borel presentation
through the specified torus. -/
structure BorelDynamicNeighbourhoodData
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (s : S) where
  base : Scheme.{u}
  projection : base ⟶ S
  openImmersion : IsOpenImmersion projection
  contains : s ∈ Set.range projection
  split : IsSplitTorus ((CommGroupScheme.baseChange projection).obj T).toGrp
  cocharacter : cocharacterLattice ((CommGroupScheme.baseChange projection).obj T)
  positive :
    SubgroupFunctor.range ((GroupScheme.baseChange projection).map i) =
      Dynamic.parabolic (CommGroupScheme.groupHom cocharacter ≫
        (GroupScheme.baseChange projection).map t)
  centralizer :
    Dynamic.centralizer (CommGroupScheme.groupHom cocharacter ≫
        (GroupScheme.baseChange projection).map t) =
      SubgroupFunctor.range ((GroupScheme.baseChange projection).map t)
  negative : DynamicBorelData
    (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom cocharacter ≫
      (GroupScheme.baseChange projection).map t))

end RelativeLevi

/-- The prescribed positive and centralizer residue equalities persist
together on one open neighbourhood, and supply the negative Borel there. -/
theorem nonempty_borelDynamicNeighbourhood_of_residue
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (s : S) (ν : cocharacterLattice T)
    (hpos : SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
        (CommGroupScheme.groupHom ν ≫ t)))
    (hcent : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom t s)) :
    Nonempty (RelativeLevi.BorelDynamicNeighbourhoodData i T t s) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ b => (hG.isConnectedReductive_baseChange b).connectedSpace)
  have : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  have : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  have : GeometricallyConnected B.X.hom :=
    hi.isRelativeParabolicSubgroup.geometricallyConnected hG
  have : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  have : Mono i.hom.hom.left := Over.mono_left_of_mono _
  have hir : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let f := hir.liftOfLE t hti
  let χ := CommGroupScheme.groupHom ν ≫ t
  let χB := CommGroupScheme.groupHom ν ≫ f
  have hχ : χB ≫ i = χ := by
    rw [Category.assoc, hir.liftOfLE_comp]
  let b := S.fromSpecResidueField s
  have hbpoint : b (IsLocalRing.closedPoint (S.residueField s)) = s :=
    Scheme.fromSpecResidueField_apply _ _
  have hic : IsClosedSubgroup ((GroupScheme.baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint (S.residueField s))))).map i) := by
    rw [hbpoint]
    exact (hi.residueFiber s).1.isClosedSubgroup
  obtain ⟨U, p, hp, bU, hbU, hP⟩ :=
    Dynamic.exists_local_presentation_of_fieldPoint i χB b hic
      (by rw [hχ]; exact hpos)
  have : IsOpenImmersion p := hp
  rw [hχ] at hP
  obtain ⟨V, hsV, hZ⟩ :=
    RelativeCocharacterCentralizerNeighbourhood.exists_open_centralizer_eq_range
      t ν hG hT ht s hcent
  have hbVmem : b (IsLocalRing.closedPoint (S.residueField s)) ∈ V :=
    hbpoint.symm ▸ hsV
  let bV := Dynamic.fieldPointOpenLift b V hbVmem
  have hbV : bV ≫ V.ι = b := Dynamic.fieldPointOpenLift_comp b V hbVmem
  let W := pullback p V.ι
  let l : W ⟶ U := pullback.fst p V.ι
  let q : W ⟶ V := pullback.snd p V.ι
  let r : W ⟶ S := l ≫ p
  let bW : Spec (CommRingCat.of (S.residueField s)) ⟶ W :=
    pullback.lift bU bV (hbU.trans hbV.symm)
  have hbW : bW ≫ r = b := by
    rw [← Category.assoc, pullback.lift_fst, hbU]
  have hr : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (l ≫ p))
  have hsr : s ∈ Set.range r := by
    refine ⟨bW (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hbW]
    exact hbpoint
  obtain ⟨P, jP, _, _, hjP⟩ := (dynamicBaseRepresentability S G χ).1
  have hPrange : SubgroupFunctor.range ((GroupScheme.baseChange p).map i) =
      SubgroupFunctor.range ((GroupScheme.baseChange p).map jP) := by
    rw [SubgroupFunctor.range_baseChangeHom p jP, hjP.2, ← Dynamic.parabolic_baseChange]
    exact hP
  have hPrange' := congrArg (fun F => F.baseChange l) hPrange
  rw [← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom] at hPrange'
  have hPr := (SubgroupFunctor.range_eq_baseChange_comp_iff p l r rfl i jP).mp hPrange'
  rw [SubgroupFunctor.range_baseChangeHom r jP, hjP.2,
    ← Dynamic.parabolic_baseChange] at hPr
  obtain ⟨Z, jZ, _, _, hjZ⟩ := (dynamicBaseRepresentability S G χ).2.2
  have hZrange : SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map jZ) =
      SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map t) := by
    rw [SubgroupFunctor.range_baseChangeHom V.ι jZ, hjZ.2, ← Dynamic.centralizer_baseChange]
    exact hZ
  have hZrange' := congrArg (fun F => F.baseChange q) hZrange
  rw [← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom] at hZrange'
  have hZr := (SubgroupFunctor.range_eq_baseChange_comp_iff V.ι q r
    pullback.condition.symm jZ t).mp hZrange'
  rw [SubgroupFunctor.range_baseChangeHom r jZ, hjZ.2,
    ← Dynamic.centralizer_baseChange] at hZr
  let νr := cocharacterLattice.baseChange r T ν
  have hχr : Dynamic.baseChangeCocharacter r χ =
      CommGroupScheme.groupHom νr ≫ (GroupScheme.baseChange r).map t := by
    rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
  rw [hχr] at hPr hZr
  let N := oppositeBorelOfTorusCentralizer (S := W)
    (G := (GroupScheme.baseChange r).obj G)
    (T := (CommGroupScheme.baseChange r).obj T)
    (hG.baseChange r) (hT.baseChange r)
    ((GroupScheme.baseChange r).map t) (ht.baseChange r) (hmax.baseChange r) νr hZr
  exact ⟨⟨W, r, hr, hsr, hT.baseChange r, νr, hPr, hZr, N⟩⟩

/-- Choose actual neighbourhood data from the two prescribed residue equalities. -/
def borelDynamicNeighbourhoodOfResidue
    {S : Scheme.{u}} {G B : GroupScheme S} (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)
    (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (s : S) (ν : cocharacterLattice T)
    (hpos : SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
        (CommGroupScheme.groupHom ν ≫ t)))
    (hcent : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range (RelativeLevi.residueFiberHom t s)) :
    RelativeLevi.BorelDynamicNeighbourhoodData i T t s :=
  Classical.choice
    (nonempty_borelDynamicNeighbourhood_of_residue i T t hG hT ht hmax hi hti s ν hpos hcent)

end Langlands.GroupScheme
