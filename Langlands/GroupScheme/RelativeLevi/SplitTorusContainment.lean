import Langlands.GroupScheme.RelativeLevi.FieldLieContainment
import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction
import Langlands.GroupScheme.Torus.FieldCocharacterExtension
import Langlands.GroupScheme.Dynamic.LocalPresentation
import Langlands.GroupScheme.SubgroupFunctor.EtaleContainment

/-! # Spreading parabolic containment with a specified split torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- Combine a presentation on one open neighbourhood with containment on another. -/
theorem exists_open_range_le_of_two_neighbourhoods
    {S U : Scheme.{u}} {G P Q K : GroupScheme S}
    (i : P ⟶ G) (j : Q ⟶ G) (κ : K ⟶ G) [Mono i.hom.hom]
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (p : U ⟶ S) (hp : IsOpenImmersion p)
    (bU : Spec (CommRingCat.of k) ⟶ U) (hbU : bU ≫ p = b)
    (hP : SubgroupFunctor.range ((baseChange p).map i) =
      SubgroupFunctor.range ((baseChange p).map κ))
    (V : S.Opens) (hsV : b (IsLocalRing.closedPoint k) ∈ V)
    (hQ : SubgroupFunctor.range ((baseChange V.ι).map j) ≤
      SubgroupFunctor.range ((baseChange V.ι).map κ)) :
    ∃ O : S.Opens, b (IsLocalRing.closedPoint k) ∈ O ∧
      SubgroupFunctor.range ((baseChange O.ι).map j) ≤
        SubgroupFunctor.range ((baseChange O.ι).map i) := by
  let W := pullback p V.ι
  let q : W ⟶ U := pullback.fst _ _
  let r : W ⟶ V := pullback.snd _ _
  let a : W ⟶ S := q ≫ p
  have ha : a = r ≫ V.ι := pullback.condition
  have hQκ : SubgroupFunctor.range ((baseChange a).map j) ≤
      SubgroupFunctor.range ((baseChange a).map κ) := by
    rw [ha]
    apply (SubgroupFunctor.range_le_comp_baseChange_iff V.ι r j κ).mpr
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono r hQ
  have hκP : SubgroupFunctor.range ((baseChange a).map κ) ≤
      SubgroupFunctor.range ((baseChange a).map i) := by
    apply (SubgroupFunctor.range_le_comp_baseChange_iff p q κ i).mpr
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono q hP.ge
  let : IsOpenImmersion p := hp
  let : Etale a := inferInstance
  let bV := Dynamic.fieldPointOpenLift b V hsV
  have hbV : bV ≫ V.ι = b := Dynamic.fieldPointOpenLift_comp b V hsV
  let bW : Spec (CommRingCat.of k) ⟶ W :=
    pullback.lift bU bV (hbU.trans hbV.symm)
  have hbW : bW ≫ a = b := by
    simp only [a, bW, q, ← Category.assoc, pullback.lift_fst]
    exact hbU
  obtain ⟨O, hsO, hO⟩ := SubgroupFunctor.exists_open_range_le_of_etale
    a j i (bW (IsLocalRing.closedPoint k)) (hQκ.trans hκP)
  refine ⟨O, ?_, hO⟩
  have he : a (bW (IsLocalRing.closedPoint k)) = b (IsLocalRing.closedPoint k) := by
    change (bW ≫ a) _ = b _
    rw [hbW]
  exact he ▸ hsO

/-- A common ambient cocharacter compares two smooth subgroup ranges near a
residue point when it presents the larger fibre and contains the smaller one. -/
theorem exists_open_range_le_of_commonCocharacter
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected G.X.hom]
    [Smooth P.X.hom] [IsAffineHom P.X.hom] [GeometricallyConnected P.X.hom]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [GeometricallyConnected Q.X.hom]
    (i : P ⟶ G) (j : Q ⟶ G) [Mono i.hom.hom.left]
    (χP : (Gm S).toGrp ⟶ P) (χQ : (Gm S).toGrp ⟶ Q)
    (hχ : χQ ≫ j = χP ≫ i) (s : S)
    (hi : IsClosedSubgroup ((baseChange (S.fromSpecResidueField s)).map i))
    (hj : IsClosedSubgroup ((baseChange (S.fromSpecResidueField s)).map j))
    (hP : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter
        (S.fromSpecResidueField s) (χP ≫ i)))
    (hQ : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j) ≤
      Dynamic.parabolic (Dynamic.baseChangeCocharacter
        (S.fromSpecResidueField s) (χQ ≫ j))) :
    ∃ O : S.Opens, s ∈ O ∧
      SubgroupFunctor.range ((baseChange O.ι).map j) ≤
        SubgroupFunctor.range ((baseChange O.ι).map i) := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let b := S.fromSpecResidueField s
  have hb (z : Spec (CommRingCat.of (S.residueField s))) : b z = s :=
    S.fromSpecResidueField_apply s z
  have hic : IsClosedSubgroup ((baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint (S.residueField s))))).map i) := by
    rw [hb]
    exact hi
  obtain ⟨U, p, hp, bU, hbU, hpres⟩ :=
    Dynamic.exists_local_presentation_of_fieldPoint i χP b hic hP
  obtain ⟨V, hsV, hV⟩ := Dynamic.exists_range_le_parabolic_near_of_residueFiber
    j χQ s hj hQ
  obtain ⟨K, κ, hκc, hκL, hκ⟩ := (dynamicBaseRepresentability S G (χP ≫ i)).1
  have hD : SubgroupFunctor.range ((baseChange p).map i) =
      SubgroupFunctor.range ((baseChange p).map κ) := by
    rw [SubgroupFunctor.range_baseChangeHom p κ, hκ.2,
      ← Dynamic.parabolic_baseChange]
    exact hpres
  have hVκ : SubgroupFunctor.range ((baseChange V.ι).map j) ≤
      SubgroupFunctor.range ((baseChange V.ι).map κ) := by
    rw [SubgroupFunctor.range_baseChangeHom V.ι κ, hκ.2,
      ← Dynamic.parabolic_baseChange]
    simpa only [hχ] using hV
  obtain ⟨O, hsO, hO⟩ := exists_open_range_le_of_two_neighbourhoods i j κ b p hp bU hbU
    hD V ((hb _).symm ▸ hsV) hVκ
  exact ⟨O, (hb _) ▸ hsO, hO⟩

/-- Lift a cocharacter whose specified torus factors through a monic subgroup. -/
theorem exists_cocharacter_lift_of_torus_range_le
    {S : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G) [Mono i.hom.hom]
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (nuGlobal : cocharacterLattice T) (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ χ : (Gm S).toGrp ⟶ P, χ ≫ i = CommGroupScheme.groupHom nuGlobal ≫ t := by
  let hrep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  exact ⟨CommGroupScheme.groupHom nuGlobal ≫ hrep.liftOfLE t hTP, by
    rw [Category.assoc, hrep.liftOfLE_comp]⟩

/-- Forgetting commutativity identifies lattice base change with ambient
cocharacter base change, also after composing into an ambient group. -/
theorem baseChangeCocharacter_torus_comp
    {S U : Scheme.{u}} (b : U ⟶ S) {G : GroupScheme S}
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) :
    Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ t) =
      CommGroupScheme.groupHom (cocharacterLattice.baseChange b T ν) ≫
        (baseChange b).map t := by
  exact (Dynamic.baseChangeCocharacter_comp b (CommGroupScheme.groupHom ν) t).trans
    (congrArg (fun χ => χ ≫ (baseChange b).map t)
      (cocharacterLattice.groupHom_baseChange_dynamic b T ν).symm)

/-- A fibre presentation by the supplied split torus extends to two source
cocharacters with the same ambient composite. -/
theorem exists_commonCocharacter_of_splitTorus_presentation
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (i : P ⟶ G) (j : Q ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T))
    (hν : SubgroupFunctor.range ((baseChange b).map i) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ (baseChange b).map t))
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j) :
    ∃ (χP : (Gm S).toGrp ⟶ P) (χQ : (Gm S).toGrp ⟶ Q),
      χQ ≫ j = χP ≫ i ∧
      SubgroupFunctor.range ((baseChange b).map i) =
        Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χP ≫ i)) := by
  obtain ⟨nuGlobal, hnuGlobal⟩ :=
    IsSplitTorus.cocharacterLattice_baseChange_surjective_field T hT b ν
  obtain ⟨χP, hχP⟩ := exists_cocharacter_lift_of_torus_range_le i T t nuGlobal hTP
  obtain ⟨χQ, hχQ⟩ := exists_cocharacter_lift_of_torus_range_le j T t nuGlobal hTQ
  refine ⟨χP, χQ, hχQ.trans hχP.symm, ?_⟩
  have hbχ : Dynamic.baseChangeCocharacter b (χP ≫ i) =
      CommGroupScheme.groupHom ν ≫ (baseChange b).map t :=
    (congrArg (Dynamic.baseChangeCocharacter b) hχP).trans
      ((baseChangeCocharacter_torus_comp b T t nuGlobal).trans
        (congrArg (fun (nuF : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) =>
          CommGroupScheme.groupHom (G := Gm (Spec (CommRingCat.of k)))
            (H := (CommGroupScheme.baseChange b).obj T) nuF ≫ (baseChange b).map t)
          hnuGlobal))
  exact hν.trans (congrArg Dynamic.parabolic hbχ.symm)

/-- Extend the fixed-torus presentation of a parabolic field fibre. -/
theorem exists_commonCocharacter_of_splitTorus_fieldPresentation
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (i : P ⟶ G) (j : Q ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hG : IsConnectedReductive ((baseChange b).obj G))
    (hi : IsParabolicSubgroup ((baseChange b).map i))
    (ht : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map t))
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j) :
    ∃ (χP : (Gm S).toGrp ⟶ P) (χQ : (Gm S).toGrp ⟶ Q),
      χQ ≫ j = χP ≫ i ∧
      SubgroupFunctor.range ((baseChange b).map i) =
        Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χP ≫ i)) := by
  have hTPb : SubgroupFunctor.range ((baseChange b).map t) ≤
      SubgroupFunctor.range ((baseChange b).map i) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono b hTP
  obtain ⟨ν, hν⟩ := exists_fixedTorusDynamicPresentation_of_isParabolicSubgroup
    (T := (CommGroupScheme.baseChange b).obj T) hG ((baseChange b).map i) hi
    ((baseChange b).map t) ht hTPb
  exact exists_commonCocharacter_of_splitTorus_presentation i j T t hT b ν hν hTP hTQ

/-- Containment of residue-fibre parabolics containing the same specified
split torus spreads to an open neighbourhood of that point. -/
theorem exists_open_range_le_of_splitTorus_residueFiber
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (j : Q ⟶ G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (s : S)
    (ht : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map t))
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j) ≤
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map j) ≤
        SubgroupFunctor.range ((baseChange V.ι).map i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : GeometricallyConnected G.X.hom := hG.geometricallyConnected
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : GeometricallyConnected P.X.hom := hi.geometricallyConnected hG
  let : Smooth Q.X.hom := hj.smooth
  let : IsAffineHom Q.X.hom := hj.isAffineHom
  let : GeometricallyConnected Q.X.hom := hj.geometricallyConnected hG
  let : Mono i.hom.hom := hi.mono
  let : Mono i.hom.hom.left := Over.mono_left_of_mono _
  let : Mono j.hom.hom := hj.mono
  let b := S.fromSpecResidueField s
  obtain ⟨χP, χQ, hχ, hPb⟩ := exists_commonCocharacter_of_splitTorus_fieldPresentation
    i j T t hT b (hG.isConnectedReductive_residueFiber s) (hi.residueFiber s)
    ht hTP hTQ
  have hQb : SubgroupFunctor.range ((baseChange b).map j) ≤
      Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χQ ≫ j)) := by
    rw [hχ]
    exact hs.trans hPb.le
  exact exists_open_range_le_of_commonCocharacter i j χP χQ hχ s
    (hi.residueFiber s).isClosedSubgroup (hj.residueFiber s).isClosedSubgroup hPb hQb

/-- A chosen open carrying the proved split-torus parabolic containment. -/
def splitTorusParabolicContainmentNeighbourhood
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (j : Q ⟶ G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (s : S)
    (ht : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
      ((baseChange (S.fromSpecResidueField s)).map t))
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j) ≤
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    {V : S.Opens // s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map j) ≤
        SubgroupFunctor.range ((baseChange V.ι).map i)} :=
  ⟨(exists_open_range_le_of_splitTorus_residueFiber hG i j hi hj T t hT s ht hTP hTQ hs).choose,
    (exists_open_range_le_of_splitTorus_residueFiber hG i j hi hj T t hT s ht hTP hTQ hs).choose_spec⟩

end Langlands.GroupScheme.RelativeLevi
