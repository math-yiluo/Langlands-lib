import Langlands.GroupScheme.RelativeLevi.SplitTorusContainment
import Langlands.GroupScheme.RelativeLevi.ParabolicTransport
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # Spreading parabolic containment with a specified relative torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- Containment of actual residue-fibre subgroup ranges persists at every
supplied field-valued point over the same base point. -/
theorem range_le_fieldPoint_of_residueFiber
    {S : Scheme.{u}} {G P Q : GroupScheme S} (i : P ⟶ G) (j : Q ⟶ G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (h : SubgroupFunctor.range
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map j) ≤
      SubgroupFunctor.range
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map i)) :
    SubgroupFunctor.range ((baseChange b).map j) ≤
      SubgroupFunctor.range ((baseChange b).map i) := by
  let a := S.fromSpecResidueField (b (IsLocalRing.closedPoint k))
  let c := Spec.map (fieldPointResidueMap b)
  have hc : SubgroupFunctor.range ((baseChange c).map ((baseChange a).map j)) ≤
      SubgroupFunctor.range ((baseChange c).map ((baseChange a).map i)) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono c h
  have hd := (SubgroupFunctor.range_le_comp_baseChange_iff a c j i).mpr hc
  dsimp only [a, c] at hd
  rwa [fieldPointResidueMap_factorization] at hd

/-- Containment at one residue fibre spreads to a Zariski neighbourhood when
the two relative parabolics contain a common specified relative maximal torus. -/
theorem exists_open_range_le_of_torus_residueFiber
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (j : Q ⟶ G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsFibrewiseMaximalTorus t) (s : S)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j) ≤
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map j) ≤
        SubgroupFunctor.range ((baseChange V.ι).map i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom := hi.mono
  obtain ⟨𝒰, h𝒰⟩ := hT
  obtain ⟨a, u, hu⟩ := 𝒰.exists_eq s
  let U := 𝒰.X a
  let p : U ⟶ S := 𝒰.f a
  let b := U.fromSpecResidueField u
  have hbu : b (IsLocalRing.closedPoint (U.residueField u)) = u :=
    U.fromSpecResidueField_apply u _
  have hbs : (b ≫ p) (IsLocalRing.closedPoint (U.residueField u)) = s := by
    change p (b _) = s
    rw [hbu]
    exact hu
  have hmax := isMaximalTorus_baseChange_comp p b T t (ht.fieldPoint (b ≫ p))
  have hb : SubgroupFunctor.range ((baseChange (b ≫ p)).map j) ≤
      SubgroupFunctor.range ((baseChange (b ≫ p)).map i) := by
    apply range_le_fieldPoint_of_residueFiber i j (k := U.residueField u) (b ≫ p)
    exact hbs.symm ▸ hs
  have hTPU : SubgroupFunctor.range ((baseChange p).map t) ≤
      SubgroupFunctor.range ((baseChange p).map i) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono p hTP
  have hTQU : SubgroupFunctor.range ((baseChange p).map t) ≤
      SubgroupFunctor.range ((baseChange p).map j) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono p hTQ
  obtain ⟨V, huV, hV⟩ := exists_open_range_le_of_splitTorus_residueFiber
    (hG.baseChange p) ((baseChange p).map i) ((baseChange p).map j)
    (hi.baseChange hG p) (hj.baseChange hG p)
    ((CommGroupScheme.baseChange p).obj T) ((baseChange p).map t) (h𝒰 a) u
    hmax hTPU hTQU ((SubgroupFunctor.range_le_comp_baseChange_iff p b j i).mp hb)
  let : Etale p := 𝒰.map_prop a
  let q : (V : Scheme) ⟶ S := V.ι ≫ p
  let : Etale q := inferInstance
  have hq : SubgroupFunctor.range ((baseChange q).map j) ≤
      SubgroupFunctor.range ((baseChange q).map i) :=
    (SubgroupFunctor.range_le_comp_baseChange_iff p V.ι j i).mpr hV
  obtain ⟨O, huO, hO⟩ := SubgroupFunctor.exists_open_range_le_of_etale
    q j i ⟨u, huV⟩ hq
  refine ⟨O, ?_, hO⟩
  have he : q ⟨u, huV⟩ = s := hu
  exact he ▸ huO

/-- An actual open carrying containment, selected after splitting the supplied
relative maximal torus and descending the resulting etale neighbourhood. -/
def torusParabolicContainmentNeighbourhood
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (j : Q ⟶ G)
    (hi : IsRelativeParabolicSubgroup i) (hj : IsRelativeParabolicSubgroup j)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsFibrewiseMaximalTorus t) (s : S)
    (hTP : SubgroupFunctor.range t ≤ SubgroupFunctor.range i)
    (hTQ : SubgroupFunctor.range t ≤ SubgroupFunctor.range j)
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map j) ≤
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i)) :
    {V : S.Opens // s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map j) ≤
        SubgroupFunctor.range ((baseChange V.ι).map i)} :=
  ⟨(exists_open_range_le_of_torus_residueFiber hG i j hi hj T t hT ht s hTP hTQ hs).choose,
    (exists_open_range_le_of_torus_residueFiber hG i j hi hj T t hT ht s hTP hTQ hs).choose_spec⟩

end Langlands.GroupScheme.RelativeLevi
