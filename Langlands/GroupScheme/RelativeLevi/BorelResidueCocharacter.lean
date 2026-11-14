import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.FieldCocharacterExtension
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Cocharacters presenting a Borel on a specified residue fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B : GroupScheme S} {T : CommGroupScheme S}

/-- At a specified residue point, a Borel containing a split maximal torus
is presented by the fibre of a cocharacter of that same torus over the base.
The fibre centralizer is precisely the given torus. -/
theorem exists_residueBorelCocharacter
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (hmax : IsFibrewiseMaximalTorus t)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) (s : S) :
    ∃ ν : cocharacterLattice T,
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i s) =
          Dynamic.parabolic
            (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
              (CommGroupScheme.groupHom ν ≫ t)) ∧
        Dynamic.centralizer
            (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
              (CommGroupScheme.groupHom ν ≫ t)) =
          SubgroupFunctor.range (RelativeLevi.residueFiberHom t s) := by
  let b := S.fromSpecResidueField s
  let Gs := (GroupScheme.baseChange b).obj G
  let Ts := (CommGroupScheme.baseChange b).obj T
  let ts := (GroupScheme.baseChange b).map t
  let is := (GroupScheme.baseChange b).map i
  have hGs : IsConnectedReductive Gs := hG.isConnectedReductive_residueFiber s
  have : IsAffineHom Gs.X.hom := hGs.isAffineHom
  have hTs : IsSplitTorus Ts.toGrp := hT.baseChange b
  have htmax : IsMaximalTorus (T := Ts) ts := hmax s
  have his : IsBorelSubgroup is := (hi.residueFiber s).isBorelSubgroup
  have : IsClosedImmersion is.hom.hom.left := his.isClosedSubgroup
  have hirep : (SubgroupFunctor.range is).IsRepresentedBy is :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have htis : SubgroupFunctor.range ts ≤ SubgroupFunctor.range is := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    intro U x hx
    exact hti ((Over.map b).obj U) hx
  obtain ⟨νs, hνs, hrep⟩ :=
    (regularCocharacterBorel (S.residueField s) Gs hGs Ts ts hTs htmax).2.2
      _ is (hirep.liftOfLE ts htis) his (hirep.liftOfLE_comp ts htis)
  have hZ := centralizer_comp_eq_range_of_isRegular hGs hTs ts htmax νs hνs
  let ν := IsSplitTorus.extendFieldCocharacter T hT b νs
  have hν : cocharacterLattice.baseChange b T ν = νs :=
    IsSplitTorus.baseChange_extendFieldCocharacter T hT b νs
  have hχ : Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ t) =
      CommGroupScheme.groupHom νs ≫ ts := by
    rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic,
      hν]
    rfl
  exact ⟨ν, by rw [hχ]; exact hrep.2, by rw [hχ]; exact hZ⟩

namespace RelativeLevi

/-- An actual global torus cocharacter and its two subgroup-functor
certificates on a specified residue fibre. -/
structure BorelResidueCocharacterData
    (t : T.toGrp ⟶ G) (i : B ⟶ G) (s : S) where
  cocharacter : cocharacterLattice T
  parabolic_eq :
    SubgroupFunctor.range (residueFiberHom i s) =
      Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom cocharacter ≫ t))
  centralizer_eq :
    Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom cocharacter ≫ t)) =
      SubgroupFunctor.range (residueFiberHom t s)

end RelativeLevi

/-- Choose a cocharacter of the original split torus that presents the
given Borel and has the given torus as centralizer on the specified fibre. -/
def residueBorelCocharacter
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (hmax : IsFibrewiseMaximalTorus t)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) (s : S) :
    RelativeLevi.BorelResidueCocharacterData t i s :=
  Classical.choice <| by
    obtain ⟨ν, hP, hZ⟩ := exists_residueBorelCocharacter hG hT t hmax i hi hti s
    exact ⟨⟨ν, hP, hZ⟩⟩

end Langlands.GroupScheme
