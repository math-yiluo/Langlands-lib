import Langlands.GroupScheme.Absolute.BorelIdentityComponent
import Langlands.GroupScheme.Absolute.StandardDynamicOvergroup
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # A conditional fixed-torus parabolic classification reduction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [Smooth P.X.hom]

/-- Borel conjugacy, regular-cocharacter Borels, and the two standard-parabolic
statements give an actual fixed-torus presentation of a smooth closed overgroup
containing an ambient Borel. All four structural statements are explicit inputs. -/
theorem exists_fixedTorusDynamicPresentation_of_borel
    (hB : BorelConjugacyStatement.{u})
    (hregular : RegularCocharacterBorelStatement.{u})
    (hpoints : StandardParabolicPointsStatement.{u})
    (hstandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G)
    (j : T.toGrp ⟶ G) (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    (hi : IsClosedSubgroup i) (hf : f ≫ i = j)
    (hex : ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ P),
      IsBorelSubgroup (b ≫ i)) :
    ∃ ζ : cocharacterLattice T,
      SubgroupFunctor.range i =
        Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let d := BorelExistence.borelPairInOvergroupData j i f hT hj hi hf
    (borelSubgroupsAreConjugate_of_borelConjugacy hB) hex
  obtain ⟨ν, hν, hrep⟩ :=
    (hregular k G hG T j hT hj).2.2 d.subgroup (d.inclusion ≫ i)
      d.torusFactor d.isBorelSubgroup
        (by rw [← Category.assoc, d.torusFactor_comp, hf])
  have hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range i := by
    rw [← hrep.2]
    exact SubgroupFunctor.range_le_of_factor d.inclusion rfl
  let result := standardDynamicOvergroupData_of_statements j ν i
    hpoints hstandard hG (hj.isMaximalSplitTorus hT) hν hi hle
  exact ⟨result.cocharacter, result.range_eq⟩

end AlgClosed

/-- Reduction of the exact arbitrary-field target to five explicit structural
statements. The algebraic-closure Borel is taken directly from parabolicity;
no parabolic field-extension theorem is used. -/
theorem splitParabolicCocharacterStatement_of_structuralStatements
    (hB : BorelConjugacyStatement.{u})
    (hregular : RegularCocharacterBorelStatement.{u})
    (hpoints : StandardParabolicPointsStatement.{u})
    (hstandard : StandardCocharacterStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u}) :
    SplitParabolicCocharacterStatement.{u} := by
  intro k _ G hG T j hT hj P i f hi hf
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth P.X.hom := hi.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply (exists_range_eq_parabolic_iff_baseChange
    (K := AlgebraicClosure k) T j i hT).mpr
  let b := algebraBaseMap k (AlgebraicClosure k)
  let F := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  have hG' : IsConnectedReductive (F.obj G) :=
    hG.baseChange_toAlgebraicClosure
  have hT' : IsSplitTorus T'.toGrp := hT.baseChange b
  have hj' : IsMaximalTorus (T := T') (F.map j) :=
    (hmax k (AlgebraicClosure k) G T j hj.1 hj.2.1).mp hj
  have hi' : IsClosedSubgroup (F.map i) :=
    hi.isClosedSubgroup.baseChange b
  have : Smooth (F.obj P).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd P.X.hom b)
    infer_instance
  apply exists_fixedTorusDynamicPresentation_of_borel
    hB hregular hpoints hstandard hG' (F.map j) (F.map i) (F.map f)
      hT' hj' hi'
  · exact (F.map_comp f i).symm.trans (congrArg F.map hf)
  · obtain ⟨B, jB, fB, hjB, hfB⟩ := hi.exists_isBorelSubgroup
    exact ⟨B, fB, hfB.symm ▸ hjB⟩

/-- Select an actual integral cocharacter and its all-test presentation equality
from the five explicit structural inputs. -/
def splitParabolicCocharacterPresentation
    (hB : BorelConjugacyStatement.{u})
    (hregular : RegularCocharacterBorelStatement.{u})
    (hpoints : StandardParabolicPointsStatement.{u})
    (hstandard : StandardCocharacterStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hj : IsMaximalTorus j)
    {P : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) (f : T.toGrp ⟶ P)
    (hi : IsParabolicSubgroup i) (hf : f ≫ i = j) :
    FixedTorusDynamicPresentations T j i := by
  let h := splitParabolicCocharacterStatement_of_structuralStatements
    hB hregular hpoints hstandard hmax k G hG T j hT hj P i f hi hf
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.GroupScheme
