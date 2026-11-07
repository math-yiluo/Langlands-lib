import Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterStatement
import Langlands.GroupScheme.Absolute.BorelIdentityComponent
import Langlands.GroupScheme.Absolute.SmoothSubgroupPointComparison
import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement

/-! # Fixed-torus classification from the local absolute Borel-overgroup input -/

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

/-- The local absolute point presentation suffices for the all-test fixed-torus
presentation of a smooth closed overgroup containing an ambient Borel. -/
theorem exists_fixedTorusDynamicPresentation_of_absoluteBorelOvergroup
    (hB : BorelConjugacyStatement.{u})
    (habsolute : AbsoluteBorelOvergroupCocharacterStatement.{u})
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
  obtain ⟨ζ, hpoints⟩ :=
    habsolute k G hG T j hT P i hi d.subgroup d.inclusion (d.isBorelPair hj hf)
  exact ⟨ζ, (Dynamic.range_eq_parabolic_iff_algClosed_points
    (CommGroupScheme.groupHom ζ ≫ j) hi).mpr hpoints⟩

end AlgClosed

/-- An independent absolute Borel-overgroup proof replaces both broad rational
standard-parabolic inputs in the original fixed-torus classification reduction. -/
theorem splitParabolicCocharacterStatement_of_absoluteBorelOvergroup
    (hB : BorelConjugacyStatement.{u})
    (habsolute : AbsoluteBorelOvergroupCocharacterStatement.{u})
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
  apply exists_fixedTorusDynamicPresentation_of_absoluteBorelOvergroup
    hB habsolute hG' (F.map j) (F.map i) (F.map f) hT' hj' hi'
  · exact (F.map_comp f i).symm.trans (congrArg F.map hf)
  · obtain ⟨B, jB, fB, hjB, hfB⟩ := hi.exists_isBorelSubgroup
    exact ⟨B, fB, hfB.symm ▸ hjB⟩

end Langlands.GroupScheme
