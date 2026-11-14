import Langlands.GroupScheme.RelativeLevi.ParabolicPresheafBaseChange

/-! # Pullback of a supplied parabolic representing scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- The actual pullback of a supplied representing scheme represents parabolics
of the pulled-back group. -/
def representableByBaseChange (b : S' ⟶ S) (hG : IsReductive G) {M : Over S}
    (e : (parabolicPresheaf G hG).RepresentableBy M) :
    (parabolicPresheaf ((GroupScheme.baseChange b).obj G) (hG.baseChange b)).RepresentableBy
      ((Over.pullback b).obj M) := by
  let r : ((Over.map b).op ⋙ parabolicPresheaf G hG).RepresentableBy
      ((Over.pullback b).obj M) :=
    { homEquiv := ((Over.mapPullbackAdj b).homEquiv _ M).symm.trans e.homEquiv
      homEquiv_comp := fun a c => by
        dsimp
        rw [(Over.mapPullbackAdj b).homEquiv_naturality_left_symm, e.homEquiv_comp] }
  exact r.ofIso (parabolicPresheafBaseChangeIso b hG).symm

/-- The pulled-back representing equivalence is the original one under the
slice adjunction and the canonical direct/iterated ambient comparison. -/
theorem representableByBaseChange_homEquiv (b : S' ⟶ S) (hG : IsReductive G)
    {M : Over S} (e : (parabolicPresheaf G hG).RepresentableBy M)
    {T : Over S'} (a : T ⟶ (Over.pullback b).obj M) :
    baseChangeEquiv b T ((representableByBaseChange b hG e).homEquiv a) =
      e.homEquiv (((Over.mapPullbackAdj b).homEquiv T M).symm a) := by
  exact (baseChangeEquiv b T).apply_symm_apply _

/-- Smooth proper representability, when supplied, is preserved by arbitrary
change of base. -/
theorem exists_smooth_proper_representation_baseChange
    (b : S' ⟶ S) (hG : IsReductive G) {M : Over S}
    (e : (parabolicPresheaf G hG).RepresentableBy M)
    (hs : Smooth M.hom) (hp : IsProper M.hom) :
    ∃ M' : Over S',
      Nonempty ((parabolicPresheaf ((GroupScheme.baseChange b).obj G)
        (hG.baseChange b)).RepresentableBy M') ∧ Smooth M'.hom ∧ IsProper M'.hom := by
  refine ⟨(Over.pullback b).obj M, ⟨representableByBaseChange b hG e⟩, ?_, ?_⟩
  · exact MorphismProperty.pullback_snd _ _ hs
  · exact MorphismProperty.pullback_snd _ _ hp

end Langlands.GroupScheme.ParabolicSubgroupModuli
