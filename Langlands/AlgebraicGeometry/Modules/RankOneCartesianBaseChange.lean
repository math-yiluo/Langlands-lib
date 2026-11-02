import Langlands.AlgebraicGeometry.Modules.RankOneStalkReflection

/-! # Rank-one loci under arbitrary cartesian base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {P Y T S : Scheme.{u}} {a : P ⟶ Y} {p : P ⟶ T}
  {f : Y ⟶ S} {g : T ⟶ S}

/-- A rank-one stalk of a cartesian pullback reflects to the original stalk
for a locally finitely presented, relatively flat module. -/
def stalkRankOneEquivOfCartesianPullback (H : IsPullback a p f g)
    [LocallyOfFinitePresentation f] (M : Y.Modules) [M.IsFinitePresentation]
    (hM : IsFlatOver f M) (x : P)
    (e : stalk ((Scheme.Modules.pullback a).obj M) x ≃ₗ[P.presheaf.stalk x]
      P.presheaf.stalk x) :
    stalk M (a x) ≃ₗ[Y.presheaf.stalk (a x)] Y.presheaf.stalk (a x) := by
  let r := S.fromSpecResidueField (f (a x))
  let t := pullback.fst g r
  let b := pullback.snd g r
  let aX := pullback.fst p t
  let bX := pullback.snd p t ≫ b
  have HT : IsPullback t b g r := .of_hasPullback g r
  have HP : IsPullback aX (pullback.snd p t) p t := .of_hasPullback p t
  have HX : IsPullback aX bX (a ≫ f) r := by
    rw [H.w]
    exact HP.paste_vert HT
  have HY := IsPullback.of_hasPullback f r
  let fs := HY.lift (aX ≫ a) bX (by rw [Category.assoc, HX.w])
  have HF : IsPullback fs (pullback.snd p t) (pullback.snd f r) b := by
    apply IsPullback.of_right' (t := HY)
    rw [← HT.w]
    exact HP.paste_horiz H
  have : Flat b := inferInstance
  have : Flat fs := MorphismProperty.of_isPullback HF.flip inferInstance
  exact stalkRankOneEquivOfFiberwiseFlatPullback a f M hM x HX HY fs
    (HY.lift_fst _ _ _) (HY.lift_snd _ _ _) e

/-- The actual rank-one locus of a locally finitely presented, relatively flat
module commutes with every cartesian base change. -/
lemma rankOneLocus_pullback_of_isPullback (H : IsPullback a p f g)
    [LocallyOfFinitePresentation f] (M : Y.Modules) [M.IsFinitePresentation]
    (hM : IsFlatOver f M) :
    Picard.rankOneLocus ((Scheme.Modules.pullback a).obj M) =
      a ⁻¹ᵁ Picard.rankOneLocus M := by
  apply le_antisymm
  · intro x hx
    exact mem_rankOneLocus_of_stalkEquiv M (a x)
      (stalkRankOneEquivOfCartesianPullback H M hM x
        (stalkRankOneEquivOfMem _ x hx))
  · exact Picard.preimage_rankOneLocus_le a M

end Langlands.AlgebraicGeometry.Modules
