import Langlands.GroupScheme.Reductive.AffinePinnedBorelTorusNormalization
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonPullback
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Simultaneous local Borel and torus normalization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T U V : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Pull an actual group section back to the normalized direct pullback. -/
def pullBasePoint (N : AffinePinnedModel.{u}) (g : T ⟶ N.base)
    (q : U ⟶ T) (c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X) :
    Over.mk (𝟙 U) ⟶ (N.groupOver (q ≫ g)).X :=
  baseChangeBasePoint q (N.groupOver g) c ≫
    (baseChangeCompIso g q N.group).inv.hom.hom

/-- Normalized comparison pullback carries an inner automorphism to the
inner automorphism of the normalized pulled-back section. -/
theorem pullComparison_inner (N : AffinePinnedModel.{u}) (g : T ⟶ N.base)
    (q : U ⟶ T) (c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X) :
    pullComparison ((N.groupOver g).innerIso c) q =
      (N.groupOver (q ≫ g)).innerIso (N.pullBasePoint g q c) := by
  apply Iso.ext
  simp only [pullComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    baseChange_innerIso_hom]
  rw [innerIso_hom_comp, Iso.hom_inv_id_assoc]
  rfl

/-- A target group section simultaneously corrects the Borel and torus squares. -/
def HasBorelTorusCorrection (e : Comparison f g) : Prop :=
  ∃ c : Over.mk (𝟙 T) ⟶ (N.groupOver g).X,
    let d := e ≪≫ (N.groupOver g).innerIso c
    PreservesBorel d ∧ PreservesTorus d

private theorem correction_pullAlong_iff (e : Comparison f g) (q : U ⟶ T)
    {f' : U ⟶ M.base} {g' : U ⟶ N.base}
    (hf : q ≫ f = f') (hg : q ≫ g = g') :
    HasBorelTorusCorrection (pullComparisonAlong e q hf hg) ↔
      HasBorelTorusCorrection (pullComparison e q) := by
  subst f'
  subst g'
  rw [pullComparisonAlong_rfl]

/-- The existence of a simultaneous correction respects the actual
direct-versus-iterated pullback identification. -/
theorem correction_pullComparison_comp_iff (e : Comparison f g)
    (q : U ⟶ T) (r : V ⟶ U) :
    HasBorelTorusCorrection (pullComparison (pullComparison e q) r) ↔
      HasBorelTorusCorrection (pullComparison e (r ≫ q)) := by
  rw [← correction_pullAlong_iff (pullComparison e q) r
    (Category.assoc r q f).symm (Category.assoc r q g).symm,
    ← pullComparisonAlong_rfl e q, pullComparisonAlong_comp,
    pullComparisonAlong_rfl]

/-- Simultaneous normalization by actual target sections on an etale cover. -/
def HasEtaleBorelTorusNormalization (e : Comparison f g) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T,
    ∀ j, HasBorelTorusCorrection (pullComparison e (𝒰.f j))

/-- First align the Borels, then align their coordinate tori inside the target
Borel; compose the covers and multiply the actual conjugating sections. -/
theorem hasEtaleBorelTorusNormalization (e : Comparison f g) :
    HasEtaleBorelTorusNormalization e := by
  obtain ⟨𝒰, h𝒰⟩ := hasEtaleBorelNormalization e
  choose c hc using h𝒰
  choose 𝒱 h𝒱 using fun j =>
    hasEtaleBorelTorusRefinement
      (pullComparison e (𝒰.f j) ≪≫ (N.groupOver (𝒰.f j ≫ g)).innerIso (c j))
      (hc j)
  refine ⟨𝒰.bind 𝒱, fun ⟨j, k⟩ => ?_⟩
  apply (correction_pullComparison_comp_iff e (𝒰.f j) ((𝒱 j).f k)).mp
  obtain ⟨b, hb⟩ := h𝒱 j k
  let r := (𝒱 j).f k
  let c' := N.pullBasePoint (𝒰.f j ≫ g) r (c j)
  let b' := b ≫ (N.borelInclusionOver (r ≫ (𝒰.f j ≫ g))).hom.hom
  refine ⟨b' * c', ?_⟩
  have hi : (N.groupOver (r ≫ (𝒰.f j ≫ g))).innerIso (b' * c') =
      (N.groupOver (r ≫ (𝒰.f j ≫ g))).innerIso c' ≪≫
        (N.groupOver (r ≫ (𝒰.f j ≫ g))).innerIso b' :=
    Iso.ext (innerIso_mul_hom _ _ _)
  dsimp only at hb
  rw [pullComparison_trans, pullComparison_inner] at hb
  dsimp only
  rw [hi]
  simpa only [Iso.trans_assoc] using hb

end Langlands.GroupScheme.AffinePinnedModel
