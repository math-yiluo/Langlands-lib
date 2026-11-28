import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesInjectivity
import Langlands.GroupScheme.Rational.NumberFieldCocycleCoverDescent
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple

/-! # Local triviality of finite field cocycles from the real places -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}

/-- Triviality after pullback of the whole cover at every real place. -/
def RealLocallyTrivial (ξ : Cocycle G U) : Prop :=
  ∀ w : InfinitePlace F, w.IsReal →
    (ξ.baseChangePullback (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial

/-- Local triviality at the real places is preserved by coefficient maps. -/
theorem RealLocallyTrivial.map {ξ : Cocycle G U} (h : ξ.RealLocallyTrivial) (q : G ⟶ H) :
    (ξ.map q).RealLocallyTrivial := by
  intro w hw
  let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
  obtain ⟨f, hf⟩ := (h w hw).map ((GroupScheme.baseChange b).map q)
  refine ⟨f, fun a c => ?_⟩
  change ((ξ.map q).baseChange b _ ((Over.mapPullbackAdj b).counit.app U)).toFun a c = _
  rw [baseChange_map_toFun]
  exact hf a c

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L]

/-- The nonarchimedean and complex vanishing theorems supply the missing
local trivializations for a simply connected coefficient group. -/
theorem RealLocallyTrivial.locallyTrivial_of_isSimplyConnected
    {ξ : Cocycle G (GaloisCocycle.cover F L)} (h : ξ.RealLocallyTrivial)
    (hG : IsSimplyConnected G) : ξ.LocallyTrivial := by
  let V := GaloisCocycle.cover F L
  let ζ := coboundary (1 : V ⟶ G.X)
  have hz : ζ.IsTrivial := ⟨1, fun _ _ => rfl⟩
  have hc : ζ.LocallyCohomologous ξ := by
    apply simplyConnectedRealToAllPlacesComparison F G hG L ζ ξ
    intro w hw
    let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
    let r := (Over.mapPullbackAdj b).counit.app V
    obtain ⟨g, hg⟩ := hz.baseChange b _ r
    obtain ⟨f, hf⟩ := h w hw
    refine ⟨g * f⁻¹, fun a c => ?_⟩
    change (ξ.baseChangePullback b).toFun a c =
      ((ζ.baseChangePullback b).twist (g * f⁻¹)).toFun a c
    rw [hf a c]
    change (a ≫ f) * (c ≫ f)⁻¹ = (a ≫ (g * f⁻¹))⁻¹ *
      (ζ.baseChange b _ r).toFun a c * (c ≫ (g * f⁻¹))
    rw [hg a c]
    simp only [MonObj.comp_mul, GrpObj.comp_inv]
    group
  intro v
  let b := algebraBaseMap F (Global.placeCompletion F v)
  exact IsTrivial.of_cohomologous (hc v) (hz.baseChange b _ ((Over.mapPullbackAdj b).counit.app V))

end Langlands.GroupScheme.Cocycle
