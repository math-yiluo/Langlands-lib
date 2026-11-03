import Langlands.BruhatTits.Cartan.CentralizerValuationConsequences

/-! # Restriction of the normalized centralizer valuation to the actual torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual torus-point restriction of the positive normalized valuation. -/
def torusValuationRestriction (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    rationalPoints S.toGrp →* Multiplicative (RealTorusSpace.V S) :=
  (centralizerValuation s h).comp (rationalPoints.map s)

/-- Evaluating the restricted valuation uses the order of the pulled-back character. -/
theorem torusValuationRestriction_spec (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s))
    (t : rationalPoints S.toGrp) (χ : rationalCharacters Z) :
    RealTorusSpace.eval S (characterRestriction s χ) (torusValuationRestriction s h t).toAdd =
      ((rationalCharacterValuation S.toGrp t).toAdd (characterRestrict s χ) : ℝ) := by
  change RealTorusSpace.eval S (characterRestriction s χ)
    (centralizerValuation s h (rationalPoints.map s t)).toAdd = _
  rw [centralizerValuation_spec, rationalCharacterValuation_characterRestrict]

/-- If the torus's own restriction-evaluation comparison is supplied, the
centralizer valuation restricts to that same normalized torus valuation. -/
theorem torusValuationRestriction_eq_id (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s))
    (hS : Function.Bijective (restrictionEvaluation (𝟙 S.toGrp))) :
    torusValuationRestriction s h = centralizerValuation (𝟙 S.toGrp) hS := by
  apply MonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  symm
  apply (eq_centralizerValuation_iff s h (rationalPoints.map s t) _).mpr
  intro χ
  have ht := centralizerValuation_spec (𝟙 S.toGrp) hS t (characterRestrict s χ)
  simpa [characterRestriction, characterRestrict] using
    ht.trans (congrArg (fun n : ℤ => (n : ℝ))
      (rationalCharacterValuation_characterRestrict s χ t))

section CoordinateSplitTorus

variable (F) (I : Type u) [Finite I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I

/-- On the actual coordinate split torus, restriction is the published positive
torus valuation, without an additional identity-comparison argument. -/
theorem torusValuationRestriction_eq_split (s : (𝕋).toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    torusValuationRestriction s h = SplitTorusValuation.realValuation F I := by
  apply MonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  symm
  apply (eq_centralizerValuation_iff s h (rationalPoints.map s t) _).mpr
  intro χ
  rw [SplitTorusValuation.eval_realValuation]
  simpa [characterRestriction] using
    congrArg (fun n : ℤ => (n : ℝ))
      (rationalCharacterValuation_characterRestrict s χ t)

/-- The restricted valuation sends an actual uniformizer cocharacter value to
its positive embedded cocharacter. -/
theorem torusValuationRestriction_uniformizer (s : (𝕋).toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (c : cocharacterLattice 𝕋) :
    (torusValuationRestriction s h
      (SplitTorusValuation.cocharacterPoints F I c
        (SplitTorusValuation.uniformizerUnit F))).toAdd = (1 : ℝ) ⊗ₜ[ℤ] c := by
  rw [torusValuationRestriction_eq_split]
  exact SplitTorusValuation.realValuation_cocharacterPoints_uniformizer F I c

end CoordinateSplitTorus

end Langlands.BruhatTits.Cartan
