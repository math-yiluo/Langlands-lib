import Langlands.BruhatTits.Cartan.CentralizerValuation
import Langlands.Geometry.Building.SplitTorusValuation

/-! # Intrinsic image and kernel comparisons for the normalized valuation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- Transport by the inverse comparison does not change the actual norm kernel.
For an actual centralizer this is `Z(F)^1`, not the parahoric kernel `Z(F)^0`. -/
theorem centralizerValuation_ker (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    (centralizerValuation s h).ker = rationalCommonNormKernel Z := by
  rw [centralizerValuation, MonoidHom.ker_comp_of_injective _ _
    (LinearEquiv.ofBijective (restrictionEvaluation s) h).symm.injective,
    rationalNormLogarithm_ker]

/-- The quotient by the actual common norm kernel is the actual real valuation image. -/
def centralizerValuationQuotientEquiv (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    (rationalPoints Z ⧸ rationalCommonNormKernel Z) ≃* centralizerValuationImage s h :=
  (QuotientGroup.quotientMulEquivOfEq (centralizerValuation_ker s h).symm).trans
    (QuotientGroup.quotientKerEquivRange (centralizerValuation s h))

@[simp] theorem centralizerValuationQuotientEquiv_mk (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (z : rationalPoints Z) :
    centralizerValuationQuotientEquiv s h (QuotientGroup.mk z) =
      ⟨centralizerValuation s h z, z, rfl⟩ := rfl

/-- The actual real image and actual integer-character image have the same
canonical quotient source. No full cocharacter-lattice assertion is made. -/
def centralizerValuationImageEquiv (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) :
    centralizerValuationImage s h ≃* rationalCharacterValuationImage Z :=
  (centralizerValuationQuotientEquiv s h).symm.trans (rationalNormKernelQuotientEquiv Z)

@[simp] theorem centralizerValuationImageEquiv_apply (s : S.toGrp ⟶ Z)
    (h : Function.Bijective (restrictionEvaluation s)) (z : rationalPoints Z) :
    centralizerValuationImageEquiv s h ⟨centralizerValuation s h z, z, rfl⟩ =
      ⟨rationalCharacterValuation Z z, z, rfl⟩ := by
  rw [← centralizerValuationQuotientEquiv_mk s h z]
  change rationalNormKernelQuotientEquiv Z
    ((centralizerValuationQuotientEquiv s h).symm
      (centralizerValuationQuotientEquiv s h (QuotientGroup.mk z))) = _
  rw [MulEquiv.symm_apply_apply, rationalNormKernelQuotientEquiv_mk]

section Split

variable (F) (I : Type u) [Finite I]

local notation "𝕋" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I

/-- In the coordinate split-torus case the character normalization agrees with
the published positive split-torus valuation. -/
theorem centralizerValuation_id_eq_split
    (h : Function.Bijective (restrictionEvaluation (𝟙 (𝕋).toGrp))) :
    centralizerValuation (𝟙 (𝕋).toGrp) h = SplitTorusValuation.realValuation F I := by
  apply MonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  symm
  apply (eq_centralizerValuation_iff _ h t _).mpr
  intro χ
  simpa [characterRestriction, characterRestrict] using
    SplitTorusValuation.eval_realValuation F I
      (rationalCharacters.equivCharacterLattice 𝕋 χ) t

end Split

end Langlands.BruhatTits.Cartan
