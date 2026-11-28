import Langlands.Automorphic.GroupSchemeArithmeticHarishChandraInduction
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Automorphic.GroupSchemeHarishChandraParabolicReduction
import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof
import Langlands.Global.AdelicLeviCenterRestrictionUniform
import Langlands.Global.AdelicSmoothIwasawaHeight

/-! # Uniform Harish-Chandra equations for parabolic parameter twists -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
open AdelicGroupPoints InfiniteAdelicGroupPoints

private theorem smoothHeightPairings : IwasawaSmoothHeightPairingsStatement.{u} := by
  intro F _ _ G P _ p K hK d hsmooth hG hp hmax
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffine P.X.left := isAffine_of_isAffineHom p.hom.hom.left
  let : Smooth G.X.hom := hsmooth.smooth
  exact adelicSmoothIwasawaHeight F G P p K hK hsmooth hmax

private theorem uniformLeviCenterTransfer_of_finiteRestriction
    (hCenter : ParabolicLeviCenterRestrictionStatement.{u}) :
    UniformParabolicLeviCenterTransferStatement.{u} := by
  intro F _ _ G P U M _ _ p iU l hG hp hu hl hmul d e hsG hcG hsM hcM
  let : IsAffineHom P.X.hom := hl.isAffineHom
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : IsClosedImmersion iU.hom.hom.left := hu.1.isClosedSubgroup
  let : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
  obtain ⟨transfer, _, hCompare⟩ :=
    hCenter F G P M U p iU l hG hp hu hl hmul hsG hsM hcG hcM 1
  refine hasUniformLeviCenterTransfer_of_identity iU l hsG hcG hsM hcM
    adelicEnvelopingCenterConjugation hG ?_
  intro z
  refine ⟨(transfer z).val, fun v hv => ?_⟩
  have hIdentity (w : InfinitePlotSmoothFunctions F G) :
      infiniteLeviRestriction (q := p) l 1 w = infiniteLeviIdentitySlice (p := p) l w := by
    apply Subtype.ext
    funext m
    change w.val (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F (InfiniteAdeleRing F)) m * 1) =
      w.val (M.affinePointsTarget (l ≫ p) (CommAlgCat.of F (InfiniteAdeleRing F)) m)
    rw [mul_one]
  simpa only [hIdentity, plotSmoothCenterAction, AlgHom.comp_apply, Subalgebra.val_apply]
    using (hCompare v hv z).symm

/-- The uniform Harish-Chandra equations on the given parabolic quotient and compact. -/
theorem inducedHarishChandraEquations : InducedHarishChandraEquationsStatement.{u} := by
  have hCenter : ParabolicLeviCenterRestrictionStatement.{u} := parabolicLeviCenterRestriction
  have hArithmetic := arithmeticHarishChandraFiniteness_of_leviCenterRestriction hCenter
  exact inducedHarishChandraEquations_of_parabolicCenter
    (parabolicHarishChandraFiniteness_of_arithmetic_and_center hArithmetic hCenter)
    smoothHeightPairings (uniformLeviCenterTransfer_of_finiteRestriction hCenter)

end Langlands.Global
