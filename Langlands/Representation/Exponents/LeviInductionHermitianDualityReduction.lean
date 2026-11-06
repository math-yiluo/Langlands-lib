import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.Representation.Aubert.General.NormalizedInductionHermitianDuality
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Exponents.ParabolicPresentationUnitarity
import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Unitary.Restriction

/-! # Hermitian duality for represented parabolic induction

Renard IV.2.1.2 with IV.2.1, Remark 1, in the form `LeviInductionHermitianDualityStatement`
used by VII.1.3. The generic `normalizedInduction_hermitianDuality` applies to the literal
point images of a represented parabolic once compactness of `P(F) \ G(F)`, unimodularity of
rational points of connected reductive groups, and the existence of parabolic root
presentations are supplied. The last two give the modular-character identity of V.5.4 for
`P(F)` through `modularCharacter_of_presentation`. The Levi-point side is transported along
`leviPointsEquiv`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- `LeviInductionHermitianDualityStatement` follows from compactness of the parabolic
quotients, unimodularity of rational points of connected reductive groups (which takes the
standard-cocharacter statement as an argument), and the existence of parabolic root
presentations. -/
theorem leviInductionHermitianDuality_of_presentation
    (hC : ArbitraryParabolicQuotientCompactStatement.{u})
    (hUnimod : RationalPointFamily.RationalReductiveUnimodularityStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hPres : ParabolicRootPresentationExistenceStatement.{u}) :
    LeviInductionHermitianDualityStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro σ hσ hσu χ χ' hχ hχ' hconj W hW hWu hWn
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : T2Space (rationalPoints M) := rationalPoint_t2Space k M
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hl.isConnectedReductive).1
  obtain ⟨pres⟩ := hPres k G hG P M A p l a hp hl ha
  let : MeasurableSpace (rationalPoints G) := borel _
  have : BorelSpace (rationalPoints G) := ⟨rfl⟩
  let : LocallyCompactSpace (pointImage p) :=
    (isClosed_pointImage p hp.isClosedSubgroup).locallyCompactSpace
  have : CompactSpace (Induction.LeftQuotient (pointImage p)) := hC k G hG P p hp
  let e := leviPointsEquiv p l hp hl
  let χ₀ : pointImage (l ≫ p) →* ℂˣ := χ.comp e.symm.toMonoidHom
  let χ₀' : pointImage (l ≫ p) →* ℂˣ := χ'.comp e.symm.toMonoidHom
  have hχ₀ : IsOpen (χ₀.ker : Set (pointImage (l ≫ p))) := hχ.preimage e.symm.continuous
  have hχ₀' : IsOpen (χ₀'.ker : Set (pointImage (l ≫ p))) := hχ'.preimage e.symm.continuous
  obtain ⟨b⟩ := hσu
  exact normalizedInduction_hermitianDuality
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (hUnimod k G hG hStandard)
    (modularCharacter_of_presentation hG p l r hp hl hr hmul pres
      (hUnimod k M hl.isConnectedReductive hStandard))
    (SmoothRep.pullback e.symm σ)
    (isAdmissible_comp_continuousMulEquiv σ.representation e.symm hσ)
    ⟨b.comp e.symm.toMonoidHom⟩ χ₀ χ₀' hχ₀ hχ₀' (fun m => hconj (e.symm m)) W hW hWu hWn

end Langlands.Aubert.General.RepresentedParabolic
