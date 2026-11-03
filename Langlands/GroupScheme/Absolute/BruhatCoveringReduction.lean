import Langlands.GroupScheme.Absolute.BruhatCoveringSteps
import Langlands.GroupScheme.Dynamic.ProperAffineExtension
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.Dynamic.BruhatCellLimit

/-! # Reduction of the absolute Bruhat covering to structure-theory statements -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The structure-theory statements from which the absolute Bruhat covering is derived. -/
def BruhatCoveringPrerequisites : Prop :=
  TorusFiniteGaloisSplittingStatement.{u} ∧ RegularCocharacterBorelStatement.{u} ∧
    GenericCentralizerStatement.{u} ∧ MaximalTorusCentralizerStatement.{u} ∧
    ParabolicSubgroupQuotientProperStatement.{u} ∧
    CentralizerBorelIntersectionStatement.{u} ∧ SolvableMaximalTorusConjugacyStatement.{u}

/-- The structure-theory prerequisites imply the absolute Bruhat covering for every Borel pair
of a connected reductive group over an algebraically closed field. -/
theorem absoluteBruhatCovering_of_prerequisites (h : BruhatCoveringPrerequisites.{u}) :
    AbsoluteBruhatCoveringStatement.{u} := by
  intro k _ _ G hG B T i j hij g
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  obtain ⟨hsplit, hreg, hgen, hcent, hproper, hcbi, hsolv⟩ := h
  obtain ⟨ν, hP, hZ⟩ := BruhatCovering.exists_cocharacter hsplit hreg hgen hcent hG hij
  obtain ⟨Q, q, hsep, hprop, hsm, hsurj, hqc, hfib⟩ :=
    BruhatCovering.exists_proper_quotient hproper hij.1
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range i) q hfib
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q :=
    fun _ g h => Dynamic.flagQuotientSchemeAction_act_lift G _ q hfib g h
  -- The orbit `t ↦ λ(t) · gB` extends over the affine line since `G/B` is proper.
  obtain ⟨e, he⟩ :=
    AffineLine.exists_extension_of_isProper Q ((a.restrict (ν ≫ j)).gmOrbit (g ≫ q))
  -- Its value at `0` is a fixed point, the coset of a point normalizing the torus.
  obtain ⟨n, hn, hnq⟩ := BruhatCovering.exists_normalizerPoint_of_isFixed hcbi hsolv hij
    (ν ≫ j) hZ q hfib a hact _ (SchemeAction.IsGmOrbitExtension.isFixed_evalZero _ he)
  -- The opposite cell at that point places `g` in `B n B`.
  obtain ⟨b₁, b₂, hg⟩ := Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints
    i j q a hact hfib ν hP n g hn he hnq.symm
  exact ⟨b₁, b₂, ⟨n, hn⟩, hg⟩

end Langlands.GroupScheme
