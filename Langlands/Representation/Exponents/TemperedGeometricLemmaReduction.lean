import Langlands.Representation.Exponents.LeviUnitaryFiltration
import Langlands.Representation.Exponents.TemperedGeometricPiece
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement

/-! Conditional assembly of the exact tempered geometric-lemma target. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The exact tempered geometric lemma follows from the represented geometric
lemma, root-presentation existence, quotient compactness, and Jacquet
admissibility at both carrier universes used by the construction. -/
def TemperedGeometricLemmaReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    ParabolicRootPresentationExistenceStatement.{u} →
      ArbitraryParabolicQuotientCompactStatement.{u} →
        ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
          ArbitraryParabolicJacquetAdmissibilityStatement.{u, max u v} →
            TemperedGeometricLemmaStatement.{u, v}

/-- Evaluate the supplied geometric gluing, take its unitary filtration, and
identify each selected piece with the induced unitary Jacquet piece. All
structural inputs remain explicit; this is a conditional reduction only. -/
theorem temperedGeometricLemma_of_structuralInputs :
    TemperedGeometricLemmaReductionStatement.{u, v} := by
  intro hgeom hpres hcompact hJ hJI k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ AL aL haL
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro ρ hρ
  obtain ⟨m, c, z, hz, D, hglue⟩ :=
    hgeom k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨presQ⟩ := hpres k G hG Q L AL q lQ aL hq hlQ haL
  let π := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  have hπ : π.IsAdmissible :=
    leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement hcompact hG
      p l r hp hl hr hmul ρ hρ.isAdmissible
  have hJacπ := hJI k G hG Q L U q lQ rQ hq hlQ hrQ hmulQ π hπ
  have hLeviJacπ : IsAdmissible
      ((leviJacquetInductionFunctor p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π).representation
      (leviPointsEquiv q lQ hq hlQ) hJacπ
  refine ⟨m, c, z, hz, D, ?_⟩
  intro A' a' ha'
  obtain ⟨s, e, hs⟩ := exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ haL
    (fun i => (D i).pieceFunctor) hglue ρ hLeviJacπ
  refine ⟨s, e, fun j => ?_⟩
  have hJacρ := hJ k M hl.isConnectedReductive
    (D (e j)).P' (D (e j)).M' (D (e j)).N'
    (D (e j)).p' (D (e j)).l' (D (e j)).r'
    (D (e j)).hp' (D (e j)).hl' (D (e j)).hr' (D (e j)).hmul' ρ hρ.isAdmissible
  obtain ⟨f⟩ := hs j
  obtain ⟨g⟩ := (D (e j)).nonempty_selectedWeightPart_pieceFunctor_equiv
    hcompact haL presQ (ha' (e j)) ρ hρ hJacρ
  exact ⟨f.trans g⟩

end Langlands.Aubert.General.RepresentedParabolic
