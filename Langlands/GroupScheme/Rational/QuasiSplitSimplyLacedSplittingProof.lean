import Langlands.GroupScheme.Rational.QuasiSplitSimplyLacedSplittingStatement
import Langlands.GroupScheme.Rational.FullRelativeRootPairing
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction

/-! # Quasi-split groups with reduced simply-laced relative roots split -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A quasi-split absolutely almost-simple group whose full relative root
system is reduced and simply laced has each such maximal split torus already
maximal among all tori. -/
theorem quasiSplitSimplyLacedSplitting : QuasiSplitSimplyLacedSplittingStatement.{u} := by
  apply quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  intro hne J P _ hP
  exact isIrreducible_fullRelativeRootPairing i P hP hG hi hne

end Langlands.GroupScheme
