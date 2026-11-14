import Langlands.GroupScheme.Rational.FullRelativeRootPairing
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement

/-! # Irreducibility of the actual relative root system -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual relative root system of an almost-simple group is irreducible. -/
theorem relativeRootSystemIrreducible : RelativeRootSystemIrreducibleStatement.{u} := by
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  intro hne J P _ hP
  exact isIrreducible_fullRelativeRootPairing i P hP hG hi hne

end Langlands.GroupScheme
