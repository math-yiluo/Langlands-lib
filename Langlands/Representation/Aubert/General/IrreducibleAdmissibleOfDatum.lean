import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Aubert.General.JacquetCartanDatumStatement
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# Jacquet's theorem for `G(F)` from Jacquet–Cartan data

`Langlands.Aubert.General.rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum`
derives `RationalPointsIrreducibleAdmissibleStatement` from
`RationalPointsJacquetCartanDatumStatement`. It applies the published abstract
theorem `SmoothRep.isAdmissible_of_jacquetCartanDatum` to the datum on `G(F)`,
with the published facts that `G(F)` is a topological group and has a compact
open subgroup.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

universe u uV

/-- Jacquet–Cartan data on every `G(F)` imply that every irreducible smooth
complex representation of every `G(F)` is admissible. -/
theorem rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum
    (h : RationalPointsJacquetCartanDatumStatement.{u}) :
    RationalPointsIrreducibleAdmissibleStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  let : Smooth G.X.hom := hG.smooth
  let : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
  obtain ⟨𝒟⟩ := h F G hG
  intro A hA
  exact SmoothRep.isAdmissible_of_jacquetCartanDatum 𝒟
    (Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup F G) A hA

end Langlands.Aubert.General
