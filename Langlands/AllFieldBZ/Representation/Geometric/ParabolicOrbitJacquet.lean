import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Geometric.ParabolicOrbitJacquet

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitJacquet`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitJacquet` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic
universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ} (B : GeneralLinear.BlockShape n)

end Langlands.AllFieldBZ.Parabolic
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
universe uR uG uF uV

section RawOrbit
variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

end RawOrbit
open Langlands.GeneralLinear
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The actual compact orbit piece for normalized parabolic induction, followed
by normalized radical coinvariants for the target parabolic. The orbit is
`P_B * w⁻¹ * P_C`, so the stabilizer representation uses conjugation by `w⁻¹`. -/
def parabolicOrbitJacquetFunctor (w : Equiv.Perm (Fin n)) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      Rep.{max uF uV} ℂ (C.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.inducingFunctor (T.leviHalfCharacter B) ⋙
    rawOrbitPiece (B.parabolic F.Carrier) (C.parabolic F.Carrier)
      (permutation n F.Carrier w) ⋙
    Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)

end Langlands.AllFieldBZ.Geometric
