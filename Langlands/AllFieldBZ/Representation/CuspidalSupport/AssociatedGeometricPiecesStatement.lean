import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem MinimalWeylTransportQuasicuspidalTheorem PadicAssociatedGeometricPiecesTheorem
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) (n : ℕ)

/-- For associated Levis, a nonconjugating minimal representative gives a zero
actual geometric piece on every smooth quasicuspidal input. -/
def AssociatedGeometricPieceVanishingTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    LevisAssociated (F := F.Carrier) B C →
    ∀ (w : MinimalRepresentatives B C)
      (S : BlockRefinement B) (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R),
      ¬ ConjugatesLevi (F := F.Carrier) B C w.val →
      Subsingleton ((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1).obj ρ)

/-- For associated Levis, a conjugating minimal representative gives the
actual whole-Levi Weyl transport, up to a representation equivalence. -/
def AssociatedGeometricPieceEquivalenceTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    LevisAssociated (F := F.Carrier) B C →
    ∀ (w : MinimalRepresentatives B C)
      (S : BlockRefinement B) (R : BlockRefinement C)
      (hS : IsIntersectionRefinement (F := F.Carrier) B C w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ R)
      (hw : ConjugatesLevi (F := F.Carrier) B C w.val),
      Nonempty (((Langlands.AllFieldBZ.Geometric.geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1).obj ρ).ρ.Equiv
        (transport B C w.val hw ρ.representation))

/-- Quasicuspidality of whole-Levi transport for a conjugating minimal
representative, independently of any intersection refinements or factors. -/
def MinimalWeylTransportQuasicuspidalTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    ∀ (w : MinimalRepresentatives B C)
      (hw : ConjugatesLevi (F := F.Carrier) B C w.val),
      IsLeviQuasicuspidal C (transport B C w.val hw ρ.representation)

/-- The individual-piece reduction used in BZ77 2.13(c), over all finite
p-adic extensions and positive ranks, with independent carrier universe. -/
def PadicAssociatedGeometricPiecesTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n →
      AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n ∧
      AssociatedGeometricPieceEquivalenceTheorem.{uF, uV} F T n ∧
      MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n

end Langlands.AllFieldBZ.CuspidalSupport
