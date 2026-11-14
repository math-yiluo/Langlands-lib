import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding NormalizedJacquetEquivalenceTheorem NormalizedJacquetSubquotientTheorem
open Langlands.GeneralLinear
universe uF uV uW

/-- The actual normalized Jacquet functor preserves actual subquotients. -/
def NormalizedJacquetSubquotientTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubquotient ((T.normalizedJacquetFunctor B).obj D)
        ((T.normalizedJacquetFunctor B).obj A)

/-- Equivalent ambient representations have equivalent actual normalized
Jacquet modules, even when their carriers lie in different universes. -/
def NormalizedJacquetEquivalenceTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier)),
      Nonempty (A.representation.Equiv D.representation) →
      Nonempty (((T.normalizedJacquetFunctor B).obj A).representation.Equiv
        ((T.normalizedJacquetFunctor B).obj D).representation)

end Langlands.AllFieldBZ.CuspidalSupport
