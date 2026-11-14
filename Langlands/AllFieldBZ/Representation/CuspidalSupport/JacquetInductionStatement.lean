import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.JacquetInductionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.JacquetInductionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) (n : ℕ)

/-- For nonassociated Levis, the normalized Jacquet module of quasicuspidal
induction has no nonzero quasicuspidal subquotient. -/
def NonassociatedJacquetSubquotientsTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    ¬ LevisAssociated (F := F.Carrier) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier),
      SmoothRep.IsSubquotient D A → IsLeviQuasicuspidal C D.representation →
      Subsingleton D

/-- For associated Levis, the actual Jacquet module has one successive
quotient for each minimal conjugating permutation, equal up to actual
representation equivalence to the corresponding Weyl transport. -/
def AssociatedJacquetFiltrationTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsLeviQuasicuspidal B ρ.representation →
    LevisAssociated (F := F.Carrier) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    IsLeviQuasicuspidal C A.representation ∧
    ∃ (r : ℕ) (e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B C)
      (s : ObjectRepFiltration (Rep.of A.representation) r),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport B C (e i).val.val (e i).property ρ.representation))

end Langlands.AllFieldBZ.CuspidalSupport
