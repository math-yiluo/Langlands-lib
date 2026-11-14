import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
/-! BZ77 section 2.13: Jacquet modules of quasicuspidal induction. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) (n : ℕ)

/-- For nonassociated Levis, the normalized Jacquet module of quasicuspidal
induction has no nonzero quasicuspidal subquotient. -/
def NonassociatedJacquetSubquotientsTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
    IsLeviQuasicuspidal B ρ.representation →
    ¬ LevisAssociated (F := F) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    ∀ D : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F),
      SmoothRep.IsSubquotient D A → IsLeviQuasicuspidal C D.representation →
      Subsingleton D

/-- For associated Levis, the actual Jacquet module has one successive
quotient for each minimal conjugating permutation, equal up to actual
representation equivalence to the corresponding Weyl transport. -/
def AssociatedJacquetFiltrationTheorem : Prop :=
  letI := T.topology
  ∀ (B C : BlockShape n) (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
    IsLeviQuasicuspidal B ρ.representation →
    LevisAssociated (F := F) B C →
    let A := (T.normalizedJacquetFunctor C).obj
      ((T.normalizedParabolicInductionFunctor B).obj ρ)
    IsLeviQuasicuspidal C A.representation ∧
    ∃ (r : ℕ) (e : Fin r ≃ MinimalConjugatingPermutations (F := F) B C)
      (s : ObjectRepFiltration (Rep.of A.representation) r),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport B C (e i).val.val (e i).property ρ.representation))

end Langlands.AllField.CuspidalSupport
