import Langlands.GroupScheme.SplitExistence.Assembly
import Langlands.GroupScheme.SplitExistence.ToChevalleyData
import Langlands.GroupScheme.SplitExistence.IntegralBase
import Langlands.GroupScheme.SplitExistence.ChevalleyLieExistence

/-! # The Existence Theorem for split reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open SplitExistence in
/-- The Existence Theorem from the existence of integral Chevalley data with Lie relations for
every base of every reduced root datum. -/
theorem splitReductiveExistence_of_nonempty
    (H : ∀ (J X Y : Type u) [Finite J] [AddCommGroup X] [AddCommGroup Y] [Module.Finite ℤ X]
      (P : RootDatum J X Y) [P.IsReduced] (b : P.Base), Nonempty (ChevalleyLieData P b)) :
    SplitReductiveExistenceStatement.{u} := by
  intro k _ J X Y _ _ _ _ P hP
  obtain ⟨b⟩ := nonempty_base_int P
  obtain ⟨D⟩ := H J X Y P b
  exact ChevalleyData.exists_split_of_chevalleyData k D.toChevalleyData

open SplitExistence in
/-- **The Existence Theorem for split reductive groups**: for every field `k`, every reduced root
datum indexed by a finite type, on a finitely generated lattice, is isomorphic to the root datum
of a split maximal torus of a connected reductive group over `k`. -/
theorem splitReductiveExistence : SplitReductiveExistenceStatement.{u} :=
  splitReductiveExistence_of_nonempty fun _ _ _ _ _ _ _ P _ b => nonempty_chevalleyLieData P b

end Langlands.GroupScheme
