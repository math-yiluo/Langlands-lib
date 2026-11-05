import Langlands.Sheaf.Renard.BasisSheaf
import Langlands.CategoryTheory.RenardAbelian

/-!
# Renard A.VI.1: basis-sheaf abelianness at a sufficient section universe

These two proposition definitions concern the actual normalized basis-sheaf
category. The independent parameters are `u` and `v`; section carriers lie in
`Type (max u v)`. The space, its supplied topology and its chosen basis are
universally quantified. No proof of either proposition is supplied here.
-/

universe u v

namespace Langlands.Sheaf.Renard

/-- The actual basis-sheaf category admits Mathlib's abelian structure, with
section carriers in the sufficient universe `max u v`. -/
def BasisSheafAbelianStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (B : OpenBasis X),
    Nonempty (CategoryTheory.Abelian (BasisSheaf.{u,max u v} B))

/-- The same actual basis-sheaf category satisfies Renard's existing seven
abelian-category axioms, at the same sufficient section universe. -/
def BasisSheafAbelianAxiomsStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (B : OpenBasis X),
    Langlands.Renard.AbelianAxioms (BasisSheaf.{u,max u v} B)

end Langlands.Sheaf.Renard
