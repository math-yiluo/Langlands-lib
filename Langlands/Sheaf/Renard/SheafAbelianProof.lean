import Langlands.Sheaf.Renard.SheafAbelianStatements
import Langlands.Sheaf.Renard.BasisMathlibSheafEquivalence
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Renard A.VI.1: proof of basis-sheaf abelianness at a sufficient section universe

The actual basis-sheaf category is transported along the published equivalence
with Mathlib's sheaves on all opens, which are abelian at section universe
`max u v`.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Langlands.Sheaf.Renard

/-- Forgetting `AddCommGrpCat.{max u v}` preserves filtered colimits indexed in `u`. -/
local instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
  preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max u v})

/-- Abelian structure on the actual basis-sheaf category, transported from
Mathlib's abelian sheaves on all opens along the published equivalence. -/
@[instance_reducible]
noncomputable def basisSheafAbelian (X : Type u) [TopologicalSpace X] (B : OpenBasis X) :
    Abelian (BasisSheaf.{u,max u v} B) :=
  have : HasFiniteProducts (BasisSheaf.{u,max u v} B) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
      (BasisMathlib.equivalence.{u,v} B).functor⟩
  abelianOfEquivalence (BasisMathlib.equivalence.{u,v} B).functor

/-- Renard A.VI.1 for basis sheaves, at section universe `max u v`. -/
theorem basisSheafAbelianStatement : BasisSheafAbelianStatement.{u,v} :=
  fun X _ B => ⟨basisSheafAbelian.{u,v} X B⟩

/-- The same assertion in the published seven-axiom interface. -/
theorem basisSheafAbelianAxiomsStatement : BasisSheafAbelianAxiomsStatement.{u,v} :=
  fun X _ B => (Langlands.Renard.abelianAxioms_iff_nonempty_abelian _).2
    (basisSheafAbelianStatement.{u,v} X B)

end Langlands.Sheaf.Renard
