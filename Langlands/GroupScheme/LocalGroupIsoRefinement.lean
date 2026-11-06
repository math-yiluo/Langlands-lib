import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.CocycleRefinement

/-! # Refinement of natural local group isomorphisms and their discrepancy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U V : Over S}

namespace LocalGroupIso

/-- Restrict the local isomorphisms along any morphism of their parameter schemes. -/
def refine (e : LocalGroupIso G H U) (r : V ⟶ U) : LocalGroupIso G H V where
  toFun b := e.toFun (b ≫ r)
  naturality t b g := by
    simpa only [Category.assoc] using e.naturality t (b ≫ r) g

@[simp] theorem refine_toFun (e : LocalGroupIso G H U) (r : V ⟶ U)
    {T : Over S} (b : T ⟶ V) (g : T ⟶ G.X) :
    (e.refine r).toFun b g = e.toFun (b ≫ r) g := rfl

/-- Refinement preserves agreement of the local isomorphisms. -/
theorem IsIndependent.refine {e : LocalGroupIso G H U} (h : e.IsIndependent)
    (r : V ⟶ U) : (e.refine r).IsIndependent := by
  intro T b c g
  exact h (b ≫ r) (c ≫ r) g

/-- Refining both the local isomorphisms and the natural cocycle preserves discrepancy. -/
theorem HasDiscrepancy.refine {e : LocalGroupIso G H U} {a : AutomorphicAction A G}
    {ξ : Cocycle A U} (h : e.HasDiscrepancy a ξ) (r : V ⟶ U) :
    (e.refine r).HasDiscrepancy a (ξ.refine r) := by
  intro T b c g
  exact h (b ≫ r) (c ≫ r) g

end LocalGroupIso

namespace Cocycle

/-- The actual universal overlap value is pulled back by the product refinement. -/
theorem refine_universal (ξ : Cocycle A U) (r : V ⟶ U) :
    (ξ.refine r).toFun (fst V V) (snd V V) =
      (r ⊗ₘ r) ≫ ξ.toFun (fst U U) (snd U U) := by
  change ξ.toFun (fst V V ≫ r) (snd V V ≫ r) = _
  simpa only [tensorHom_fst, tensorHom_snd] using
    ξ.naturality (r ⊗ₘ r) (fst U U) (snd U U)

end Cocycle

end Langlands.GroupScheme
