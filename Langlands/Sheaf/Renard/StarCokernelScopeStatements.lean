import Langlands.Sheaf.Renard.StarDiagram
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Internal star-sheaf cokernel and section-universe targets

These proposition definitions use the actual published star diagram. They are
internal size-scope statements, with exact proofs left to a separate successor.
The canonical zero morphisms come from the existing pointwise preadditive
structure; no abelian structure or cokernel-existence instance is assumed.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Langlands.Sheaf.Renard.StarDiagram

section CanonicalZero

variable {I : Type u}

local instance : TopologicalSpace (Option I) := topology I

/-- The canonical zero sheaf morphism has the actual zero group homomorphism
as every component. -/
@[simp] theorem sheafHomEquiv_zero_app
    (H K : BasisSheaf.{u,v} (allOpenBasis (Option I))) (V : StarOpen I) :
    (sheafHomEquiv H K (0 : H ⟶ K)).app (op V) = 0 := rfl

/-- The published component law also gives zero in the canonical source
category's zero-morphism notation. -/
theorem f_comp_gi_eq_zero (i : I) : f.{u,v} (I := I) ≫ gi.{u,v} i = 0 := by
  apply (sheafHomEquiv _ _).injective
  apply NatTrans.ext
  funext V
  exact f_gi_component_zero i V.unop

end CanonicalZero

/-- Every actual colimit cokernel cofork yields an injection of the leaf
indices into its actual whole-space section carrier, at independent u and v. -/
def CokernelSectionInjectionStatement : Prop :=
  ∀ (I : Type u),
    letI : TopologicalSpace (Option I) := topology I
    ∀ (c : CokernelCofork (f.{u,v} (I := I))),
      IsColimit c → Nonempty (I ↪ Sections c.pt.obj.obj (whole I))

/-- The actual star map on I = Type v has no categorical cokernel when its
section carriers are required to remain in Type v. -/
def UndersizedNoCokernelStatement : Prop :=
  letI : TopologicalSpace (Option (Type v)) := topology (Type v)
  ¬ HasCokernel (f.{v + 1,v} (I := Type v))

/-- The actual basis-sheaf category for this undersized specialization admits
no Mathlib abelian structure. -/
def UndersizedNotAbelianStatement : Prop :=
  letI : TopologicalSpace (Option (Type v)) := topology (Type v)
  ¬ Nonempty (Abelian (BasisSheaf.{v + 1,v} (allOpenBasis (Option (Type v)))))

/-- The three exact proof targets, with u/v independent in the general clause
and space universe v+1 in each Type-v undersized specialization. -/
def CokernelScopeStatements : Prop :=
  CokernelSectionInjectionStatement.{u,v} ∧
    UndersizedNoCokernelStatement.{v} ∧ UndersizedNotAbelianStatement.{v}

end Langlands.Sheaf.Renard.StarDiagram
