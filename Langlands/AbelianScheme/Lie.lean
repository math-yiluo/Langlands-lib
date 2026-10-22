import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.RelativeDifferentials
import Langlands.AlgebraicGeometry.ModuleDual
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Relative Lie modules of group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The identity section of a group scheme, as a morphism from the base. -/
abbrev identitySection (G : GroupScheme S) : S ⟶ G.X.left := η[G.X].left

@[reassoc (attr := simp)]
lemma identitySection_comp (G : GroupScheme S) :
    G.identitySection ≫ G.X.hom = 𝟙 S := η[G.X].w

/-- Group-scheme homomorphisms preserve the identity section. -/
@[reassoc (attr := simp)]
lemma identitySection_naturality {G H : GroupScheme S} (f : G ⟶ H) :
    G.identitySection ≫ f.hom.hom.left = H.identitySection := by
  exact congrArg (fun g => g.left) (IsMonHom.one_hom f.hom.hom)

/-- The actual relative cotangent sheaf pulled back to the identity section. -/
def cotangentAtIdentity (G : GroupScheme S) : S.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback G.identitySection).obj
    (Langlands.Scheme.relativeDifferentials G.X.hom)

/-- The relative Lie module, defined as the sheaf dual of the cotangent module at the identity. -/
def Lie (G : GroupScheme S) : S.Modules :=
  Langlands.Scheme.Modules.dual G.cotangentAtIdentity

/-- Lie sections are local module-sheaf homomorphisms from the cotangent module to the
structure sheaf, restricted to the actual open subscheme. -/
def lieSectionsEquiv (G : GroupScheme S) (U : S.Opens) :
    Γ(G.Lie, U) ≃
      (G.cotangentAtIdentity.restrict U.ι ⟶
        (Langlands.SchemeModule.structureModule S).restrict U.ι) :=
  Langlands.Scheme.Modules.internalHomSectionsEquiv G.cotangentAtIdentity
    (Langlands.SchemeModule.structureModule S) U

/-- Evaluation of a Lie section on a cotangent section, linear in both entries. -/
def lieEval (G : GroupScheme S) (U : S.Opens) :
    Γ(G.Lie, U) →ₗ[Γ(S, U)] (Γ(G.cotangentAtIdentity, U) →ₗ[Γ(S, U)] Γ(S, U)) :=
  Langlands.Scheme.Modules.dualEval G.cotangentAtIdentity U

end Langlands.GroupScheme

namespace Langlands.CommGroupScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The relative Lie module of a commutative group scheme. -/
abbrev Lie (G : CommGroupScheme S) : S.Modules := Langlands.GroupScheme.Lie G.toGrp

end Langlands.CommGroupScheme

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The relative Lie module of an actual abelian scheme. -/
abbrev Lie (A : AbelianScheme S) : S.Modules := Langlands.GroupScheme.Lie A.toGrp

end Langlands.AbelianScheme
