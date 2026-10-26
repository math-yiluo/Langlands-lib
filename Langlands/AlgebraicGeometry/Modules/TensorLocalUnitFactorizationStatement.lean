import Langlands.AlgebraicGeometry.Modules.TensorMonoidal

/-! # Local unit factorization of a tensor-invertible pair of scheme modules -/

universe u

open CategoryTheory MonoidalCategory

namespace Langlands.Scheme.Modules

/-- A tensor-invertible pair locally admits maps from the structure module whose
tensor is an isomorphism. This definition states the geometric prerequisite. -/
def TensorLocalUnitFactorizationStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (M N : X.Modules) (_e : M ⊗ N ≅ 𝟙_ X.Modules) (x : X),
    ∃ (U : X.Opens) (_hx : x ∈ U)
      (s : 𝟙_ U.toScheme.Modules ⟶ M.restrict U.ι)
      (t : 𝟙_ U.toScheme.Modules ⟶ N.restrict U.ι),
      IsIso (s ⊗ₘ t)

end Langlands.Scheme.Modules
