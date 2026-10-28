import Langlands.AlgebraicGeometry.Modules.RestrictTensor

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.Scheme.Modules

/-- For every open `U` of `X` and module sheaves `M`, `N` on `X`, the comparison
`restrictTensorHom U M N : M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U` is an isomorphism, and it sends the
sheafified pure tensor of two sections over `V ⊆ U` to the sheafified pure tensor of the same
sections over `U.ι ''ᵁ V`. -/
def RestrictTensorComparisonStatement (X : Scheme.{u}) : Prop :=
  ∀ (U : X.Opens) (M N : X.Modules),
    IsIso (restrictTensorHom U M N) ∧
      ∀ (V : U.toScheme.Opens) (m : (M.restrict U.ι).val.obj (op V))
        (n : (N.restrict U.ι).val.obj (op V)),
        ((restrictTensorHom U M N).val.app (op V)).hom
            (((tensorSheafifyUnit (M.restrict U.ι) (N.restrict U.ι)).app (op V)).hom
              (m ⊗ₜ[U.toScheme.presheaf.obj (op V)] n)) =
          ((tensorSheafifyUnit M N).app (op (U.ι ''ᵁ V))).hom
            (m ⊗ₜ[X.presheaf.obj (op (U.ι ''ᵁ V))] n)

end Langlands.Scheme.Modules
