import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.AbelianScheme.Torsion
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality

/-! # Statement: the fibral criterion for groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fibral criterion for multiplicative type** (Conrad, *Reductive group schemes* (2014),
Theorem B.4.1). Let `H` be a group scheme over a scheme `S` that is flat, locally of finite
presentation and affine over `S`.
1. If every fibre of `H` is connected, `H` is of multiplicative type if and only if every
   geometric fibre `H_s̄` is of multiplicative type.
2. If `H` is commutative, `H` is of multiplicative type if and only if every geometric fibre
   `H_s̄` is of multiplicative type and, for each `n ≥ 1`, the order of the `n`-torsion
   `H_s̄[n]` (the dimension of its coordinate ring over `κ(s)^alg`) is a locally constant
   function of `s`. -/
def MultiplicativeTypeFibralCriterionStatement : Prop :=
  ∀ (S : Scheme.{u}) (H : GroupScheme S) [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [IsAffineHom H.X.hom],
    ((∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber H s).X.left) →
      (RelativeMultiplicativeType.IsMultiplicativeType H ↔
        ∀ s : S, IsMultiplicativeType (geometricFiber H s))) ∧
    (∀ [IsCommMonObj H.X],
      RelativeMultiplicativeType.IsMultiplicativeType H ↔
        (∀ s : S, IsMultiplicativeType (geometricFiber H s)) ∧
        ∀ n : ℕ, 0 < n → IsLocallyConstant fun s : S =>
          letI := Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
            (torsion (geometricFiber H s) (n : ℤ)).X.hom
          Module.finrank (AlgebraicClosure (S.residueField s))
            Γ((torsion (geometricFiber H s) (n : ℤ)).X.left, ⊤))

end Langlands.GroupScheme
