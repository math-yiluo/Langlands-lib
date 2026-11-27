import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Dynamic.Basic

/-! # The Lie algebras of a parabolic, its Levi subgroup and its unipotent radical as weight spaces

For a parabolic subgroup `Q = M' ⋉ V` of a connected reductive group `G` over a field, with a
rational Levi subgroup `M'` and unipotent radical `V`, this file states that some central
cocharacter `ψ` of `M'` presents `Q` as a dynamic parabolic and that, on the Lie algebra of `G`,
`Lie M'` is the weight-zero space of `ψ`, `Lie V` the sum of its positive weight spaces and
`Lie Q` the sum of its nonnegative weight spaces. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme

/-- The Lie algebras of a parabolic `Q = M' ⋉ V`, of its rational Levi subgroup `M'` and of its
unipotent radical `V` are the nonnegative, zero and positive weight spaces of a central
cocharacter `ψ` of `M'` that presents `Q` as the dynamic parabolic `P_G(ψ)`. Here the Lie
algebras are the images in `Lie G` of the actual Lie kernels under the maps induced by
`q`, `l' ≫ q` and `iV ≫ q`, and the weight spaces are those of `𝔾_m` acting on `Lie G` through
`ψ ≫ l' ≫ q` and the adjoint representation. -/
def LeviCocharacterLieWeightsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q M' V : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] [IsAffineHom M'.X.hom] [IsAffineHom V.X.hom]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l' : M' ⟶ Q),
    IsConnectedReductive G → IsParabolicSubgroup q →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsRationalLeviSubgroup l' →
    ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M',
      IsCentral ψ ∧ (Dynamic.parabolic (ψ ≫ l' ≫ q)).IsRepresentedBy q ∧
      weightSpace (ψ ≫ l' ≫ q) (Gm.powerHom _ 0) =
        LinearMap.range (Lie.targetMapLinear (l' ≫ q) k) ∧
      (⨆ n : ℕ, weightSpace (ψ ≫ l' ≫ q) (Gm.powerHom _ (n + 1))) =
        LinearMap.range (Lie.targetMapLinear (iV ≫ q) k) ∧
      (⨆ n : ℕ, weightSpace (ψ ≫ l' ≫ q) (Gm.powerHom _ n)) =
        LinearMap.range (Lie.targetMapLinear q k)

end Langlands.GroupScheme
