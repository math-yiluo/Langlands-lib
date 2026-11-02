import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Torus.Weights

/-! # Statement: Lie algebras of dynamic subgroups as sums of weight spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Lie algebras of dynamic subgroups** (Conrad–Gabber–Prasad, Proposition 2.1.8(1)). Let `G`
be an affine group scheme locally of finite type over a field `k` and `χ` a cocharacter of `G`.
An element `X` of the actual Lie algebra `lieKernel G k`, viewed as a `k[ε]`-point of `G`, is
* a point of `Dynamic.centralizer χ` exactly when it lies in the weight space of the trivial
  character of `𝔾_m` acting through `χ`;
* a point of `Dynamic.parabolic χ` exactly when it lies in the sum of the weight spaces of the
  characters `t ↦ t ^ n`, `n ≥ 0`;
* a point of `Dynamic.unipotent χ` exactly when it lies in the sum of the weight spaces of the
  characters `t ↦ t ^ n`, `n > 0`. -/
def DynamicLieStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (X : lieKernel G k),
    (X.val ∈ (Dynamic.centralizer χ).carrier _ ↔
      Additive.ofMul X ∈ weightSpace χ (Gm.powerHom _ 0)) ∧
    (X.val ∈ (Dynamic.parabolic χ).carrier _ ↔
      Additive.ofMul X ∈ ⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)) ∧
    (X.val ∈ (Dynamic.unipotent χ).carrier _ ↔
      Additive.ofMul X ∈ ⨆ n : ℕ, weightSpace χ (Gm.powerHom _ (n + 1)))

end Langlands.GroupScheme
