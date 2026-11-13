import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Torus.Weights

/-! # Statement: Lie algebras of dynamic subgroups over a ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Lie algebras of dynamic subgroups over a ring** (Conrad–Gabber–Prasad,
Proposition 2.1.8(1)). Let `R` be any commutative ring and `G` an affine group scheme of
finite presentation over `Spec R` (its structure morphism is affine and locally of finite
presentation), and let `χ` be a cocharacter of `G`. An element `X` of the actual
Lie algebra `lieKernel G R`, viewed as an `R[ε]`-point of `G`, is
* a point of `Dynamic.centralizer χ` exactly when it lies in the weight space of the trivial
  character of `𝔾_m` acting through `χ`;
* a point of `Dynamic.parabolic χ` exactly when it lies in the sum of the weight spaces of the
  characters `t ↦ t ^ n`, `n ≥ 0`;
* a point of `Dynamic.unipotent χ` exactly when it lies in the sum of the weight spaces of the
  characters `t ↦ t ^ n`, `n > 0`. -/
def DynamicRingLieStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G) (X : lieKernel G R),
    (X.val ∈ (Dynamic.centralizer χ).carrier _ ↔
      Additive.ofMul X ∈ weightSpace χ (Gm.powerHom _ 0)) ∧
    (X.val ∈ (Dynamic.parabolic χ).carrier _ ↔
      Additive.ofMul X ∈ ⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)) ∧
    (X.val ∈ (Dynamic.unipotent χ).carrier _ ↔
      Additive.ofMul X ∈ ⨆ n : ℕ, weightSpace χ (Gm.powerHom _ (n + 1)))

end Langlands.GroupScheme
