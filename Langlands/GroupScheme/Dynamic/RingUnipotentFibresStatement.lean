import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: unipotent fibres of dynamic unipotent subgroups over a ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fibral unipotence of `U_G(χ)` over a ring** (Conrad, *Reductive group schemes* (2014),
Theorem 4.1.7(4), last sentence, for the conjugation action of a cocharacter). Let `G` be an
affine group scheme locally of finite type over `Spec R`, `R` any commutative ring, and `χ` a
cocharacter of `G`. For every representative `j : H ⟶ G` of `U_G(χ)`, every field `K` and every
point `y : Spec K ⟶ Spec R`, the base change of `H` along `y` is unipotent. -/
def DynamicRingUnipotentFibresStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    (H : GroupScheme (Spec (CommRingCat.of R))) (j : H ⟶ G),
    (Dynamic.unipotent χ).IsRepresentedBy j →
      ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
        IsUnipotent ((GroupScheme.baseChange y).obj H)

end Langlands.GroupScheme
