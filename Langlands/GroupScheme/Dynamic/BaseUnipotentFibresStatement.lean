import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: unipotent fibres of dynamic subgroups over any base scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fibral unipotence of `U_G(χ)` over any base scheme.** This is the arbitrary-base
version of the unipotence assertion in CGP, Lemma 2.1.5, obtained by base change to each
field-valued point; compare Conrad, Theorem 4.1.7(4) and the discussion after Example 4.1.9.
For an affine, locally finite-type group scheme `G` over `S`, every representative of
`U_G(χ)` has unipotent base change along every field-valued point of `S`. No smoothness
or finite-presentation hypothesis is imposed. -/
def DynamicBaseUnipotentFibresStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (H : GroupScheme S) (j : H ⟶ G),
    (Dynamic.unipotent χ).IsRepresentedBy j →
      ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ S),
        IsUnipotent ((GroupScheme.baseChange y).obj H)

end Langlands.GroupScheme
