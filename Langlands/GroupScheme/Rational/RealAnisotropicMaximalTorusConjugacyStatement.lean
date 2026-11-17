import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: maximal tori of anisotropic real groups are conjugate (Milne 25.57) -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Conjugacy of maximal tori** (Milne, *Algebraic Groups*, Theorem 25.57 (Cartan)). Let `G`
be an anisotropic semisimple group over `ℝ`, and let `j : T ⟶ G` and `j' : T' ⟶ G` be maximal
tori. Then conjugation by some real point `g ∈ G(ℝ)` carries `T` onto `T'`.

This is a statement only; nothing is proved here. -/
def RealAnisotropicMaximalTorusConjugacyStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G → IsAnisotropic G →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of ℝ))) (j : T.toGrp ⟶ G)
      (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of ℝ))) ⟶ G.X,
          SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j'

end Langlands.GroupScheme
