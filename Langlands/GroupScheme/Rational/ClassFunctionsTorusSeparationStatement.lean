import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: the canonical class quotient separates conjugacy classes of torus points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

/-- **Regular class functions separate semisimple classes**, for points of a maximal torus
(Steinberg 1965, Corollaries 6.4 and 6.6, implication b) ⇒ a)). Let `G` be a semisimple group
over an algebraically closed field `k` and `j : T ⟶ G` a maximal torus. If two points
`s t ∈ T(k)` have the same image under the canonical class-function quotient
`ClassFunctions.rho G`, their images in `G(k)` are conjugate by a point of `G(k)`. -/
def TorusSeparationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (s t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X),
      (s ≫ j.hom.hom) ≫ rho G = (t ≫ j.hom.hom) ≫ rho G →
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
        g * (s ≫ j.hom.hom) * g⁻¹ = t ≫ j.hom.hom

end Langlands.GroupScheme.ClassFunctions
