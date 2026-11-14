import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: conjugacy and density of Cartan subgroups -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.44, the assertions over an algebraically closed field. Let `G` be a
smooth connected affine group over an algebraically closed field `k`.
* Any two Cartan subgroups of `G` are conjugate by a `k`-point of `G`.
* For every Cartan subgroup `c : C ⟶ G`, the image of the conjugation morphism
  `G × C ⟶ G`, `(g, x) ↦ g c(x) g⁻¹`, contains a dense open subset of `G`: the conjugates of
  `C`, which are the Cartan subgroups of `G`, cover a dense open subset. -/
def CartanConjugacyDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ (C C' : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G) (c' : C' ⟶ G),
      IsCartanSubgroup c → IsCartanSubgroup c' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          SubgroupFunctor.range (c ≫ (G.innerIso g).hom) = SubgroupFunctor.range c') ∧
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G), IsCartanSubgroup c →
      ∃ U : Set G.X.left, IsOpen U ∧ Dense U ∧
        U ⊆ Set.range (fst G.X C.X * (snd G.X C.X ≫ c.hom.hom) * (fst G.X C.X)⁻¹).left

end Langlands.GroupScheme
