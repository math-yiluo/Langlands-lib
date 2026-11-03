import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Invariant affine neighbourhoods in actual Borel quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The affine-open-cover input to the flag step: if a smooth connected
unipotent subgroup lies in every Borel through a maximal torus, then every
rational point of an actual Borel quotient has an invariant affine open
neighbourhood. Invariance is equality of inverse-image scheme opens under
the action morphism and the second projection. -/
def FlagInvariantAffineOpenCoverStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
    IsMaximalTorus t →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      (∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
        IsBorelSubgroup b' → SubgroupFunctor.range t ≤ SubgroupFunctor.range b' →
          SubgroupFunctor.range i ≤ SubgroupFunctor.range b') →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b →
        ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
          IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
          Flat q.left → Surjective q.left → QuasiCompact q.left →
          (∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
            g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Z) →
          ∀ (a : SchemeAction G Q),
            (∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
              a.act g (h ≫ q) = (g * h) ≫ q) →
            ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q),
              ∃ V : Q.left.Opens,
                IsAffineOpen V ∧ Set.range x.left ⊆ V ∧
                  (a.restrict i).hom.left ⁻¹ᵁ V =
                    (snd U.X Q).left ⁻¹ᵁ V

end Langlands.GroupScheme
