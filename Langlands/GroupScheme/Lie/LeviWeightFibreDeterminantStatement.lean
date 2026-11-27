import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Torus.Weights
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Determinant characters of weight spaces of a central split torus

For a central split torus `A` of an affine group scheme `M` mapping to `G`, the determinant of
`M` on a weight space of `A` in `Lie G` is a rational character over `k`. After a field
extension, its restriction to a split torus through which `A` factors is the sum of the finer
weights over the given one, counted with the dimensions of their weight spaces. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Determinant characters of weight spaces.** Let `G` be an affine group scheme locally of
finite type over a field `k`, `l : M ⟶ G` a homomorphism from an affine group scheme `M`, and
`a : A ⟶ M` a central homomorphism from a split torus `A`. For a fixed field extension `K/k` and
each character `β` of `A`, there is a rational character of `M` over `k` whose base change to
`K`, restricted along any homomorphism `s : S ⟶ M_K` from a split torus `S` through which
`A_K ⟶ M_K` factors, is the sum of the characters `α` of `S` lying over `β`, each counted with
the dimension of its weight space in `Lie G_K`. -/
def LeviWeightFibreDeterminantStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (M : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom M.X.hom] (l : M ⟶ G)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
    IsSplitTorus A.toGrp → IsCentral a →
    let f := algebraBaseMap k K
    let BC := GroupScheme.baseChange f
    letI : IsAffineHom (BC.obj G).X.hom := by
      change IsAffineHom (Limits.pullback.snd G.X.hom f)
      infer_instance
    ∀ β : characterLattice A, ∃ χ : rationalCharacters M,
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of K))) (s : S.toGrp ⟶ BC.obj M)
        (j : (CommGroupScheme.baseChange f).obj A ⟶ S),
        IsSplitTorus S.toGrp → CommGroupScheme.groupHom j ≫ s = BC.map a →
        rationalCharacters.equivCharacterLattice S
            (characterRestrict s (rationalCharacters.baseChange f χ)) =
          ∑ᶠ (α : characterLattice S) (_ : j ≫ α = characterLattice.baseChange f A β),
            (Module.finrank K (weightSpace (s ≫ BC.map l) α) : ℤ) • α

end Langlands.GroupScheme
