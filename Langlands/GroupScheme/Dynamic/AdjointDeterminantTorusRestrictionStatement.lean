import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Lie.ActionWeights
import Langlands.GroupScheme.Torus.Split

/-! # Restriction of the adjoint determinant character to a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

/-- Over a field `k`, the restriction of `det(Ad | Lie U)` along a homomorphism `j` from a split
torus `T` to the represented parabolic `P(χ)` is the sum (in the additive character group) of the
nonzero characters `α` of `T` occurring in `Lie(U)`, each with multiplicity the `k`-dimension of
its weight space in `Lie(U)`; there are finitely many such `α`. Nonreduced roots and all
multiplicities are kept, and the characteristic and the rank of `T` are arbitrary. -/
def AdjointDeterminantTorusRestrictionStatement : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy iP) (hU : (unipotent χ).IsRepresentedBy iU)
    [IsAffineHom U.X.hom] [IsAffine P.X.left]
    {d : ℕ} (c : Lie.FiniteCoordinates U d)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}, IsSplitTorus T.toGrp →
    ∀ j : T.toGrp ⟶ P,
      ((parabolicAdjointAction hP hU).lieRoots j).Finite ∧
      characterRestrict j (adjointDeterminantCharacter hP hU c) =
        ∑ᶠ α ∈ (parabolicAdjointAction hP hU).lieRoots j,
          Module.finrank (CommRingCat.of k) ((parabolicAdjointAction hP hU).lieWeightSpace j α) •
            (rationalCharacters.equivCharacterLattice T).symm α

end Langlands.GroupScheme.Dynamic
