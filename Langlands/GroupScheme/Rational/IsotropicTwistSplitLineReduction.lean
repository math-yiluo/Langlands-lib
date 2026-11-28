import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Isotropic inner twists and centralizers of split lines

This module states one proposition: if the twist of a quasi-split group by a finite-Galois
cocycle, acting by conjugation, contains a closed copy of `𝔾_m`, then after a finite Galois
refinement of the cover the cocycle is cohomologous to a cocycle with values in the
centralizer of a closed copy of `𝔾_m` in the quasi-split group itself. The statement is not
proved here.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be a quasi-split group over a field `K`, `ξ` a cocycle of `G` on a finite Galois
field cover `Spec L → Spec K`, and `H` a twist of `G` by `ξ` acting by conjugation, given by a
family of identifications `φ` of `G` and `H` over the cover whose discrepancy is `ξ`. If `H`
contains a closed copy `μ` of `𝔾_m`, then on some finite Galois refinement `Spec M → Spec K`
of the cover there are a cochain `g` and a closed copy `ν` of `𝔾_m` in `G` such that every
value of the refined cocycle twisted by `g` centralizes `ν`. -/
def IsotropicTwistSplitLineReductionStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsQuasiSplit G →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle G (GaloisCocycle.cover K L))
      (H : GroupScheme (Spec (CommRingCat.of K)))
      (φ : LocalGroupIso G H (GaloisCocycle.cover K L)),
      IsAffineHom H.X.hom → φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ →
      ∀ μ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ H, IsClosedSubgroup μ →
        ∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (_ : Algebra L M)
          (_ : IsScalarTower K L M) (_ : FiniteDimensional K M) (_ : IsGalois K M)
          (g : GaloisCocycle.cover K M ⟶ G.X)
          (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G),
          IsClosedSubgroup ν ∧
            ∀ {Z : Over (Spec (CommRingCat.of K))} (a b : Z ⟶ GaloisCocycle.cover K M),
              ((ξ.refine (GaloisCocycle.coverMap K L M)).twist g).toFun a b ∈
                (torusCentralizer ν).carrier Z

end Langlands.GroupScheme
