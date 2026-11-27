import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Statement: torus cocycles of anisotropic quadratic tori in simply connected groups

Let `G` be a simply connected group over a number field `F`, and `T` a maximal `F`-torus
of `G` that splits over a quadratic extension `L` and is anisotropic over `F`. The module
states that every cocycle of `T` on the cover `Spec L → Spec F` that is trivial at the real
places becomes trivial in `G`. It proves nothing.
-/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Let `F` be a number field, `G` a simply connected group over `F`, `L/F` a Galois
extension of degree `2`, and `i : T → G` a maximal `F`-torus whose base change to `L` is
split and which is anisotropic over `F`. Every cocycle `η` of `T` on the cover
`Spec L → Spec F` that is trivial at every real place has trivial image `η.map i` in `G`.
Triviality at a real place `w` means triviality of the base change to the actual pullback
of the cover to the completion `F_w`. This is the step of the Hasse principle for groups of
types `E_7` and `E_8` in Platonov–Rapinchuk, *Algebraic Groups and Number Theory*, §6.8
(printed p. 386) that follows Lemma 6.28, carried out with the rank-one subgroups of the
simple roots and the componentwise induction of the proof of Proposition 6.25 (printed
pp. 394–395). -/
def NumberFieldQuadraticAnisotropicToralKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalTorus i →
        IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj T.toGrp) →
        IsAnisotropic T.toGrp →
        ∀ η : Cocycle T.toGrp (GaloisCocycle.cover F L),
          (∀ w : InfinitePlace F, w.IsReal →
            let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
            let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
            (η.baseChange b _ r).IsTrivial) →
          (η.map i).IsTrivial

end Langlands.GroupScheme
