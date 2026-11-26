import Langlands.GroupScheme.Rational.NumberFieldHasseKernelReduction
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: toral representatives of quadratic cocycles over number fields -/

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Let `F` be a number field, `G` a connected reductive group over `F` and `L/F` a
quadratic Galois extension. Every cocycle of `G` on the cover `Spec L → Spec F` that is
trivial at every real place is cohomologous to the image of a cocycle of a maximal
`F`-torus of `G` on the same cover, and this torus cocycle can be chosen trivial at every
real place. Triviality at a real place `w` means triviality of the base change to the
actual pullback of the cover to the completion `F_w`. This is the toral reduction of
Platonov–Rapinchuk, *Algebraic Groups and Number Theory*, Lemma 6.28, printed
pp. 369–370, without its hypothesis that `G` has a Borel subgroup over `L`. -/
def NumberFieldQuadraticToralReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      Module.finrank F L = 2 →
      ∀ ξ : Cocycle G (GaloisCocycle.cover F L),
        (∀ w : InfinitePlace F, w.IsReal →
          let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
          let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
          (ξ.baseChange b _ r).IsTrivial) →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
          (η : Cocycle T.toGrp (GaloisCocycle.cover F L)),
          IsMaximalTorus i ∧
          (∀ w : InfinitePlace F, w.IsReal →
            let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
            let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
            (η.baseChange b _ r).IsTrivial) ∧
          ξ.Cohomologous (η.map i)

end Langlands.GroupScheme
