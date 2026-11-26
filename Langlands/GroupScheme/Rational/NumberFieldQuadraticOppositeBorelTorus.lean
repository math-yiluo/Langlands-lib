import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.Maximal
import Langlands.Global.AdelicGroupLocalPoints
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Quadratic opposite-Borel tori and cocycle reduction controlled at the real places

`IsQuadraticOppositeBorelTorus Q t` says that `t : T ⟶ G` is a maximal torus over `F`
whose base change to the quadratic extension `Q` has, as its subgroup functor, the full
intersection of the subgroup functors of a geometric Borel subgroup of `G_Q` and of its
Galois translate by the nonidentity automorphism of `Q/F`.

`NumberFieldQuadraticOppositeBorelTorusStatement` combines Platonov–Rapinchuk, Lemmas 6.17
and 6.28: for a semisimple group over a number field that is quasi-split over a totally
imaginary quadratic extension `Q`, such a torus exists, and every cocycle on the cover
`Spec Q → Spec F` that is trivial at the real places is cohomologous to the image of a torus
cocycle on the same cover that is again trivial at the real places. The statement is not
proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] (Q : Type u) [Field Q] [Algebra F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The homomorphism `t : T ⟶ G` over `F` is a maximal torus, `Q/F` is quadratic, and there
are a nonidentity automorphism `σ` of `Q/F` and a geometric Borel subgroup `j : B ⟶ G_Q` such
that, on every test scheme over `Q`, the points of `G_Q` lying in both `B` and its Galois
translate `σ(B)` are exactly the points of the base change `T_Q`: `T_Q = B ∩ σ(B)` as subgroup
functors of `G_Q`. -/
def IsQuadraticOppositeBorelTorus (t : T.toGrp ⟶ G) : Prop :=
  Module.finrank F Q = 2 ∧ IsMaximalTorus t ∧
  ∃ (σ : Q ≃ₐ[F] Q) (B : GroupScheme (Spec (CommRingCat.of Q)))
    (j : B ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G),
    σ ≠ 1 ∧ IsGeometricBorelSubgroup j ∧
    SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F Q)).map t)

/-- Platonov–Rapinchuk, Lemmas 6.17 and 6.28, over a totally imaginary quadratic extension.
Let `G` be a semisimple group over a number field `F`, and let `Q/F` be a quadratic Galois
extension with `Q` totally imaginary such that `G_Q` is quasi-split. Then there is a maximal
torus `t : T ⟶ G` with `T_Q = B ∩ σ(B)` for a geometric Borel subgroup `B` of `G_Q` and the
nonidentity automorphism `σ` of `Q/F`, such that every cocycle `ξ` with values in `G` on the
cover `Spec Q → Spec F` whose pullback to the full base-changed cover at every real place
`w` of `F` is trivial is cohomologous to the image under `t` of a cocycle `δ` with values in
`T` on the same cover whose pullback at every real place is again trivial. -/
def NumberFieldQuadraticOppositeBorelTorusStatement : Prop :=
  ∀ (F Q : Type u) [Field F] [NumberField F] [Field Q] [Algebra F Q]
    [FiniteDimensional F Q] [IsGalois F Q] [IsTotallyComplex Q]
    (_ : Module.finrank F Q = 2) (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSemisimple G → IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G) →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G),
      IsQuadraticOppositeBorelTorus Q t ∧
      ∀ ξ : Cocycle G (GaloisCocycle.cover F Q),
        (∀ w : InfinitePlace F, w.IsReal →
          (ξ.baseChangePullback
            (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
        ∃ δ : Cocycle T.toGrp (GaloisCocycle.cover F Q), (δ.map t).Cohomologous ξ ∧
          ∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial

end Langlands.GroupScheme
