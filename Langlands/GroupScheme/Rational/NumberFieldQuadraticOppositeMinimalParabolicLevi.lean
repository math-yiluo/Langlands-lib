import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.Global.AdelicGroupLocalPoints
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Quadratic opposite minimal parabolics and cocycle reduction to their Levi subgroups

`IsQuadraticOppositeMinimalParabolicLevi Q t` says that `t : C ⟶ G` is a closed subgroup over
`F` whose base change to the quadratic extension `Q` is a Levi subgroup of a minimal parabolic
subgroup `P` of `G_Q` defined over `Q`, and is, as a subgroup functor, the full intersection of
`P` with its Galois translate by the nonidentity automorphism of `Q/F`.

`NumberFieldQuadraticOppositeMinimalParabolicLeviStatement` combines Platonov–Rapinchuk,
Lemmas 6.17' and 6.28', for the conjugacy class of minimal parabolic subgroups: for a semisimple
group over a number field and a totally imaginary quadratic extension `Q`, such a subgroup
exists, and every cocycle on the cover `Spec Q → Spec F` that is trivial at the real places is
cohomologous to the image of a cocycle of the subgroup on the same cover that is again trivial
at the real places. The statement is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] (Q : Type u) [Field Q] [Algebra F Q]
  {G C : GroupScheme (Spec (CommRingCat.of F))}

/-- The homomorphism `t : C ⟶ G` over `F` is a closed subgroup, `Q/F` is quadratic, and there
are a nonidentity automorphism `σ` of `Q/F`, a minimal parabolic subgroup `j : P ⟶ G_Q` over
`Q` and a rational Levi subgroup `l : C_Q ⟶ P` with `l ≫ j = t_Q`, such that, on every test
scheme over `Q`, the points of `G_Q` lying in both `P` and its Galois translate `σ(P)` are
exactly the points of `C_Q`: `C_Q = P ∩ σ(P)` as subgroup functors of `G_Q`. -/
def IsQuadraticOppositeMinimalParabolicLevi (t : C ⟶ G) : Prop :=
  Module.finrank F Q = 2 ∧ IsClosedSubgroup t ∧
  ∃ (σ : Q ≃ₐ[F] Q) (P : GroupScheme (Spec (CommRingCat.of Q)))
    (j : P ⟶ (GroupScheme.baseChange (algebraBaseMap F Q)).obj G)
    (l : (GroupScheme.baseChange (algebraBaseMap F Q)).obj C ⟶ P),
    σ ≠ 1 ∧ IsMinimalParabolicSubgroup j ∧ IsRationalLeviSubgroup l ∧
    l ≫ j = (GroupScheme.baseChange (algebraBaseMap F Q)).map t ∧
    SubgroupFunctor.range j ⊓ SubgroupFunctor.range (radicalGaloisHom j σ) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F Q)).map t)

/-- Platonov–Rapinchuk, Lemmas 6.17' and 6.28', for the reflexive conjugacy class of minimal
parabolic subgroups, over a totally imaginary quadratic extension. Let `G` be a semisimple group
over a number field `F`, and let `Q/F` be a quadratic Galois extension with `Q` totally
imaginary. Then there is a closed subgroup `t : C ⟶ G` over `F` such that `C_Q` is a Levi
subgroup of a minimal parabolic subgroup `P` of `G_Q` and `C_Q = P ∩ σ(P)` for the nonidentity
automorphism `σ` of `Q/F`, and such that every cocycle `ξ` with values in `G` on the cover
`Spec Q → Spec F` whose pullback to the full base-changed cover at every real place `w` of `F`
is trivial is cohomologous to the image under `t` of a cocycle `δ` with values in `C` on the
same cover whose pullback at every real place is again trivial. -/
def NumberFieldQuadraticOppositeMinimalParabolicLeviStatement : Prop :=
  ∀ (F Q : Type u) [Field F] [NumberField F] [Field Q] [Algebra F Q]
    [FiniteDimensional F Q] [IsGalois F Q] [IsTotallyComplex Q]
    (_ : Module.finrank F Q = 2) (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSemisimple G →
    ∃ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
      IsQuadraticOppositeMinimalParabolicLevi Q t ∧
      ∀ ξ : Cocycle G (GaloisCocycle.cover F Q),
        (∀ w : InfinitePlace F, w.IsReal →
          (ξ.baseChangePullback
            (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial) →
        ∃ δ : Cocycle C (GaloisCocycle.cover F Q), (δ.map t).Cohomologous ξ ∧
          ∀ w : InfinitePlace F, w.IsReal →
            (δ.baseChangePullback
              (algebraBaseMap F (Global.placeCompletion F (.inl w)))).IsTrivial

end Langlands.GroupScheme
