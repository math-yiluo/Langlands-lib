import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Relative
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Statement: the derived group of a reductive group scheme over a base -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The derived group of a reductive group scheme** (Conrad, *Reductive group schemes* (2014),
Theorem 5.3.1). Call a homomorphism `d : D ⟶ G` of group schemes over a scheme `S'` admissible
when it is a closed subgroup with normal range, `D` is a semisimple `S'`-group (reductive with
semisimple geometric fibres, Definition 3.1.1), and some fppf quotient `q : G ⟶ Q` with kernel
the range of `d` has an `S'`-torus `Q` as target. For every reductive group scheme `G` over a
scheme `S` there is an admissible `d : D ⟶ G` such that
1. every admissible `d' : D' ⟶ G` has the same range as `d` (uniqueness of `D(G)`);
2. a `T`-point of `G` lies in the range of `d` exactly when, on some fppf cover of `T`, its
   restrictions lie in the commutator subgroups of the points of `G` (`D(G)` represents the fppf
   sheafification of the commutator subfunctor);
3. the base change of `d` along every `S' ⟶ S` is admissible (formation of `D(G)` commutes with
   base change);
4. for every fppf quotient `q : G ⟶ Q` with kernel the range of `d` and every homomorphism
   `φ : G ⟶ A` to a commutative `S`-group scheme, `φ` factors uniquely through `q`. -/
def RelativeDerivedGroupStatement : Prop :=
  let Admissible : ∀ {S' : Scheme.{u}} {G' D' : GroupScheme S'}, (D' ⟶ G') → Prop :=
    fun {S'} {G' D'} d =>
      IsClosedSubgroup d ∧ (SubgroupFunctor.range d).IsNormal ∧ IsReductive D' ∧
        (∀ s : S', IsSemisimple (geometricFiber D' s)) ∧
        ∃ (Q : GroupScheme S') (q : G' ⟶ Q),
          RelativeTorus.IsTorus Q ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (D : GroupScheme S) (d : D ⟶ G), Admissible d ∧
      (∀ (D' : GroupScheme S) (d' : D' ⟶ G), Admissible d' →
        SubgroupFunctor.range d' = SubgroupFunctor.range d) ∧
      (∀ (T : Over S) (x : T ⟶ G.X), x ∈ (SubgroupFunctor.range d).carrier T ↔
        ∃ 𝒰 : Scheme.Cover.{u}
            (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left,
          ∀ i : 𝒰.I₀, (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ x ∈
            _root_.commutator (Over.mk (𝒰.f i ≫ T.hom) ⟶ G.X)) ∧
      (∀ (S' : Scheme.{u}) (b : S' ⟶ S), Admissible ((GroupScheme.baseChange b).map d)) ∧
      (∀ (Q : GroupScheme S) (q : G ⟶ Q),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
        ∀ (A : GroupScheme S) [IsCommMonObj A.X] (φ : G ⟶ A), ∃! ψ : Q ⟶ A, q ≫ ψ = φ)

end Langlands.GroupScheme
