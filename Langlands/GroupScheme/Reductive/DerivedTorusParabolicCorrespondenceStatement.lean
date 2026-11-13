import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.RelativeLevi.Basic

/-! # Statement: maximal tori and parabolic subgroups of a reductive group and its derived group -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Maximal tori and parabolic subgroups of `G` and of `D(G)`** (Conrad, *Reductive group
schemes* (2014), Proposition 5.3.4). Let `G` be a reductive group scheme over a scheme `S`, let
`d : D ⟶ G` be a closed subgroup with normal range such that `D` is semisimple and some fppf
quotient of `G` by the range of `d` is an `S`-torus (so the range of `d` is the derived group
`D(G)`, Theorem 5.3.1), and let `z : Z ⟶ G` be a maximal central torus (closed, central, an
`S`-torus, containing every closed central `S`-torus subgroup). A maximal torus of a group `H`
over `S` is a closed subgroup `t : T ⟶ H` with `T` an `S`-torus whose residue fibres are maximal
tori. Then:
1. for every maximal torus `t` of `G`, the intersection `T ∩ D(G)` (as a subgroup of `D`) has
   the range of a maximal torus of `D`, and multiplication `Z × (T ∩ D(G)) ⟶ G` factors through
   an isogeny onto `T`;
2. for every maximal torus `t'` of `D` there is a maximal torus `t` of `G` such that
   multiplication `Z × T' ⟶ G` factors through an isogeny onto `T` and `T ∩ D(G)` has the range
   of `t'`;
3. maximal tori of `G` with the same intersection with `D(G)` have the same range;
4. the same three assertions for parabolic subgroups, where `P ∩ D(G)` is itself a parabolic
   subgroup of `D` and the isogenies `Z × (P ∩ D(G)) ⟶ P` and `Z × P' ⟶ P` are central. -/
def ReductiveDerivedTorusParabolicCorrespondenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    let IsMaximalCentralTorus : ∀ {Z : GroupScheme S}, (Z ⟶ G) → Prop :=
      fun {Z} z => IsClosedSubgroup z ∧ IsCentral z ∧ RelativeTorus.IsTorus Z ∧
        ∀ (Z' : GroupScheme S) (z' : Z' ⟶ G), IsClosedSubgroup z' → IsCentral z' →
          RelativeTorus.IsTorus Z' → SubgroupFunctor.range z' ≤ SubgroupFunctor.range z
    let IsMaxTorus : ∀ {H : GroupScheme S} {T : CommGroupScheme S}, (T.toGrp ⟶ H) → Prop :=
      fun {_} {T} t => RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
        IsFibrewiseMaximalTorus t
    ∀ (D : GroupScheme S) (d : D ⟶ G), IsClosedSubgroup d →
      (SubgroupFunctor.range d).IsNormal → IsReductive D →
      (∀ s : S, IsSemisimple (geometricFiber D s)) →
      (∃ (Q : GroupScheme S) (q : G ⟶ Q), RelativeTorus.IsTorus Q ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) →
      ∀ (Z : GroupScheme S) (z : Z ⟶ G) (hz : IsCentral z), IsMaximalCentralTorus z →
        -- maximal tori
        (∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G), IsMaxTorus t →
          (∃ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ D), IsMaxTorus t' ∧
            SubgroupFunctor.range t' = SubgroupFunctor.range (subgroupIntersectionFst d t)) ∧
          ∃ e : Z ⊗ subgroupIntersection d t ⟶ T.toGrp, IsIsogeny e ∧
            e ≫ t = prodHom z (subgroupIntersectionHom d t) (hz.commute_values _)) ∧
        (∀ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ D), IsMaxTorus t' →
          ∃ (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (e : Z ⊗ T'.toGrp ⟶ T.toGrp),
            IsMaxTorus t ∧ IsIsogeny e ∧ e ≫ t = prodHom z (t' ≫ d) (hz.commute_values _) ∧
            SubgroupFunctor.range (subgroupIntersectionFst d t) = SubgroupFunctor.range t') ∧
        (∀ (T₁ T₂ : CommGroupScheme S) (t₁ : T₁.toGrp ⟶ G) (t₂ : T₂.toGrp ⟶ G),
          IsMaxTorus t₁ → IsMaxTorus t₂ →
          SubgroupFunctor.range (subgroupIntersectionFst d t₁) =
            SubgroupFunctor.range (subgroupIntersectionFst d t₂) →
          SubgroupFunctor.range t₁ = SubgroupFunctor.range t₂) ∧
        -- parabolic subgroups
        (∀ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i →
          IsRelativeParabolicSubgroup (subgroupIntersectionFst d i) ∧
          ∃ e : Z ⊗ subgroupIntersection d i ⟶ P, IsCentralIsogeny e ∧
            e ≫ i = prodHom z (subgroupIntersectionHom d i) (hz.commute_values _)) ∧
        (∀ (P' : GroupScheme S) (i' : P' ⟶ D), IsRelativeParabolicSubgroup i' →
          ∃ (P : GroupScheme S) (i : P ⟶ G) (e : Z ⊗ P' ⟶ P),
            IsRelativeParabolicSubgroup i ∧ IsCentralIsogeny e ∧
            e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) ∧
            SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i') ∧
        (∀ (P₁ P₂ : GroupScheme S) (i₁ : P₁ ⟶ G) (i₂ : P₂ ⟶ G),
          IsRelativeParabolicSubgroup i₁ → IsRelativeParabolicSubgroup i₂ →
          SubgroupFunctor.range (subgroupIntersectionFst d i₁) =
            SubgroupFunctor.range (subgroupIntersectionFst d i₂) →
          SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂)

end Langlands.GroupScheme
