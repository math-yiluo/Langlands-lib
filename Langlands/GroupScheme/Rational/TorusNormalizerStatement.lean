import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statements: representability of the torus normalizer and the point quotients `N/Z`

Three statement targets for a split subtorus `i : T ⟶ G` of a connected reductive group
over a field `k`:

* the normalizer and centralizer subgroup functors are represented by smooth closed
  subgroups;
* for a maximal split torus, restriction `N(k)/Z(k) → N(U)/Z(U)` is bijective for every
  connected test scheme `U`;
* over an infinite field, the published `normalizerPoints i` and `centralizerPoints i` are
  the abstract normalizer and centralizer of the torus points `i(T(k))` in `G(k)`.

The quotients here are quotients of groups of points, not points of a quotient scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A subgroup functor has a smooth closed representative when some closed subgroup
`j : H ⟶ G` with `H` smooth over the base represents it. -/
def HasSmoothClosedRepresentative (F : SubgroupFunctor G) : Prop :=
  ∃ (H : GroupScheme S) (j : H ⟶ G), IsClosedSubgroup j ∧ Smooth H.X.hom ∧
    F.IsRepresentedBy j

theorem HasSmoothClosedRepresentative.hasClosedRepresentative {F : SubgroupFunctor G}
    (h : F.HasSmoothClosedRepresentative) : F.HasClosedRepresentative := by
  obtain ⟨H, j, hj, -, hF⟩ := h
  exact ⟨H, j, hj, hF⟩

end SubgroupFunctor

/-- **Normalizer and centralizer of a split torus are smooth closed subgroups**
(Milne 1.83, 1.92 and 13.10). For a split subtorus `i` of a connected reductive group over
a field, the all-test functors `torusNormalizer i` and `torusCentralizer i` are represented
by smooth closed subgroups of `G`. -/
def TorusNormalizerRepresentableStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_ : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_ : IsSplitSubtorus i),
    (torusNormalizer i).HasSmoothClosedRepresentative ∧
      (torusCentralizer i).HasSmoothClosedRepresentative

/-- **The relative Weyl group is the same over every connected test scheme**
(Borel–Tits 5.3; Milne 25.16(b)(c) and 25.17). For a maximal split torus `i` of a connected
reductive group over a field `k` and every connected `k`-scheme `U`, for instance the
spectrum of a field extension of `k`, restriction
`relativeWeylGroup i = N(k)/Z(k) → N(U)/Z(U)` is bijective. -/
def RelativeWeylGroupRestrictStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_ : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_ : IsMaximalSplitTorus i)
    (U : Over (Spec (CommRingCat.of k))) [ConnectedSpace U.left],
    Function.Bijective (relativeWeylGroupRestrict i U)

/-- **Over an infinite field, normalizer and centralizer points are abstract**
(Milne 1.84 and 1.93). For a split subtorus `i` of a connected reductive group over an
infinite field `k`, `normalizerPoints i` is the normalizer, and `centralizerPoints i` the
centralizer, in `G(k)` of the subgroup `i(T(k))` of torus points. -/
def NormalizerPointsInfiniteFieldStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_ : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_ : IsSplitSubtorus i),
    normalizerPoints i =
        Subgroup.normalizer ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) ∧
      centralizerPoints i =
        Subgroup.centralizer ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 _)) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))

end Langlands.GroupScheme
