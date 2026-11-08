import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Representation.Category.Basic

/-! # The `PQ`-regularity lemma (Renard VII.3.3)

For represented parabolics `P = MN` and `Q = MU` of a connected reductive group with the same
Levi subgroup `M`, a split component `a : A_M → M` and a smooth representation `σ` of `M(F)`:
`PQ`-regularity `I_σ + I^{PQ}_σ = ℂ[A_M(F)]` is equivalent to
`I_σ + ⋂_{w̄ < 1̄} I^{Q,w̄}_σ = ℂ[A_M(F)]`; it forces the exponents of `σ` to be disjoint from
those of every graded piece below `1̄`; and for `σ` of finite length that disjointness implies
`PQ`-regularity. The ideals `I^{Q,w̄}_σ` and the exponents of the pieces are read on the full
graded pieces of the geometric lemma, at arbitrary intersection data.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.3.3, Lemma, for represented parabolics `P = MN` and `Q = MU` with the same
Levi subgroup `M` of `G` (`l ≫ p = lQ ≫ q`) and a split component `a : A ⟶ M`. For every
smooth representation `σ` of `M(F)`, every choice of representatives `z w̄` of the actual
double cosets `P(F) \ G(F) / Q(F)` and every choice of intersection data at the
representatives of the double cosets strictly below `1̄` in the Bruhat relation:
1. `I_σ + I^{PQ}_σ = ℂ[A(F)]` if and only if `I_σ + ⋂_{w̄ < 1̄} I^{Q,w̄}_σ = ℂ[A(F)]`, with
   `I^{Q,w̄}_σ` the kernel on the full graded piece `i^M_{Q'} ∘ w ∘ r^M_{P'}(σ)`;
2. if `σ` is `PQ`-regular, then for every `w̄ < 1̄` no exponent of `A(F)` on `σ` is an exponent
   of `A(F)` on that graded piece;
3. if `σ` has finite length and the disjointness of 2 holds for every `w̄ < 1̄`, then `σ` is
   `PQ`-regular. -/
def PQRegularityLemmaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
        (ha : IsSplitComponent a),
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        haveI := leviPoints_nonarchimedeanGroup p l hp hl
        letI := RationalPointFamily.splitComponentPointTopology ha
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
          (z : parabolicDoubleCosets p q → rationalPoints G),
          (∀ w, DoubleCoset.mk (pointImage p) (pointImage q) (z w) = w) →
          ∀ (D : ∀ w, Geometric.BruhatLT (pointImage p) (pointImage q) w
              (identityParabolicDoubleCoset p q) →
              GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (z w)),
            (IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ ↔
                splitComponentKernel l hl a σ ⊔
                  (⨅ (w) (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
                    (identityParabolicDoubleCoset p q)),
                    pieceSplitComponentKernel a (D w h) σ) = ⊤) ∧
              (IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
                ∀ w (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
                  (identityParabolicDoubleCoset p q)),
                  Disjoint (groupExponents ha σ)
                    {χ | IsGeneralizedWeight ((D w h).pieceFunctor.obj σ).ρ
                      (rationalPoints.map a) χ
                      ha.isCentralSplitTorus.isCentral.map_mem_center}) ∧
              (σ.HasFiniteLength →
                (∀ w (h : Geometric.BruhatLT (pointImage p) (pointImage q) w
                  (identityParabolicDoubleCoset p q)),
                  Disjoint (groupExponents ha σ)
                    {χ | IsGeneralizedWeight ((D w h).pieceFunctor.obj σ).ρ
                      (rationalPoints.map a) χ
                      ha.isCentralSplitTorus.isCentral.map_mem_center}) →
                IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)

end Langlands.Aubert.General.RepresentedParabolic
