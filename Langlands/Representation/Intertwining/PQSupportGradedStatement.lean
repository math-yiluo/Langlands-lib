import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Category.Basic

/-! # Support subquotients of `r_Q^G ∘ i_P^G` (Renard VII.3.2)

For represented parabolics `P = MN` and `Q = MU` of a connected reductive group with the same
Levi subgroup `M`, and a linear order `⪯` on `P(F) \ G(F) / Q(F)` refining the Bruhat
relation: the inclusions `F̃^{⪯w̄} ⊆ F̃^{≺w̄} ⊆ F̃^{<w̄}` and `F̃^{≤w̄} ⊆ F̃^{<w̄}` of support
subspaces of `i_P^G`, the natural isomorphism `F^{≺w̄}/F^{⪯w̄} ≅ F^{<w̄}/F^{≤w̄}` of their
images in `r_Q^G ∘ i_P^G`, the reformulated geometric lemma
`F^{≺w̄}/F^{⪯w̄} ≅ i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{M∩w·Q}` at arbitrary intersection data, and the
natural identification of `F^{<1̄}/F^{≤1̄}` with the identity functor.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.3.2, for represented parabolics `P = MN` and `Q = MU` with the same Levi
subgroup `M` of `G` (`l ≫ p = lQ ≫ q`). For every linear order `o` on
`P(F) \ G(F) / Q(F)` refining the Bruhat relation and every double coset `w`:
1. at every smooth representation `W` of `M(F)`, `F̃^{⪯w}(W) ⊆ F̃^{≺w}(W) ⊆ F̃^{<w}(W)` and
   `F̃^{≤w}(W) ⊆ F̃^{<w}(W)`;
2. `F^{≺w}/F^{⪯w} ≅ F^{<w}/F^{≤w}` as functors to representations of `M(F)`;
3. for every representative `z` of `w` and every intersection datum `D` at `z`,
   `F^{≺w}/F^{⪯w} ≅ D.pieceFunctor`, the piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}`.
Moreover `F^{<1̄}/F^{≤1̄}` is naturally isomorphic to the identity: there are equivariant
linear equivalences `(F^{<1̄}/F^{≤1̄})(W) ≃ W`, natural in `W`. -/
def PQSupportGradedStatement : Prop :=
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
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        (∀ (o : LinearOrder (parabolicDoubleCosets p q)),
          Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o →
          ∀ w : parabolicDoubleCosets p q,
            (∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
              (initialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
                  (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ∧
                (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
                  (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W ∧
                (closureVanishingSubfunctor p l r hp hr hl hmul q w).obj W ≤
                  (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W) ∧
            Nonempty
              ((initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w).quotientFunctor
                  (strictInitialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w) ≅
                (closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ w).quotientFunctor
                  (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ w)) ∧
            ∀ (z : rationalPoints G),
              DoubleCoset.mk (pointImage p) (pointImage q) z = w →
              ∀ D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z,
                Nonempty
                  ((initialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o
                      w).quotientFunctor
                    (strictInitialSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ o w) ≅
                    D.pieceFunctor)) ∧
        ∃ e : ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
            ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)).quotientObj
              (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)) W).ρ.Equiv W.representation,
          ∀ (W W' : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (f : W ⟶ W') x,
            e W' (((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)).quotientMap
              (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)) f).hom x) =
              SmoothRep.hom f (e W x)

end Langlands.Aubert.General.RepresentedParabolic
