import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Galois stability of `G(K)^1` and `G(K)^0`, and `G(F)^0 = G(K)^0 ∩ G(F)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- **Galois descent of `G(K)^1` and `G(K)^0`** (Kaletha–Prasad Definition 2.6.23,
Lemma 2.6.24 and Proposition 9.3.24). Let `G` be a connected reductive group over a
nonarchimedean local field `F` and `K = UnramifiedClosure F` the maximal unramified
extension. Then:

1. `G(K)^1`, the common kernel of the normalized valuations of all rational
   characters of `G_K`, is stable under every `σ ∈ Aut(K/F)`;
2. for every datum `E` of KP Definition 2.6.23(1) for `G_K`, the subgroup
   `G(K)^0 = E.zeroPoints` is stable under every `σ ∈ Aut(K/F)`;
3. for every such `E` and every datum `Z0` of KP Definition 2.6.23(3) for `G`,
   relative to any maximal split torus `S` and its centralizer `Z`, the subgroup
   `G(F)^0 = Z0.zeroSubgroup` is the preimage of `G(K)^0` under the extension of
   scalars `G(F) → G(K)` (KP Proposition 9.3.24).

Clause 3 is KP Proposition 9.3.24. Clauses 1 and 2 are derived, not numbered results of
KP; KP use them in §9.2.5 to descend the integral models to the integers of `F`. -/
def UnramifiedZeroDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    (∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
      ∀ x ∈ characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (UnramifiedClosure F) G),
        rationalConjugate F (UnramifiedClosure F) G σ x ∈
          characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (UnramifiedClosure F) G)) ∧
    ∀ E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G),
      (∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
        ∀ x ∈ E.zeroPoints,
          rationalConjugate F (UnramifiedClosure F) G σ x ∈ E.zeroPoints) ∧
      ∀ {S : CommGroupScheme (Spec (CommRingCat.of F))}
        {Z : GroupScheme (Spec (CommRingCat.of F))}
        (i : S.toGrp ⟶ G) (j : Z ⟶ G) (Z0 : ZeroSubgroupDatum i j),
        E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = Z0.zeroSubgroup

end Langlands.Geometry.Building
