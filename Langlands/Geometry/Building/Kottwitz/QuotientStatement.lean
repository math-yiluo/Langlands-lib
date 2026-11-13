import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # KP Corollary 11.7.6: quotients induced by the Kottwitz homomorphism -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- The three quotients of KP Corollary 11.7.6, with their maps on representatives. -/
def QuotientStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (Z : GroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (d : ZeroSubgroupDatum i j),
    let N := d.zeroSubgroup
    let H := characterValuationKernel (ValuativeRel.valuation F) G
    let A := Multiplicative (ReductiveInvariantTarget F G hG)
    let Ator := fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG
    ∃ hN : N.Normal,
      letI := hN
      N ≤ H ∧
      (∃ e : (rationalPoints G ⧸ N) ≃* A,
        ∀ g, e (QuotientGroup.mk' N g) = reductiveKottwitzRational F G hG g) ∧
      (∃ e : (H ⧸ N.subgroupOf H) ≃* Ator,
        ∀ x : H, (e (QuotientGroup.mk' (N.subgroupOf H) x) : A) =
          reductiveKottwitzRational F G hG x.val) ∧
      (∃ e : (rationalPoints G ⧸ H) ≃* (A ⧸ Ator),
        ∀ g, e (QuotientGroup.mk' H g) =
          QuotientGroup.mk' Ator (reductiveKottwitzRational F G hG g))

end Langlands.Geometry.Building.Kottwitz
