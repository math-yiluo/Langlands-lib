import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! # KP Corollary 11.7.5: rational surjectivity and the chamber quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open scoped Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.Kottwitz

private instance chamberStatementAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- KP Corollary 11.7.5. Rational surjectivity is unconditional. The chamber clause
is conditional on the supplied building data and uses their coefficient Galois action. -/
def ChamberStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    Function.Surjective (reductiveKottwitzRational F G hG) ∧
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      ∀ (hiT : IsMaximalSplitTorus
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        haveI := mono_of_isMaximalSplitTorus hiT
        haveI : Mono ((GroupScheme.baseChange
            (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
          mono_of_isMaximalSplitTorus hiT
        ∀ (D : KPApartmentData
            (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
            (IntegerValuation.order (MaximalUnramified.valuation F)))
          (C : CentralizerDatum
            (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
          (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
          (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D),
          let B := UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6
          ∀ (Cch : Set B.ReducedBuilding), B.IsChamber Cch →
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              (UnramifiedBuildingDescent.semilinearData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT C h6 hD).action σ '' Cch = Cch) →
            ∀ (S : CommGroupScheme (Spec (CommRingCat.of F)))
              (Z : GroupScheme (Spec (CommRingCat.of F)))
              (i : S.toGrp ⟶ G) (j : Z ⟶ G) (d : ZeroSubgroupDatum i j),
              let P := (MulAction.stabilizer
                (rationalPoints (baseChanged F (inertiaFixedField F) G)) Cch).comap
                  (rationalExtend F (inertiaFixedField F) G)
              let N := d.zeroSubgroup.subgroupOf P
              ∃ hN : N.Normal,
                letI := hN
                ∃ e : (P ⧸ N) ≃* Multiplicative (ReductiveInvariantTarget F G hG),
                  ∀ x : P, e (QuotientGroup.mk' N x) =
                    reductiveKottwitzRational F G hG x.val

end Langlands.Geometry.Building.Kottwitz
