import Langlands.Geometry.Building.Kottwitz.StableChamberLifting
import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement
import Langlands.Geometry.Building.Kottwitz.ChamberStatement
import Langlands.Geometry.Building.KPZeroDatumExistence

/-! # The rational chamber quotient from geometric and Kottwitz inputs -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.Kottwitz

private instance rationalChamberQuotientExtendedAffineHom
    {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- All geometric and actual-map inputs remain explicit; zero-datum existence
for the base-changed reductive group is supplied by a proved construction. -/
def RationalChamberQuotientReductionStatement : Prop :=
  UnramifiedParahoricModelStatement.{u} →
  IntegralModel.UnramifiedSmoothModelDescentStatement.{u} →
  UnramifiedChamberExactSequenceStatement.{u} →
  ReductiveKottwitzDescentStatement.{u} →
  ZeroKernelStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
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

/-- Compose chamber exactness, the descended neutral model, integral-coset
lifting and the exact rational kernel to obtain the specified quotient map. -/
theorem rationalChamberQuotientReduction :
    RationalChamberQuotientReductionStatement.{u} := by
  intro hparahoric hdescent hexact hmap hzero F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let := mono_of_isMaximalSplitTorus hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD B Cch hch hstable S Z i j d P N
  let E := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (inertiaFixedField F) G)
    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
  have hseq := hexact F G hG T iT hiT D C h6 Cch hch
  have hlift := stableChamberLifting hparahoric hdescent F G hG B
    (UnramifiedBuildingDescent.semilinearData iT
      (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
      hiT C h6 hD) E Cch hch hstable hseq.1 (hseq.2 E)
    (hmap.2 F G hG).1 (hmap.2 F G hG).2.2
  exact rationalSubgroupQuotient_of_zeroKernel F G hG hzero S Z i j d P hlift

/-- Unconditional rational surjectivity together with the explicit geometric and
map inputs closes the exact target; none of those inputs is proved here. -/
theorem chamberStatement_of_surjective_of_geometricInputs
    (hparahoric : UnramifiedParahoricModelStatement.{u})
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hexact : UnramifiedChamberExactSequenceStatement.{u})
    (hmap : ReductiveKottwitzDescentStatement.{u})
    (hzero : ZeroKernelStatement.{u})
    (hsurj : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
      Function.Surjective (reductiveKottwitzRational F G hG)) :
    ChamberStatement.{u} := by
  intro F _ _ _ _ G hG
  exact ⟨hsurj F G hG,
    rationalChamberQuotientReduction hparahoric hdescent hexact hmap hzero F G hG⟩

end Langlands.Geometry.Building.Kottwitz
