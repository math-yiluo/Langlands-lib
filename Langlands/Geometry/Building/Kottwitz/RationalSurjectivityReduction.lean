import Langlands.Geometry.Building.Kottwitz.RationalChamberQuotientReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly

/-! # Rational Kottwitz surjectivity from the remaining geometric inputs -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.Kottwitz

private instance rationalSurjectivityExtendedAffineHom
    {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The global inputs supply actual stable building data; no separate
building-availability or rational-surjectivity premise is needed. -/
def RationalSurjectivityReductionStatement : Prop :=
  SpecialTorusExistenceStatement.{u} →
  UnramifiedTwistedChamberStatement.{u} →
  UnramifiedParahoricModelStatement.{u} →
  IntegralModel.UnramifiedSmoothModelDescentStatement.{u} →
  UnramifiedChamberExactSequenceStatement.{u} →
  ReductiveKottwitzDescentStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    Function.Surjective (reductiveKottwitzRational F G hG)

/-- Construct compatible Galois-stable apartment data, take a chamber stable
under the trivial cocycle, and lift in its rational stabilizer. -/
theorem rationalSurjectivityReduction : RationalSurjectivityReductionStatement.{u} := by
  intro hSpec hTw hparahoric hdescent hexact hmap F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ := hSpec F G hG S iS hiS
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨D, C, h6⟩ := UnramifiedBuildingDescent.exists_omegaCompatible
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    quasiSplitIntegerApartmentExistence iT hGK hiT
  have hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D :=
    MaximalUnramified.galoisStable_of_isOmegaCompatible iT hiTc hGK hiT D C h6
  obtain ⟨Y, hY, hYσ⟩ := hTw F G hG T iT hiT D C h6 hD (fun _ => 1)
    (fun σ τ => by rw [map_one, mul_one])
    ⟨⊥, inferInstance, fun _ _ => rfl⟩
  have hYΓ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).action σ '' Y = Y := by
    intro σ
    simpa only [one_smul] using hYσ σ
  let E := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (inertiaFixedField F) G) hGK
  have hseq := hexact F G hG T iT hiT D C h6 Y hY
  have hlift := stableChamberLifting hparahoric hdescent F G hG
    (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6)
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD)
    E Y hY hYΓ hseq.1 (hseq.2 E)
    (hmap.2 F G hG).1 (hmap.2 F G hG).2.2
  intro a
  obtain ⟨g, hg⟩ := hlift a
  exact ⟨g.val, hg⟩

/-- The seven remaining global theorem inputs imply the exact target,
including unconditional rational surjectivity and the supplied-chamber quotient. -/
theorem chamberStatement_of_remainingInputs
    (hSpec : SpecialTorusExistenceStatement.{u})
    (hTw : UnramifiedTwistedChamberStatement.{u})
    (hparahoric : UnramifiedParahoricModelStatement.{u})
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hexact : UnramifiedChamberExactSequenceStatement.{u})
    (hmap : ReductiveKottwitzDescentStatement.{u})
    (hzero : ZeroKernelStatement.{u}) : ChamberStatement.{u} :=
  chamberStatement_of_surjective_of_geometricInputs
    hparahoric hdescent hexact hmap hzero
    (rationalSurjectivityReduction hSpec hTw hparahoric hdescent hexact hmap)

end Langlands.Geometry.Building.Kottwitz
