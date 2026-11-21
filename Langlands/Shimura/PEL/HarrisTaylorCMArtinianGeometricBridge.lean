import Langlands.Shimura.PEL.HarrisTaylorCMArtinianClassReduction
import Langlands.Shimura.PEL.HarrisTaylorCMArtinianNormalization
import Langlands.Shimura.PEL.HarrisTaylorCMArtinianPolarizedLiftingStatement

/-! # The geometric input to Artinian class lifting -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})

/-- A geometric lift gives the object conditions and polarization comparison used by
the actual pointed class map. -/
theorem normalizedPolarizedActionLiftsAlong_spec_of_geometric
    (hGeometric : DivisionCMPolarizedActionArtinianLiftingStatement D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality)
    (hDivision : D.IsDivision)
    {R' R : Type} [CommRing R'] [CommRing R] [IsLocalRing R'] [IsLocalRing R]
    [IsArtinianRing R'] [IsArtinianRing R] (φ : R' →+* R) (hφ : Function.Surjective φ)
    (hker : maximalIdeal R' * RingHom.ker φ = ⊥) (β : Spec (.of R') ⟶ Spec (.of F)) :
    NormalizedPolarizedActionLiftsAlong D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (Spec.map (CommRingCat.ofHom φ)) β := by
  let := auxiliaryStarRing D C
  let b := Spec.map (CommRingCat.ofHom φ)
  intro Y hGood hNum
  have hNormalized := (determinantDimensionCondition_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (b ≫ β) Y).mpr
    ⟨hGood, hNum⟩
  obtain ⟨X, e, hIsometry⟩ := hGeometric hDivision R' R φ hφ hker β Y hNormalized
  have hLiftNormalized :=
    D.harrisTaylorCMArtinianNormalization C R' R φ hφ β X.actionObj Y.actionObj ⟨e⟩ hNormalized
  obtain ⟨hLiftGood, hLiftNum⟩ := (determinantDimensionCondition_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality β X).mp
    hLiftNormalized
  exact ⟨X, hLiftGood, hLiftNum, e, hIsometry⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
