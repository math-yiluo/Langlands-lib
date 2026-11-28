import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitPlancherelWeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralFiberAdapter
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarProof
import Langlands.Representation.Plancherel.DynamicCommonLeviIrreducibility
import Langlands.Representation.Plancherel.SquareIntegrableCentralPullback
import Langlands.Representation.Plancherel.RationalCentralQuotient

/-! # The density package of a square-integrable inducing representation -/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.DynamicInducedOrbit.DensityPackage

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 600000 in
/-- The actual dynamic Levi modulo its norm kernel and the transported
split-center point image is finite. -/
theorem finite_dynamicSplitQuotient
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : S.toGrp ⟶ parameterScheme χ) (ha : IsSplitComponent a)
    (C : Subgroup (levi χ)) [C.Normal]
    (hCsplit : C = ((parameterHomeomorph χ).toMonoidHom.comp (rationalPoints.map a)).range) :
    Finite ((levi χ) ⧸ (commonNormKernel (leviNormCharacters χ) ⊔ C)) := by
  let e := parameterHomeomorph χ
  let M := parameterScheme χ
  let B := (rationalPoints.map a).range
  have hB : B ≤ Subgroup.center (rationalPoints M) := ha.isCentralSplitTorus.isCentral.range_le_center
  let : B.Normal := B.normal_of_le_center hB
  let : Finite (rationalPoints M ⧸ (rationalCommonNormKernel M ⊔ B)) :=
    finite_rationalCentralQuotient a ha.isCentralSplitTorus.isCentral
      (finiteIndex_splitValuationImage_of_isSplitComponent (parameterScheme_isConnectedReductive χ hG) a ha)
  have hker : (rationalCommonNormKernel M).map e.toMonoidHom =
      commonNormKernel (leviNormCharacters χ) :=
    (Subgroup.map_equiv_eq_comap_symm e.toMulEquiv _).trans
      (commonNormKernel_pullback e.symm (normCharacters χ)).symm
  have hcenter : B.map e.toMonoidHom = C :=
    (MonoidHom.range_comp e.toMonoidHom (rationalPoints.map a)).symm.trans hCsplit.symm
  have hmap : (rationalCommonNormKernel M ⊔ B).map e.toMonoidHom =
      commonNormKernel (leviNormCharacters χ) ⊔ C := by
    rw [Subgroup.map_sup, hker, hcenter]
  exact Finite.of_injective _ (QuotientGroup.congr _ _ e.toMulEquiv hmap).symm.injective

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (j : T.toGrp ⟶ G) (ζ : cocharacterLattice T)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic (CommGroupScheme.groupHom ζ ≫ j), ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic (CommGroupScheme.groupHom ζ ≫ j), ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi (CommGroupScheme.groupHom ζ ≫ j)))

set_option hygiene false in
local notation "χ" => (CommGroupScheme.groupHom ζ ≫ j)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ j)

variable (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : S.toGrp ⟶ MS) (ha : IsSplitComponent a)
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hCsplit : C = ((parameterHomeomorph χ).toMonoidHom.comp (rationalPoints.map a)).range)
  (hirr : A.IsIrreducible)
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu)

set_option maxHeartbeats 1800000 in
/-- The original opposite continuations at the specified compact give a
density package for an irreducible representation square integrable modulo
the indicated split component. -/
def ofSquareIntegrable : DensityPackage j ζ hRefl hCST hG A := by
  let hloc := DynamicCommonLeviIrreducibility.hasOpenIrreducibilityLocus χ χ rfl A hG hirr C hC mu
    hsq
  let D := Classical.choose hloc
  have hD := Classical.choose_spec hloc
  let := finite_dynamicSplitQuotient χ hG a ha C hCsplit
  have hscalar := conditionalDynamicOppositeUnitaryScalar.{u, uV} χ hRefl hCST hG K hK hPK
    hOppK A p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    hD.1 hD.2.1 hD.2.2 C hC mu hsq
  exact
    { K := K
      hK := hK
      hPK := hPK
      hOppK := hOppK
      p := p
      q := q
      DForward := DForward
      DReverse := DReverse
      hDForward := hDForward
      hneForward := hneForward
      hDForwardΩ := hDForwardΩ
      hDReverse := hDReverse
      hneReverse := hneReverse
      hDReverseΩ := hDReverseΩ
      D := D
      hD := hD.1
      hne := hD.2.1
      hirr := hD.2.2
      hreg := fun z => (hscalar.2 (unitaryToUnramified MS z) z.property).regularAt }

end Langlands.HarishChandraSchwartz.DynamicInducedOrbit.DensityPackage
