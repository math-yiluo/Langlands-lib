import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.Representation.Aubert.General.FirstAdjointness

/-! # Jacquet descent of the actual convergent weak-expansion factor -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily DynamicCommonLeviComposition

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine cFamilyLeviFiniteType

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "θ" => CommGroupScheme.groupHom α ≫ i
set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
set_option hygiene false in
local notation "ψ" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "j" => Standard.leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "hj" => outer_isRepresentedBy (i := i) (ν := ν) I' α hα
set_option hygiene false in
local notation "hc" => Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "hR" => auxiliary_realization hG hi hν I I' hζ n hn α hα
set_option hygiene false in
local notation "hθψ" => (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).symm
set_option hygiene false in
local notation "M₁" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "Source" => normalizedInductionFunctor
  (isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I))
  (isClosed_standardUnipotentPoints i ν (rootSet i ν I))

variable (B : SmoothRep.{0, u, uV} ℂ M₁)
  (hB : FactorConverges hG hi hν I I' hζ n hn α hα K hK
      (conjugateRep hG hi hν I I' hζ n hn α hα B))

set_option hygiene false in
local notation "Bconj" => conjugateRep hG hi hν I I' hζ n hn α hα B
set_option hygiene false in
local notation "StageChange" => normalizedInductionEquivOfEquiv (decomposition χs) (radical_isClosed χs)
  (restrictedConjugateEquiv hG hi hν I I' hζ n hn α hα B)

set_option maxHeartbeats 1600000 in
/-- The original factor before evaluation at the identity, with normalized induction in stages. -/
def cFactorStagedIntertwiner :=
  let translation := factorTranslation hG hi hν I I' hζ n hn α hα B
  let inputNorm := normalizedInductionLeviEquiv (commonDecomposition ψ θs hθψ) (radical_isClosed θs)
    (DynamicOppositeCanonicalScalar.radical_unimodular θs hG) Bconj
  let outputNorm := normalizedInductionLeviEquiv (commonDecomposition ψ ψ rfl) (radical_isClosed ψ)
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) Bconj
  let intertwiner := factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST Bconj hB
  let stages := SmoothRep.hom ((RealizedLeviStages.inductionInStagesIso F hG θ j hj hc χs ψ hR
    (radical_isClosed ψ) (radical_isClosed θ) (levi_isClosed θ)).app Bconj).hom
  let input := inputNorm.toIntertwiningMap.comp translation.toIntertwiningMap
  let transported := outputNorm.symm.toIntertwiningMap.comp (intertwiner.comp input)
  stages.comp transported

set_option maxHeartbeats 1800000 in
/-- The actual factor descends to the normalized Jacquet quotient of the outer parabolic. -/
def cFactorJacquetHom :=
  FirstAdjointness.forward (decomposition θ) (radical_isClosed θ)
    (DynamicOppositeCanonicalScalar.radical_unimodular θ hG) _ _
    (cFactorStagedIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST B hB)

set_option maxHeartbeats 2500000 in
/-- On every original vector the normalized Jacquet factor recovers the actual `cFactor`
after changing the inner inducing model by the published isomorphism. -/
def CFactorJacquetDescentStatement : Prop :=
  ∀ v : (Source).obj B,
    (StageChange) (cFactorJacquetHom hG hi hν I I' hζ n hn α hα K hK hCST B hB
      (Jacquet.Localization.mk ((Source).obj B).representation (radical θ) 1 v)) =
      cFactor hG hi hν I I' hζ n hn α hα K hK hCST B hB v

set_option maxHeartbeats 3000000 in
/-- Evaluation of the descended map on the actual Jacquet class gives the original stage
restriction at the identity, including the inverse outer half-modulus. -/
theorem cFactorJacquetDescent :
    CFactorJacquetDescentStatement hG hi hν I I' hζ n hn α hα K hK hCST B hB := by
  intro v
  rfl

end Langlands.HarishChandraSchwartz.WeakExpansion
