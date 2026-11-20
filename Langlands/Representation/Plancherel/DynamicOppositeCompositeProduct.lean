import Langlands.Representation.Plancherel.DynamicOppositeCanonicalScalar
import Langlands.Representation.Plancherel.RationalRankOneProductDifferences

/-! # Canonical fractions from scalar product formulas for the actual composite -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Induction Aubert.General UnramifiedOperatorFamily ValuationKernelCoordinates
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters (normCharacters χ))}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hi : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

local notation "Mχ" => parameterScheme χ
local notation "hMχ" => parameterScheme_isConnectedReductive χ hG
local notation "hpχ" => parameterProjection_continuous χ
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Ω" => (p.regularRegion ∩ q.regularRegion)
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi
local notation "composite" => conditionalContinuedComposite χ hRefl hCST hG K hK hPK hOppK A p q
  hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
local notation "Induced" z => UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
  (leviNormCharacters χ) (parameterTransport χ z) A

/-- The original continued composite acts by a constant times the pointwise
wall factors throughout a dense open set on its common regular locus. -/
def HasDenseContinuedCompositeRankOneProduct (charts : List (RankOneTranslationChart Mχ)) : Prop :=
  ∃ (κ : ℂˣ) (D' : Set X) (factors : List (X → ℂ)),
    Dense D' ∧ IsOpen D' ∧
    List.Forall₂ (fun chart g => chart.InvariantOn Mχ D' g) charts factors ∧
    ∀ z : ↥Ω, z.val ∈ D' → composite z =
      ((κ : ℂ) * (factors.map fun g => g z.val).prod) •
        Representation.IntertwiningMap.id (Induced z.val).representation

include hD in
set_option maxHeartbeats 1000000 in
/-- Compare the exact composite with its canonical fraction, shrinking the
locus by the two continuation denominators and the nonzero numerator. -/
theorem hasDenseRankOneProduct_of_continuedComposite
    (charts : List (RankOneTranslationChart Mχ)) (hj : jP ≠ 0)
    (hprod : HasDenseContinuedCompositeRankOneProduct χ hRefl hCST hG K hK hPK hOppK A p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ charts) :
    HasDenseRankOneProduct Mχ hMχ charts jP := by
  obtain ⟨κ, D', factors, hd, hopen, hinv, hproduct⟩ := hprod
  obtain ⟨a, b, _, hbn, hfrac, hcomp⟩ := conditionalCanonicalRationalScalar_spec
    χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi
  have han : a ≠ 0 := by
    intro ha
    exact hj (by rw [hfrac, ha, map_zero, zero_div])
  have hR := continuedCompositeRegion_dense Mχ hpχ hMχ p q
    (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ)
  have hoR := p.regularRegion_isOpen.inter q.regularRegion_isOpen
  let S : Set X := {z | a.val z ≠ 0}
  have hS : Dense S := rationalUnramifiedRegular_dense_nonzero Mχ hpχ hMχ a han
  have hoS : IsOpen S := (isClosed_eq (continuous_unramifiedRegularFunction _ a) continuous_const).isOpen_compl
  let D'' := (D' ∩ Ω) ∩ S
  refine ⟨a, b, κ, D'', factors, hfrac, (hd.inter_of_isOpen_right hR hoR).inter_of_isOpen_right hS hoS,
    (hopen.inter hoR).inter hoS, ?_, ?_⟩
  · exact hinv.imp (fun chart g h c z hz htz => h c z hz.1.1 htz.1.1)
  · intro z hz
    let zr : ↥Ω := ⟨z, hz.1.2⟩
    refine ⟨hz.2, hbn zr, ?_⟩
    obtain ⟨v, ℓ, hv⟩ := exists_normalized_compactCoefficient (χ := χ) (hG := hG)
      (K := K) (hK := hK) (hPK := hPK) (A := A) (hne := hne) (hi := hi)
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, map_zero] at hv
      exact zero_ne_one hv
    let e := unramifiedLeviInductionCompactEquiv (decomposition χ) (radical_isClosed χ)
      (radical_unimodular χ hG) K (parabolic_isClosed χ) hK hPK (leviNormCharacters χ)
      (fun ψ => (normCharacters_continuous χ ψ).comp (parameterHomeomorph χ).symm.continuous)
      (projection_continuous χ) (parameterTransport χ z) A
    have hf0 : e.symm v ≠ 0 := (map_ne_zero_iff e.symm e.symm.injective).mpr hv0
    apply smul_left_injective ℂ hf0
    have he := (hcomp zr).symm.trans (hproduct zr hz.1.1)
    exact congrArg (fun J => J (e.symm v)) he

end Langlands.Plancherel
