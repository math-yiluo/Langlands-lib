import Langlands.Representation.Plancherel.ActualOppositeCompactScalar
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalarProof
import Batteries.Tactic.OpenPrivate

/-! # Transport of actual opposite continuations by conjugation and compact change -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicOppositeCanonicalScalar

open Aubert.General Induction UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition

attribute [local instance]
  dynamicOppositeCanonicalScalarIsAffine dynamicOppositeCanonicalScalarTopologicalSpace
  dynamicOppositeCanonicalScalarT2Space dynamicOppositeCanonicalScalarIsTopologicalGroup
  dynamicOppositeCanonicalScalarT2Space2 dynamicOppositeCanonicalScalarLocallyCompactSpace
  dynamicOppositeCanonicalScalarNonarchimedeanGroup
  dynamicOppositeCanonicalScalarSecondCountableTopology
  dynamicOppositeCanonicalScalarSecondCountableTopology2
  centralizerClosedImmersion centralizerAffine centralizerFiniteType
  dynamicOppositeCanonicalScalarTopologicalSpace2
  dynamicOppositeCanonicalScalarMeasurableSpace3 dynamicOppositeCanonicalScalarBorelSpace3
  dynamicOppositeCanonicalScalarMeasurableSpace4 dynamicOppositeCanonicalScalarBorelSpace4

open RationalDynamicSource

open private parabolicCompactConjugation oppositeCompactConjugation
  forwardFullDomain_conjugation reverseFullDomain_conjugation
  forwardCompactFamily_conjugation reverseCompactFamily_conjugation inductionIrreducible_conjugation
  from Langlands.Representation.Plancherel.DynamicOppositeConjugationScalarProof
open private transportContinuation transport_open_locus
  from Langlands.Representation.Plancherel.DynamicOppositeConjugationScalarTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (g : rationalPoints G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

variable (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (hPK : ∀ x : rationalPoints G, ∃ p : parabolic χ, ∃ k : K, x = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppK : ∀ x : rationalPoints G, ∃ p : oppositeParabolic χ, ∃ k : K,
    x = (p : rationalPoints G) * (k : rationalPoints G))

local notation "χg" => χ ≫ (G.innerIso g).hom
local notation "Kg" => conjugateCompact g K
local notation "hKg" => conjugateCompact_isCompact g K hK
local notation "hPKg" => conjugate_parabolic_mul_compact χ g K hPK
local notation "hOppKg" => conjugate_oppositeParabolic_mul_compact χ g K hOppK
local notation "Ag" => conjugateRepresentation χ g A
local notation "ep" => parameterConjugationIso χ g
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xg" => unramifiedCharacters (normCharacters χg)

variable (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)

/-- Transport the full-domain forward continuation using the exact
conjugation square for the actual compact standard operators. -/
def conjugateForwardContinuation : ForwardContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag :=
  transportContinuation (ep) (parabolicCompactConjugation χ g A K) (oppositeCompactConjugation χ g A K)
    (fun z => forwardFullDomain_conjugation χ g A z K hK)
    (forwardCompactFamily_conjugation χ g A K hK hRefl hCST hG hPK hOppK) p

/-- Transport the actual reverse continuation by the reverse square. -/
def conjugateReverseContinuation : ReverseContinuation χg hRefl hCST hG Kg hKg hPKg hOppKg Ag :=
  transportContinuation (ep) (oppositeCompactConjugation χ g A K) (parabolicCompactConjugation χ g A K)
    (fun z => reverseFullDomain_conjugation χ g A z K hK)
    (reverseCompactFamily_conjugation χ g A K hK hRefl hCST hG hPK hOppK) q

variable {DF DR D : Set X}
  (hDFo : IsOpen DF) (hDFn : DF.Nonempty) (hDF : DF ⊆ forwardFullDomainRegion χ K hK A)
  (hDRo : IsOpen DR) (hDRn : DR.Nonempty) (hDR : DR ⊆ reverseFullDomainRegion χ K hK A)
  (hDo : IsOpen D) (hDn : D.Nonempty)
  (hDi : ∀ z ∈ D, (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
    (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
  (L : OpenSubgroup (rationalPoints G)) (hL : IsCompact (L : Set (rationalPoints G)))
  (hPL : ∀ x : rationalPoints G, ∃ p : parabolic χg, ∃ k : L, x = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppL : ∀ x : rationalPoints G, ∃ p : oppositeParabolic χg, ∃ k : L,
    x = (p : rationalPoints G) * (k : rationalPoints G))

local notation "H" => parameterScheme χ
local notation "Hg" => parameterScheme χg
local notation "hHg" => parameterScheme_isConnectedReductive χg hG
local notation "Rg" => unramifiedRegularFunctions (normCharacters χg)
local notation "Fg" => rationalUnramifiedFunctionField Hg (parameterProjection_continuous χg) hHg
local notation "sG" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hDFn hDF hDRn hDR hDn hDi

local notation "IG" => fun z : Xg => (UnramifiedLeviInduction (decomposition χg) (radical_isClosed χg)
  (leviNormCharacters χg) (parameterTransport χg z) Ag).IsIrreducible
local notation "I₀" => fun z : X => (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
  (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible
local notation "pG" => conjugateForwardContinuation χ g K hK hRefl hCST hG A hPK hOppK p
local notation "qG" => conjugateReverseContinuation χ g K hK hRefl hCST hG A hPK hOppK q
local notation "pL" => forwardContinuationChangeCompact χg Kg L hKg hL hRefl hCST hG Ag hPKg hOppKg hPL hOppL pG
local notation "qL" => reverseContinuationChangeCompact χg Kg L hKg hL hRefl hCST hG Ag hPKg hOppKg hPL hOppL qG
local notation "c" => oppositeQuotientHaarScale χg Kg L hKg hL
local notation "sF" => rationalUnramifiedFunctionFieldEquiv (parameterProjection_continuous χ)
  (parameterScheme_isConnectedReductive χ hG) (parameterProjection_continuous χg) hHg (ep) sG

include hDFo hDRo hDo in
set_option maxHeartbeats 7000000 in
/-- Compact evaluation of the conjugated canonical opposite scalar on the
changed compact subgroup, with the two quotient Haar factors. -/
theorem exists_conjugatedChangedCompact_canonicalScalar :
    ∃ (p₀ : ForwardContinuation χg hRefl hCST hG L hL hPL hOppL Ag)
      (q₀ : ReverseContinuation χg hRefl hCST hG L hL hPL hOppL Ag)
      (a b : Rg) (t : ℝ≥0), 0 < t ∧ b ≠ 0 ∧ p₀.denominator ≠ 0 ∧ q₀.denominator ≠ 0 ∧
        algebraMap Rg Fg a / algebraMap Rg Fg b =
          algebraMap Rg Fg (algebraMap ℂ Rg (t : ℂ)) * sF ∧
        ∀ z : ↥(p₀.regularRegion ∩ q₀.regularRegion), b.val z.val ≠ 0 ∧
          p₀.continuedComposite q₀ z = (a.val z.val / b.val z.val) • LinearMap.id := by
  obtain ⟨SF, hSF, hnF, hgF⟩ := transport_open_locus (ep)
    (fun z => z ∈ forwardFullDomainRegion χ K hK A)
    (fun z => z ∈ forwardFullDomainRegion χg Kg hKg Ag)
    (fun z => (forwardFullDomain_conjugation χ g A z K hK).symm) DF hDFo hDFn hDF
  obtain ⟨SR, hSR, hnR, hgR⟩ := transport_open_locus (ep)
    (fun z => z ∈ reverseFullDomainRegion χ K hK A)
    (fun z => z ∈ reverseFullDomainRegion χg Kg hKg Ag)
    (fun z => (reverseFullDomain_conjugation χ g A z K hK).symm) DR hDRo hDRn hDR
  obtain ⟨SI, hSI, hnI, hgI⟩ := transport_open_locus (ep) (I₀) (IG)
    (inductionIrreducible_conjugation χ g A) D hDo hDn hDi
  have hLF : SF ⊆ forwardFullDomainRegion χg L hL Ag :=
    Set.Subset.trans hgF (forwardFullDomainRegion_changeCompact χg Kg L hKg hL Ag).symm.le
  have hLR : SR ⊆ reverseFullDomainRegion χg L hL Ag :=
    Set.Subset.trans hgR (reverseFullDomainRegion_changeCompact χg Kg L hKg hL Ag).symm.le
  have hco := conditionalDynamicOppositeConjugationScalar.{u, uV}
    χ hRefl hCST hG g K hK hPK hOppK A p q hDFo hDFn hDF hDRo hDRn hDR hDo hDn hDi
    pG qG hSF hnF hgF hSR hnR hgR hSI hnI hgI
  have hc' := conditionalCanonicalRationalScalar_changeCompact χg Kg L hKg hL hRefl hCST hG Ag
    hPKg hOppKg hPL hOppL pG qG hSF hnF hgF hSR hnR hgR hSI hnI hgI
  obtain ⟨a, b, hb, hreg, hs, happ⟩ := conditionalCanonicalRationalScalar_compact_spec
    χg L hL hRefl hCST hG Ag hPL hOppL pL qL hSF hnF hLF hSR hnR hLR hSI hnI hgI
  refine ⟨pL, qL, a, b, c, oppositeQuotientHaarScale_pos χg Kg L hKg hL, hb, ?_,
    (qL).denominator_ne_zero (hnR.mono hLR), ?_, fun z => ⟨hreg z, happ z⟩⟩
  · exact (pL).denominator_ne_zero (hnF.mono hLF)
  · exact hs.symm.trans (hc'.trans (congrArg (fun s => algebraMap Rg Fg (algebraMap ℂ Rg (c : ℂ)) * s) hco))

end Langlands.Plancherel.DynamicOppositeCanonicalScalar
