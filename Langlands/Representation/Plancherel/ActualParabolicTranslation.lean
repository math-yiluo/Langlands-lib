import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceStatement
import Langlands.Representation.Plancherel.ActualCommonLeviConjugationStatement

/-! # Actual coefficient translation for arbitrary common-Levi parabolics -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualParabolicTranslation

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualConjugateLeviTwist ActualCommonLeviCoherence

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (g : RationalPoint F G.X)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)

variable (K K' : OpenSubgroup (RationalPoint F G.X))
  (hKK' : RationalDynamicSource.conjugateCompact g K = K')
  (P : ParabolicPresentation χ K)

/-- The actual conjugate parabolic, with its Levi and Iwasawa data transported
through conjugation. The target compact can be kept equal to K for g in K. -/
def conjugatePresentation : ParabolicPresentation χg K' where
  cocharacter := P.cocharacter ≫ (G.innerIso g).hom
  centralizer_eq := ActualCommonLeviConjugation.conjugateCentralizer
    χ P.cocharacter P.centralizer_eq g
  iwasawa := hKK' ▸ conjugate_parabolic_mul_compact P.cocharacter g K P.iwasawa

variable (hG : IsConnectedReductive G) (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))

set_option hygiene false in
local notation "Pg" => conjugatePresentation χ g K K' hKK' P
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "D₀" => commonDecomposition χ P.cocharacter P.centralizer_eq
set_option hygiene false in
local notation "Dg" => commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq
set_option hygiene false in
local notation "hc₀" => radical_isClosed P.cocharacter
set_option hygiene false in
local notation "hcg" => radical_isClosed (Pg).cocharacter
set_option hygiene false in
local notation "hd₀" => DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG
set_option hygiene false in
local notation "hdg" => DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)

/-- Actual left translation of both normalized induction factors and the
canonical conjugate twist identification for the displayed source parabolic. -/
def translatedCoefficient (z : X) :
    (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation.Equiv
      (coefficientFiber χg (Pg).cocharacter (Pg).centralizer_eq Ag
        (conjugateParameter χ g z)).representation := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K' hK' (Pg).cocharacter (Pg).iwasawa
  exact (CoefficientConjugation.leviCoefficientLeftTranslation D₀ Dg g
    (DynamicCoefficientConjugation.parabolic_mem_conjugation P.cocharacter g)
    (DynamicCoefficientConjugation.levi_mem_conjugation χ g)
    (DynamicCoefficientConjugation.radical_mem_conjugation P.cocharacter g)
    hc₀ hcg hd₀ hdg (twistObject χ z A)).trans
      (ActualConjugateLeviTensor.coefficientCongr Dg hcg hdg (conjugateTwistEquiv χ g z A))

variable (Q : ParabolicPresentation χg K')
  (p : ContinuedPair χg hG K' hK'
    (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
    Q.cocharacter Q.centralizer_eq Q.iwasawa Ag)
  (q : ContinuedPair χg hG K' hK'
    Q.cocharacter Q.centralizer_eq Q.iwasawa
    (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa (Ag).contragredient)

set_option hygiene false in
local notation "E" => ActualCommonLeviTensor.genericLocus χg hG K' hK'
  (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa Ag p q

/-- The pullback of the actual simultaneous regular and invertible locus for
this conjugate source parabolic and this target parabolic. -/
def genericLocus : Set X := conjugateParameter χ g ⁻¹' E

/-- Waldspurger's formula with source parabolic independent of the cocharacter
presenting its Levi. Both particular standard continuations are used in the
published common-Levi tensor, after the actual product left translation. -/
def genericComparison (z : genericLocus χ g K K' hKK' P hG A hK' Q p q) :
    (coefficientFiber χ P.cocharacter P.centralizer_eq A z.val).representation.IntertwiningMap
      (coefficientFiber χg Q.cocharacter Q.centralizer_eq Ag
        (conjugateParameter χ g z.val)).representation :=
  (ActualCommonLeviTensor.genericComparison χg hG K' hK'
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa Ag p q
      (Set.restrictPreimage E (conjugateParameter χ g) z)).comp
    (translatedCoefficient χ g K K' hKK' P hG A hK hK' z.val).toIntertwiningMap

end Langlands.Plancherel.ActualParabolicTranslation
