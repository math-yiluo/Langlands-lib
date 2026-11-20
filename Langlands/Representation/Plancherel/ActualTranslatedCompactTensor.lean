import Langlands.Representation.Plancherel.ActualConjugateLeviRationalParameter
import Langlands.Representation.Plancherel.ActualConjugateLeviV3Statement

/-! # The actual translated standard tensor on fixed compact carriers -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualTranslatedCompactTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualConjugateLeviTwist ActualConjugateLeviRationalParameter UnramifiedOperatorFamily

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
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (hG : IsConnectedReductive G) (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)

variable (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

set_option hygiene false in
local notation "C₀" => compactTensorEquiv χ hG K hK χ rfl hPK A
set_option hygiene false in
local notation "Cg" => compactTensorEquiv χg hG K' hK' χg rfl hχgK' Ag
set_option hygiene false in
local notation "L" => ActualConjugateLeviTensor.translatedCoefficient χ g hG A K hK hPK

/-- The actual left translation and conjugate inducing identification,
read between the fixed compact coefficient carriers. -/
def compactTranslation (z : X) :
    compactFiber χ K χ rfl A →ₗ[ℂ] compactFiber χg K' χg rfl Ag :=
  (Cg (conjugateParameter χ g z)).toLinearMap.comp
    ((L z).toIntertwiningMap.toLinearMap.comp (C₀ z).symm.toLinearMap)

set_option hygiene false in
local notation "Lc" => compactTranslation χ g hG A K hK hPK K' hK' hχgK'

variable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χg)
  (hψK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag)
  (q : ContinuedPair χg hG K' hK' ψ hψ hψK' χg rfl hχgK' (Ag).contragredient)

set_option hygiene false in
local notation "D" => ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "Jc" => pulledBackStandardTensor χ g hG A K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "Bc" => ActualConjugateLeviV3.compactComparison χ g hG A
  K hK hPK K' hK' hχgK' ψ hψ hψK' p q
/-- The actual compact comparison constructed by translation followed by
its particular standard tensor on the genuine generic locus. -/
def compactComparison (z : D) :
    compactFiber χ K χ rfl A →ₗ[ℂ] compactFiber χg K' ψ hψ Ag :=
  (Jc z).comp (Lc z.val)

set_option hygiene false in
local notation "Tc" => compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q

/-- The compact composite agrees with the chart of the ambient map used
in the V.3 germ. This proposition records the chart identification. -/
def AgreesWithV3CompactChart : Prop := ∀ z : D, Tc z = Bc z

/-- A polynomial compact translation preserves the clearing denominator
of the actual standard tensor on the full simultaneous generic locus. -/
theorem compactComparison_clears
    (b : unramifiedRegularFunctions (normCharacters χ))
    (hb : IsPolynomialOperatorOn D (fun z => b.val z.val • Jc z))
    (hL : IsPolynomialOperatorOn D (fun z => Lc z.val)) :
    IsPolynomialOperatorOn D (fun z => b.val z.val • Tc z) := by
  simpa only [compactComparison, LinearMap.smul_comp] using hb.comp hL

/-- The explicit actual reverse-dual scalar input and polynomiality of the
actual compact translation give one denominator for the whole composite. -/
theorem compactComparison_rational_of_polynomialTranslation
    (d : ScalarInverseData χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag p q)
    (hL : IsPolynomialOperatorOn D (fun z => Lc z.val)) :
    IsRationalOperatorOn D Tc := by
  obtain ⟨b, hb, hpoly⟩ := pulledBackStandardTensor_rational χ g hG A
    K' hK' hχgK' ψ hψ hψK' p q d
  exact ⟨b, hb, compactComparison_clears χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q b hpoly hL⟩

end Langlands.Plancherel.ActualTranslatedCompactTensor
