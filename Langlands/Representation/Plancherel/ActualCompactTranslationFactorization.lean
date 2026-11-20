import Langlands.Representation.Plancherel.ActualTranslatedCompactTensor
import Langlands.Representation.Plancherel.ActualCommonLeviCompactAction
import Langlands.Representation.Plancherel.RationalSourceGammaConjugation

/-! # The actual compact translation factorization -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCompactTranslationFactorization

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor
open ActualConjugateLeviTwist ActualTranslatedCompactTensor UnramifiedOperatorFamily

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
local notation "Lc" => compactTranslation χ g hG A K hK hPK K' hK' hχgK'
set_option hygiene false in
local notation "ρ" => compactTensorRepresentation χ hG K hK χ rfl hPK A

/-- The exact compact translation factors through the actual simultaneous
right action by `g⁻¹` in the two coordinates. The constant factor is
fixed by the same actual translation and action at the unit character. -/
def TranslationFactorization : Prop :=
  ∀ z : X, Lc z = ((Lc 1).comp (ρ 1 (g, g))).comp (ρ z (g⁻¹, g⁻¹))

/-- For conjugate compact subgroups, the elementary reindexing identity
is a closed target about the actual full-parameter translation. -/
def ClosedTranslationFactorizationStatement
    (_hconj : RationalDynamicSource.conjugateCompact g K = K') : Prop :=
  TranslationFactorization χ g hG A K hK hPK K' hK' hχgK'

/-- This exact factorization implies polynomiality on every parameter
subset, with the full source regular algebra. -/
theorem compactTranslation_polynomial_of_factorization
    (h : TranslationFactorization χ g hG A K hK hPK K' hK' hχgK')
    (Ω : Set X) : IsPolynomialOperatorOn Ω (fun z => Lc z.val) := by
  have hAction := compactTensorRepresentation_polynomial χ hG K hK χ rfl hPK A (g⁻¹, g⁻¹)
  have hRestrict : IsPolynomialOperatorOn Ω (fun z => ρ z.val (g⁻¹, g⁻¹)) :=
    fun v => (hAction v).restrict (Set.subset_univ Ω)
  have he : (fun z : Ω => Lc z.val) =
      (fun z : Ω => ((Lc 1).comp (ρ 1 (g, g))).comp (ρ z.val (g⁻¹, g⁻¹))) :=
    funext fun z => h z.val
  exact he.symm ▸ hRestrict.postcomp ((Lc 1).comp (ρ 1 (g, g)))

end Langlands.Plancherel.ActualCompactTranslationFactorization
