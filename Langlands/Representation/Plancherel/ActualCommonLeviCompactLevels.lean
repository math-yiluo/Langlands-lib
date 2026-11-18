import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceStatement
import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Langlands.Representation.EquivalencePullback

/-! # Actual compact product models and level refinements -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCompactLevels

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualCommonLeviV3 UnramifiedOperatorFamily

section Normalization

variable {H : Type*} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U : Subgroup H} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set H)) (hδ : IsUnimodularModulus U hU)
  (B : SmoothRep.{0, _, uV} ℂ M)

/-- The inverse of the published value-preserving product normalization. -/
def positiveToProduct :
    Representation.Equiv
      (leviProductInducedCoefficientObject h hU B).representation
      (productInducedCoefficientObject h hU B).representation :=
  (productInducedCoefficientLeviEquiv h hU B hδ).symm

end Normalization

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
  DynamicOppositeCanonicalScalar.centralizerFiniteType
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
  (hG : IsConnectedReductive G)

local instance ambientMeasurable : MeasurableSpace (RationalPoint F G.X) := borel _
local instance ambientBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance leviMeasurable : MeasurableSpace (levi χ) := borel _
local instance leviBorel : BorelSpace (levi χ) := ⟨rfl⟩
local instance leviLocallyCompact : LocallyCompactSpace (levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

open ActualCommonLeviCoherence

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "Par" => ParabolicPresentation χ K
local notation "X" => unramifiedCharacters (normCharacters χ)

/-- The fixed compact product model used by the existing orbit section space. -/
abbrev productCompact (P : Par) :=
  ProductInducedCompactPicture (commonDecomposition χ P.cocharacter P.centralizer_eq) K A

/-- The actual right action of the compact product group. -/
abbrev productCompactAction (P : Par) :=
  productInducedCompactRepresentation
    (commonDecomposition χ P.cocharacter P.centralizer_eq) K A

/-- Value-preserving passage from positive-Levi coefficient functions to the
published normalized product coefficient functions. -/
def normalizationEquiv (P : Par) (z : X) :
    Representation.Equiv
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (productInducedCoefficientObject
        (commonDecomposition χ P.cocharacter P.centralizer_eq)
        (radical_isClosed P.cocharacter) (twistObject χ z A)).representation :=
  positiveToProduct
    (commonDecomposition χ P.cocharacter P.centralizer_eq)
    (radical_isClosed P.cocharacter)
    (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG) (twistObject χ z A)

/-- Restriction to the exact fixed product compact model, including the
actual inverse smooth-dual twist identification. -/
def productCompactEquiv (P : Par) (z : X) :
    Representation.Equiv
      ((coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation.comp
        (K.prod K).toSubgroup.subtype)
      (productCompactAction χ A K P) := by
  exact (Langlands.Cohomology.HyperextAbutment.equivComp
    (normalizationEquiv χ hG A K P z) (K.prod K).toSubgroup.subtype).trans
    (productInducedCompactEquiv (leviNormCharacters χ)
      (commonDecomposition χ P.cocharacter P.centralizer_eq) K
      (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter) hK
      (fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
        (parameterHomeomorph χ).symm.continuous)
      (commonProjection_continuous χ P.cocharacter P.centralizer_eq)
      (radical_isClosed P.cocharacter) P.iwasawa (parameterTransport χ z) A)

/-- Conjugate an actual coefficient intertwiner by the two specified compact
restrictions. This helper makes no assertion that its input is a standard map. -/
def compactMap (P Q : Par) (z : X)
    (T : Representation.IntertwiningMap
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation) :
    (productCompactAction χ A K P).IntertwiningMap (productCompactAction χ A K Q) := by
  let T' :
      Representation.IntertwiningMap
        ((coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation.comp
          (K.prod K).toSubgroup.subtype)
        ((coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation.comp
          (K.prod K).toSubgroup.subtype) :=
    ⟨T.toLinearMap, fun k => T.isIntertwining' k.val⟩
  exact ((productCompactEquiv χ hG A K hK Q z).toIntertwiningMap.comp T').comp
    (productCompactEquiv χ hG A K hK P z).symm.toIntertwiningMap

/-- The square uses the entire actual coefficient fiber. -/
theorem compactMap_square (P Q : Par) (z : X)
    (T : Representation.IntertwiningMap
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation)
    (v : coefficientFiber χ P.cocharacter P.centralizer_eq A z) :
    compactMap χ hG A K hK P Q z T (productCompactEquiv χ hG A K hK P z v) =
      productCompactEquiv χ hG A K hK Q z (T v) := by
  exact congrArg (fun w => productCompactEquiv χ hG A K hK Q z (T w))
    ((productCompactEquiv χ hG A K hK P z).symm_apply_apply v)

/-- The actual compact level fixed by the displayed open subgroup. -/
abbrev level (P : Par) (H : OpenSubgroup (K.prod K)) :=
  fixedVectors (productCompactAction χ A K P) H.toSubgroup

/-- A smaller open subgroup gives the canonical inclusion of fixed vectors. -/
def levelInclusion (P : Par) {H H' : OpenSubgroup (K.prod K)} (h : H' ≤ H) :
    level χ A K P H →ₗ[ℂ] level χ A K P H' :=
  Submodule.inclusion (by
    intro v hv k
    exact hv ⟨k.val, h k.property⟩)

@[simp]
theorem levelInclusion_val (P : Par) {H H' : OpenSubgroup (K.prod K)}
    (h : H' ≤ H) (v : level χ A K P H) :
    (levelInclusion χ A K P h v : productCompact χ A K P) = v.val := rfl

/-- The two successive refinements are the same literal inclusion. -/
theorem levelInclusion_trans (P : Par) {H H' H'' : OpenSubgroup (K.prod K)}
    (h : H' ≤ H) (h' : H'' ≤ H') :
    (levelInclusion χ A K P h').comp (levelInclusion χ A K P h) =
      levelInclusion χ A K P (h'.trans h) := by
  ext v
  rfl

/-- Restrict the specified compact map to its actual compact level. -/
def levelMap (P Q : Par) (z : X)
    (T : Representation.IntertwiningMap
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation)
    (H : OpenSubgroup (K.prod K)) :
    level χ A K P H →ₗ[ℂ] level χ A K Q H :=
  fixedVectorsMap (compactMap χ hG A K hK P Q z T) H.toSubgroup

/-- The level map commutes with the actual inclusion into the compact model. -/
theorem levelMap_inclusion (P Q : Par) (z : X)
    (T : Representation.IntertwiningMap
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation)
    (H : OpenSubgroup (K.prod K)) :
    (fixedVectors (productCompactAction χ A K Q) H.toSubgroup).subtype.comp
        (levelMap χ hG A K hK P Q z T H) =
      (compactMap χ hG A K hK P Q z T).toLinearMap.comp
        (fixedVectors (productCompactAction χ A K P) H.toSubgroup).subtype := rfl

/-- Refinement commutes with the comparison on the nose. -/
theorem levelMap_refinement (P Q : Par) (z : X)
    (T : Representation.IntertwiningMap
      (coefficientFiber χ P.cocharacter P.centralizer_eq A z).representation
      (coefficientFiber χ Q.cocharacter Q.centralizer_eq A z).representation)
    {H H' : OpenSubgroup (K.prod K)} (h : H' ≤ H) :
    (levelInclusion χ A K Q h).comp (levelMap χ hG A K hK P Q z T H) =
      (levelMap χ hG A K hK P Q z T H').comp (levelInclusion χ A K P h) := by
  ext v
  rfl

end Langlands.Plancherel.ActualCommonLeviCompactLevels
