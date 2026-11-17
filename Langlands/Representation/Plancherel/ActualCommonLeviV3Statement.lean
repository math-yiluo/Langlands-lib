import Langlands.Representation.Plancherel.ActualCommonLeviRationalTensor
import Langlands.Representation.Plancherel.LeviCompactCoefficients
import Langlands.Representation.Plancherel.ProductInducedSmoothFamilies
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof
import Langlands.Representation.Aubert.General.SemidirectModularCharacter

/-! # Closed common-Levi targets for Waldspurger V.3.1 -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

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
local instance parabolicLocallyCompact
    (psiAux : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (parabolic psiAux) :=
  (DynamicOppositeCanonicalScalar.parabolic_isClosed psiAux).locallyCompactSpace
local instance radicalLocallyCompact
    (psiAux : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (radical psiAux) :=
  (radical_isClosed psiAux).locallyCompactSpace

include hG in
/-- Ambient unimodularity is a published theorem, not an extra input. -/
theorem ambient_modularCharacter (g : RationalPoint F G.X) :
    modularCharacter g = 1 :=
  RationalPointFamily.rationalReductiveUnimodularity F G hG
    Langlands.GroupScheme.standardCocharacter g

include hG in
/-- The actual common-Levi parabolic modular identity follows from the
published literal Levi and radical unimodularity. -/
theorem common_modularCharacter
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ) (p : parabolic ψ) :
    modularCharacter p =
      (HaarModulus.closedRestrictCharacter (radical ψ) (radical_isClosed ψ)
        (parabolic ψ) (commonDecomposition χ ψ hψ).le_normalizer p : ℝ≥0) := by
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    (commonDecomposition χ ψ hψ).modularCharacter_eq_restrictCharacter_of_unimodular
      (commonProjection_continuous χ ψ hψ)
      (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG)
      (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) p

/-- The actual unitary subgroup includes in the full parameter group. -/
def unitaryParameter :
    unitaryUnramifiedCharacters (normCharacters χ) →*
      unramifiedCharacters (normCharacters χ) :=
  Subgroup.inclusion inf_le_left

omit [LocallyOfFiniteType G.X.hom] in
/-- Transport to the literal Levi preserves the unitary character value. -/
theorem unitary_parameter_norm
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (m : levi χ) :
    ‖((parameterTransport χ (unitaryParameter χ z)).val m :
      ℂ)‖ = 1 :=
  z.property.2 ((parameterHomeomorph χ).symm m)

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)

include hsq in
omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
/-- The exact same central quotient Haar measure is used at every unitary
twist; square integrability follows from the published twist theorem. -/
theorem unitaryTwist_squareIntegrable
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    IsSquareIntegrableModCentralSubgroup C hC
      (twistObject χ (unitaryParameter χ z) A).representation
      qMeasure :=
  isSquareIntegrableModCentralSubgroup_unitaryTwist C hC
    (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) (unitary_parameter_norm χ z) qMeasure hsq

include hi in
/-- Only the inducing irreducible representation is used here. -/
theorem unitaryTwist_irreducible
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (twistObject χ (unitaryParameter χ z) A).IsIrreducible :=
  (SmoothRep.isIrreducible_twist_iff
    (parameterTransport χ (unitaryParameter χ z)).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker _ _) A).mpr hi

/-- Identify the central quotient with the actual image of a split component
of the actual centralizer scheme. -/
def IsActualSplitCenter : Prop :=
  ∃ (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (s : S.toGrp ⟶ parameterScheme χ),
    IsSplitComponent s ∧
      C = (rationalPoints.map s).range.map (parameterHomeomorph χ).toMulEquiv.toMonoidHom

variable
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A

/-- An extended comparison still acts on the actual coefficient fibers and
intertwines the full product rational-point action. -/
abbrev UnitaryComparisonFamily :=
  ∀ z : Xu,
    (coefficientFiber χ ψ hψ A (unitaryParameter χ z)).representation.IntertwiningMap
      (coefficientFiber χ ψ' hψ' A (unitaryParameter χ z)).representation

/-- Put a family on the fixed actual compact coefficient carriers. -/
def compactValue
    (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ') (z : Xu) :
    V₀ →ₗ[ℂ] V₁ :=
  (compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A (unitaryParameter χ z)).toLinearMap.comp
    ((T z).toLinearMap.comp
      (compactTensorEquiv χ hG K hK ψ hψ hψK A
        (unitaryParameter χ z)).symm.toLinearMap)

section Germs

variable
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- One local whole-operator representative of the particular actual tensor.
The numerator is polynomial on the full parameter space, and one denominator
works for every vector before any vector is chosen. -/
def IsLocalRepresentative (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)) : Prop :=
  IsOpen U ∧
    IsPolynomialOperatorOn Set.univ (fun z => N z.val) ∧
    (∀ z ∈ U, b.val z ≠ 0) ∧
    ∀ (z : D), z.val ∈ U → N z.val = b.val z.val • J z

/-- A regular value is specified by the rational germ of the actual standard
tensor, allowing cancellation of poles between its two factors. -/
def RegularGermAt (z : X) (L : V₀ →ₗ[ℂ] V₁) : Prop :=
  ∃ (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)),
    z ∈ U ∧ IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U N b ∧
      L = (b.val z)⁻¹ • N z

/-- Every unitary point has one ambient regular representative that describes
the extended family at every unitary point in that neighborhood. -/
def IsRegularUnitaryExtension (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ') : Prop :=
  ∀ z : Xu, ∃ (U : Set X) (N : X → V₀ →ₗ[ℂ] V₁)
    (b : unramifiedRegularFunctions (normCharacters χ)),
    unitaryParameter χ z ∈ U ∧
      IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U N b ∧
      ∀ w : Xu, unitaryParameter χ w ∈ U →
        compactValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T w =
          (b.val (unitaryParameter χ w))⁻¹ • N (unitaryParameter χ w)

/-- The extension agrees with the actual generic tensor at every unitary
parameter where that tensor is defined. -/
def AgreesOnUnitaryGeneric (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ') : Prop :=
  ∀ (z : Xu) (hz : unitaryParameter χ z ∈ D),
    T z = genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
      ⟨unitaryParameter χ z, hz⟩

/-- All regular representatives of the actual rational germ give the specified
value, including representatives with different denominators. -/
def IsUniqueByRationalGerm (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ') : Prop :=
  ∀ (z : Xu) (L : V₀ →ₗ[ℂ] V₁),
    RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) L →
      L = compactValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z

/-- The genuine generic locus is nonempty and dense both ambiently and on the
entire unitary parameter subgroup. An open dense sublocus is also required. -/
def HasDenseGenericLocus : Prop :=
  (D).Nonempty ∧ Dense D ∧ Dense ((unitaryParameter χ) ⁻¹' D) ∧
    ∃ O : Set X, IsOpen O ∧ O.Nonempty ∧ O ⊆ D ∧ Dense O ∧
      Dense ((unitaryParameter χ) ⁻¹' O)

end Germs

include hψK in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The literal Iwasawa factorization in the set formulation used by the
source-normalized compact coefficient and form APIs. -/
theorem iwasawa_sets (g : RationalPoint F G.X) :
    ∃ q ∈ parabolic ψ, ∃ k ∈ K, g = q * k := by
  obtain ⟨q, k, h⟩ := hψK g
  exact ⟨q, q.property, k, k.property, h⟩

/-- The actual coefficient map, with the given K Haar probability. -/
def coefficientMap (z : Xu) :
    coefficientFiber χ ψ hψ A (unitaryParameter χ z) →ₗ[ℂ]
      LocallyConstant (RationalPoint F G.X) ℂ :=
  CompactInduction.leviCoefficientMap
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (twistObject χ (unitaryParameter χ z) A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ)
    (commonProjection_continuous χ ψ hψ) (iwasawa_sets K ψ hψK)
    (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ)
    (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1

/-- The exact inverse-formal-degree form uses the fixed actual central quotient
Haar measure and the same K Haar probability at every unitary twist. -/
def formalDegreeForm (z : Xu) :
    InvariantPositiveForm
      (coefficientFiber χ ψ hψ A (unitaryParameter χ z)).representation :=
  CompactInduction.leviFormalDegreeProductForm
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ)
    (twistObject χ (unitaryParameter χ z) A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ)
    (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG)
    (common_modularCharacter χ hG ψ hψ)
    (compactOpenCofinal_of_nonarchimedean (levi χ)) C hC qMeasure
    (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z)
    (unitaryTwist_irreducible χ A hi z)

/-- V.3.1 on every unitary parameter and every coefficient vector, with the
actual source coefficient maps and inverse-formal-degree forms. -/
def PreservesCoefficientsAndForms
    (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ') : Prop :=
  ∀ z : Xu, Function.Bijective (T z) ∧
    (∀ v : coefficientFiber χ ψ hψ A (unitaryParameter χ z),
      coefficientMap χ hG A C hC qMeasure hsq K hK ψ' hψ' hψ'K z (T z v) =
        coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK z v) ∧
    ∀ v w : coefficientFiber χ ψ hψ A (unitaryParameter χ z),
      (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ' hψ' hψ'K z).inner
          (T z v) (T z w) =
        (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK z).inner v w

/-- Closed common-Levi V.3.1 target. Continuations, scalar inverse data,
nonempty/dense generic loci and the full-unitary regular extension are all
conclusions; the only inputs are the displayed structural and inducing data. -/
def ClosedV31Statement : Prop :=
  IsActualSplitCenter χ C →
  ∃ (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
    (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient),
    Nonempty (ScalarInverseData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) ∧
    HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q ∧
    IsRationalOperatorOn
      (genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)
      (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) ∧
    ∃ T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ',
      IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
      AgreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
      IsUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
      PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi
        K hK ψ hψ hψK ψ' hψ' hψ'K T

end Langlands.Plancherel.ActualCommonLeviV3
