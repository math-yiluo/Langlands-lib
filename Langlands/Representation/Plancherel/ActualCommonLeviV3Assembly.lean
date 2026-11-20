import Langlands.Representation.Plancherel.ActualCommonLeviV3PreservationExtension
import Langlands.Representation.Plancherel.ActualCommonLeviV3RegularExtension
import Langlands.Representation.Plancherel.ActualCommonLeviV3Bijectivity
import Langlands.Representation.Plancherel.RationalUnitaryPoleFactorization

/-! # Assembling the common-Levi unitary comparison from its generic identities -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor
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
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "F₀" z => coefficientFiber χ ψ hψ A (unitaryParameter χ z)
local notation "F₁" z => coefficientFiber χ ψ' hψ' A (unitaryParameter χ z)
local notation "E₀" => compactTensorEquiv χ hG K hK ψ hψ hψK A
local notation "E₁" => compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A
local notation "C₀" => coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK
local notation "C₁" => coefficientMap χ hG A C hC qMeasure hsq K hK ψ' hψ' hψ'K
local notation "B₀" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK
local notation "B₁" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ' hψ' hψ'K
local notation "M₀" => compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi
local notation "M₁" => compactFormalDegreeModel χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "Du" => (unitaryParameter χ) ⁻¹' D
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J[" z "," hz "]" =>
  genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
    (Subtype.mk (unitaryParameter χ z) hz)

variable
  (hform : ∀ (z : unitaryUnramifiedCharacters (normCharacters χ))
    (hz : unitaryParameter χ z ∈ genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)
    (v w : coefficientFiber χ ψ hψ A (unitaryParameter χ z)),
    let Jz := genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
      ⟨unitaryParameter χ z, hz⟩
    (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ' hψ' hψ'K z).inner (Jz v) (Jz w) =
      (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK z).inner v w)

include hform in
private theorem compactComparison_formalDegreeModel_norm
    (z : Xu) (hz : z ∈ Du) (a : V₀) : ‖M₁ (J ⟨unitaryParameter χ z, hz⟩ a)‖ = ‖M₀ a‖ := by
  let e := E₀ (unitaryParameter χ z)
  let v := e.symm a
  have hv : e v = a := e.apply_symm_apply a
  have hJ : J ⟨unitaryParameter χ z, hz⟩ a = E₁ (unitaryParameter χ z) (J[z, hz] v) :=
    (congrArg (fun t : V₀ => J ⟨unitaryParameter χ z, hz⟩ t) hv.symm).trans
      (compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
        ⟨unitaryParameter χ z, hz⟩ v).symm
  have he : inner ℂ (M₁ (J ⟨unitaryParameter χ z, hz⟩ a)) (M₁ (J ⟨unitaryParameter χ z, hz⟩ a)) =
      inner ℂ (M₀ a) (M₀ a) := by
    calc
      _ = inner ℂ (M₁ (E₁ (unitaryParameter χ z) (J[z, hz] v)))
          (M₁ (E₁ (unitaryParameter χ z) (J[z, hz] v))) :=
        congrArg₂ (fun t s : V₁ => inner ℂ (M₁ t) (M₁ s)) hJ hJ
      _ = (B₁ z).inner (J[z, hz] v) (J[z, hz] v) :=
        compactFormalDegreeModel_inner χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi
          z (J[z, hz] v) (J[z, hz] v)
      _ = (B₀ z).inner v v := hform z hz v v
      _ = inner ℂ (M₀ (e v)) (M₀ (e v)) :=
        (compactFormalDegreeModel_inner χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi z v v).symm
      _ = _ := congrArg₂ (fun t s : V₀ => inner ℂ (M₀ t) (M₀ s)) hv hv
  exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) _).trans
    ((congrArg (fun c : ℂ => Real.sqrt (RCLike.re c)) he).trans
      (norm_eq_sqrt_re_inner (𝕜 := ℂ) _).symm)

variable
  (b : unramifiedRegularFunctions (normCharacters χ))
  (N : unramifiedCharacters (normCharacters χ) →
    compactFiber χ K ψ hψ A →ₗ[ℂ] compactFiber χ K ψ' hψ' A)
  (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
  (hnum : ∀ z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q,
    N z.val = b.val z.val • compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)

include hform hN hnum in
/-- The exact generic form identity bounds the cleared numerator on the full
unitary group using the original common denominator and the source norm. -/
theorem compactComparison_hasClearedUnitaryBound (hD : Dense Du) :
    HasClearedUnitaryBound (parameterScheme χ)
      (fun z => (M₁).toLinearMap.comp (N z)) b := by
  refine hasClearedUnitaryBound_of_dense (parameterScheme χ) _
    (hN.postcomp (M₁).toLinearMap) b Du hD ?_
  intro a
  refine ⟨‖M₀ a‖, norm_nonneg _, ?_⟩
  intro z hz
  have hval : N (unitaryParameter χ z) a =
      b.val (unitaryParameter χ z) • (J ⟨unitaryParameter χ z, hz⟩ a) :=
    congrArg (fun L : V₀ →ₗ[ℂ] V₁ => L a) (hnum ⟨unitaryParameter χ z, hz⟩)
  have hm := (congrArg (M₁) hval).trans ((M₁).map_smul _ _)
  change ‖M₁ (N (unitaryParameter χ z) a)‖ ≤ ‖M₀ a‖ * ‖b.val (unitaryParameter χ z)‖
  apply le_of_eq
  calc
    _ = ‖b.val (unitaryParameter χ z)‖ * ‖M₁ (J ⟨unitaryParameter χ z, hz⟩ a)‖ :=
      (congrArg norm hm).trans (norm_smul _ _)
    _ = ‖b.val (unitaryParameter χ z)‖ * ‖M₀ a‖ :=
      congrArg (fun c : ℝ => ‖b.val (unitaryParameter χ z)‖ * c)
        (compactComparison_formalDegreeModel_norm χ hG A C hC qMeasure hsq hi K hK
          ψ hψ hψK ψ' hψ' hψ'K p q hform z hz a)
    _ = _ := mul_comm _ _

variable
  (hD : HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q)
  (f : RationalUnitaryPoleFactorization (parameterScheme χ) b)
  (hden : ∀ z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q, b.val z.val ≠ 0)

include hform hN hnum hD f hden in
private theorem poleFactorization_germs (z : Xu) :
    ∃ L : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) L :=
  exists_regularGermAt_of_poleFactorization χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
    b f N hN M₁
    (compactComparison_hasClearedUnitaryBound χ hG A C hC qMeasure hsq hi K hK
      ψ hψ hψK ψ' hψ' hψ'K p q hform b N hN hnum hD.2.2.1)
    hden hnum z

/-- Construct the actual unitary family from a pole factorization of one
common denominator and the exact generic isometry. -/
def comparisonFamilyOfPoleFactorization : UnitaryComparisonFamily χ A ψ hψ ψ' hψ' :=
  comparisonFamilyOfRegularGerms χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD.2.1
    (poleFactorization_germs χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK ψ' hψ' hψ'K
      p q hform b N hN hnum hD f hden)

local notation "T" => comparisonFamilyOfPoleFactorization χ hG A C hC qMeasure hsq hi
  K hK ψ hψ hψK ψ' hψ' hψ'K p q hform b N hN hnum hD f hden

/-- The constructed family has the exact regularity, agreement, uniqueness
and preservation clauses of the closed statement once the two generic
identities and the denominator presentation have been supplied. -/
theorem comparisonFamilyOfPoleFactorization_spec
    (hcoeff : ∀ (z : Xu) (hz : z ∈ Du) (v : F₀ z), C₁ z (J[z, hz] v) 1 = C₀ z v 1) :
    IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
    AgreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
    IsUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T ∧
    PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK ψ' hψ' hψ'K T := by
  have hR : IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T :=
    comparisonFamilyOfRegularGerms_isRegular χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD.2.1
      (poleFactorization_germs χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK ψ' hψ' hψ'K
        p q hform b N hN hnum hD f hden)
  have hA := hR.agreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
  refine ⟨hR, hA, hR.isUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    p q hD.2.1, ?_⟩
  have hv (z : Xu) (hz : z ∈ Du) (v : F₀ z) : T z v = J[z, hz] v :=
    congrArg (fun S : (F₀ z).representation.IntertwiningMap (F₁ z).representation => S v) (hA z hz)
  have hf (z : Xu) (v w : F₀ z) : (B₁ z).inner (T z v) (T z w) = (B₀ z).inner v w :=
    preserves_formalDegreeForm_of_regular_of_dense χ hG A C hC qMeasure hsq hi
      K hK ψ hψ hψK ψ' hψ' hψ'K p q T hR hD.2.2.1
      (fun s hs a b => (congrArg₂ (fun x y : F₁ s => (B₁ s).inner x y)
        (hv s hs a) (hv s hs b)).trans (hform s hs a b)) z v w
  obtain ⟨z₀, hz₀⟩ := hD.1
  intro z
  refine ⟨comparison_bijective_of_preservesFormalDegreeForm χ hG A K hK
    ψ hψ hψK ψ' hψ' hψ'K p q C hC qMeasure hsq hi ⟨z₀, hz₀⟩ z T (hf z), ?_, hf z⟩
  exact preserves_coefficients_of_regular_of_dense χ hG A C hC qMeasure hsq
    K hK ψ hψ hψK ψ' hψ' hψ'K p q T hR hD.2.2.1
    (fun s hs a => (congrArg (fun x : F₁ s => C₁ s x 1) (hv s hs a)).trans (hcoeff s hs a)) z

end Langlands.Plancherel.ActualCommonLeviV3
