import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.Plancherel.ActualCommonLeviCompactAction
import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Smooth.Factorization.TwoFactorExternalTensorProof
import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Langlands.Representation.Unitary.CompletionIntertwiner
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Bijectivity of the actual common-Levi unitary comparison -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

private theorem fixedVectors_eq_of_action_eq
    {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ σ : Representation ℂ H V} (L : Subgroup H)
    (h : ∀ x ∈ L, ρ x = σ x) :
    fixedVectors ρ L = fixedVectors σ L := by
  have he : ρ.comp L.subtype = σ.comp L.subtype :=
    MonoidHom.ext fun x => h x x.property
  exact congrArg Representation.invariants he

private theorem surjective_of_generic_fixedVectors
    {H V W : Type*} [Group H] [TopologicalSpace H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ ρ' : Representation ℂ H V} {σ σ' : Representation ℂ H W}
    (K : OpenSubgroup H) (hρ : ∀ x ∈ K, ρ x = ρ' x) (hσ : ∀ x ∈ K, σ x = σ' x)
    (e : ρ'.Equiv σ') (hρadm : IsAdmissible ρ) (hσadm : IsAdmissible σ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Surjective f := by
  intro w
  obtain ⟨J, hw⟩ := hσadm.1 w
  let L := J ⊓ K
  have hwL : w ∈ fixedVectors σ L.toSubgroup := fun x => hw ⟨x, x.property.1⟩
  have hρL := fixedVectors_eq_of_action_eq L.toSubgroup
    (fun x hx => hρ x hx.2)
  have hσL := fixedVectors_eq_of_action_eq L.toSubgroup
    (fun x hx => hσ x hx.2)
  have hrank : Module.finrank ℂ (fixedVectors ρ L.toSubgroup) =
      Module.finrank ℂ (fixedVectors σ L.toSubgroup) :=
    (congrArg (fun U : Submodule ℂ V => Module.finrank ℂ U) hρL).trans
      ((fixedVectorsEquiv e L.toSubgroup).finrank_eq.trans
        (congrArg (fun U : Submodule ℂ W => Module.finrank ℂ U) hσL).symm)
  let _ : FiniteDimensional ℂ (fixedVectors ρ L.toSubgroup) := hρadm.2 L
  let _ : FiniteDimensional ℂ (fixedVectors σ L.toSubgroup) := hσadm.2 L
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp
    (fixedVectorsMap_injective f hf L.toSubgroup)
  obtain ⟨v, hv⟩ := hs ⟨w, hwL⟩
  exact ⟨v, congrArg Subtype.val hv⟩

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor

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
  leviLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "G₀" => RationalPoint F G.X

include hG hK hψK in
/-- The actual coefficient fiber is admissible for an admissible inducing twist. -/
theorem coefficientFiber_isAdmissible (z : X) (hA : (twistObject χ z A).IsAdmissible) :
    (coefficientFiber χ ψ hψ A z).IsAdmissible := by
  let _ := quotientCompact K hK ψ hψK
  let B := twistObject χ z A
  let hw := commonDecomposition χ ψ hψ
  let hU := radical_isClosed ψ
  have hδ := DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
  have hdual : B.contragredient.IsAdmissible :=
    (SmoothRep.isAdmissible_contragredient_iff (compactOpenCofinal_of_nonarchimedean (levi χ))
      B).mpr hA
  have hind (C : SmoothRep.{0, u, uV} ℂ (levi χ)) (hC : C.IsAdmissible) :
      ((DynamicNormalization.leviTwistedInductionFunctor hw hU).obj C).IsAdmissible :=
    isAdmissible_of_equiv
      (SmoothRep.equivOfIso ((DynamicNormalization.normalizedInductionLeviTwistIso hw hU hδ).app C))
      (normalizedInductionFunctor_obj_isAdmissible hw hU (commonProjection_continuous χ ψ hψ)
        C hC)
  have hprod : IsAdmissible (BinaryTensor.external
      ((DynamicNormalization.leviTwistedInductionFunctor hw hU).obj B).representation
      ((DynamicNormalization.leviTwistedInductionFunctor hw hU).obj B.contragredient).representation) :=
    TwoFactorExternalTensor.admissible _ _ (hind B hA) (hind B.contragredient hdual)
  exact isAdmissible_of_equiv (tensorEquiv χ hG K hK ψ hψ hψK A z) hprod

private theorem compactTensorRepresentation_eq_of_mem_prod (z w : X)
    (g : G₀ × G₀) (hg : g ∈ K.prod K) :
    compactTensorRepresentation χ hG K hK ψ hψ hψK A z g =
      compactTensorRepresentation χ hG K hK ψ hψ hψK A w g := by
  let k : K × K := (⟨g.1, hg.1⟩, ⟨g.2, hg.2⟩)
  exact DFunLike.congr_fun ((compactTensorRepresentation_comp χ hG K hK ψ hψ hψK A z).trans
    (compactTensorRepresentation_comp χ hG K hK ψ hψ hψK A w).symm) k

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "V₀" => coefficientFiber χ ψ hψ A
local notation "V₁" => coefficientFiber χ ψ' hψ' A
local notation "ρ₀" => compactTensorRepresentation χ hG K hK ψ hψ hψK A
local notation "ρ₁" => compactTensorRepresentation χ hG K hK ψ' hψ' hψ'K A
local notation "E₀" => compactTensorRepresentationEquiv χ hG K hK ψ hψ hψK A
local notation "E₁" => compactTensorRepresentationEquiv χ hG K hK ψ' hψ' hψ'K A

/-- One genuine generic comparison equates the dimensions of the fixed spaces
at every parameter. An injective actual intertwiner is then bijective. -/
theorem comparison_bijective_of_injective (w : D) (z : X)
    (hA : (twistObject χ z A).IsAdmissible)
    (T : (V₀ z).representation.IntertwiningMap (V₁ z).representation)
    (hT : Function.Injective T) :
    Function.Bijective T := by
  let e := (genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q w).ofBijective
    (genericComparison_bijective χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q w)
  let e' : (ρ₀ w.val).Equiv (ρ₁ w.val) :=
    (E₀ w.val).symm.trans (e.trans (E₁ w.val))
  let Tc : (ρ₀ z).IntertwiningMap (ρ₁ z) :=
    (E₁ z).toIntertwiningMap.comp (T.comp (E₀ z).symm.toIntertwiningMap)
  have hinj : Function.Injective Tc := (E₁ z).injective.comp (hT.comp (E₀ z).symm.injective)
  have h₀ : IsAdmissible (ρ₀ z) := isAdmissible_of_equiv (E₀ z)
    (coefficientFiber_isAdmissible χ hG A K hK ψ hψ hψK z hA)
  have h₁ : IsAdmissible (ρ₁ z) := isAdmissible_of_equiv (E₁ z)
    (coefficientFiber_isAdmissible χ hG A K hK ψ' hψ' hψ'K z hA)
  have hs := surjective_of_generic_fixedVectors (K.prod K)
    (compactTensorRepresentation_eq_of_mem_prod χ hG A K hK ψ hψ hψK z w.val)
    (compactTensorRepresentation_eq_of_mem_prod χ hG A K hK ψ' hψ' hψ'K z w.val)
    e' h₀ h₁ Tc hinj
  refine ⟨hT, fun v => ?_⟩
  obtain ⟨u, hu⟩ := hs (E₁ z v)
  exact ⟨(E₀ z).symm u, (E₁ z).injective hu⟩

/-- Bundle a bijective actual comparison while keeping its original operator. -/
def comparisonEquivOfInjective (w : D) (z : X)
    (hA : (twistObject χ z A).IsAdmissible)
    (T : (V₀ z).representation.IntertwiningMap (V₁ z).representation)
    (hT : Function.Injective T) :
    (V₀ z).representation.Equiv (V₁ z).representation :=
  T.ofBijective (comparison_bijective_of_injective χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    p q w z hA T hT)

@[simp]
theorem comparisonEquivOfInjective_apply (w : D) (z : X)
    (hA : (twistObject χ z A).IsAdmissible)
    (T : (V₀ z).representation.IntertwiningMap (V₁ z).representation)
    (hT : Function.Injective T)
    (v : coefficientFiber χ ψ hψ A z) :
    comparisonEquivOfInjective χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q w z hA T hT v =
      T v := rfl

variable
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)

local notation "B₀" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK
local notation "B₁" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ' hψ' hψ'K

/-- Preservation of the exact positive formal-degree form upgrades the actual
unitary intertwiner to a bijective map on the coefficient fibers. -/
theorem comparison_bijective_of_preservesFormalDegreeForm
    (w : D) (z : unitaryUnramifiedCharacters (normCharacters χ))
    (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ')
    (hform : ∀ v v', (B₁ z).inner (T z v) (T z v') = (B₀ z).inner v v') :
    Function.Bijective (T z) :=
  comparison_bijective_of_injective χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q w
    (unitaryParameter χ z) (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1
    (T z) ((B₀ z).injective_of_inner_map (B₁ z) (T z) hform)

end Langlands.Plancherel.ActualCommonLeviV3
