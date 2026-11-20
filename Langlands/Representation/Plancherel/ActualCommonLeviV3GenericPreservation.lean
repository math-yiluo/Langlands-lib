import Langlands.Representation.Plancherel.ActualCommonLeviV3PreservationProof
import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement

/-! # The exact common-Levi generic tensor and compact probability duality -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel

open Aubert.General Induction

namespace CompactInduction

universe uG uV

variable {H : Type uG} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [T2Space H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {P M U : Subgroup H} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup H)
  (huni : IsUnimodularModulus U hU) (hK : IsCompact (K : Set H))
  (hP : IsClosed (P : Set H)) (hm : Continuous h.projection)
  (hPK : ∀ g : H, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hH : ∀ g : H, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

/-- Turn positive-Levi induction of the smooth dual into the smooth dual
of normalized induction using exactly the compact probability pairing. -/
def leviInducedSmoothDualEquiv :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient).representation.Equiv
    ((normalizedInductionFunctor h hU).obj A).contragredient.representation :=
  (normalizedInductionLeviEquiv h hU huni A.contragredient).symm.trans
    (integralDualEquiv h hU hP hm K hK hPK hH hδ A hA).symm

variable [CompactSpace (LeftQuotient P)]

/-- The exact coefficient-tensor equivalence sends a positive-Levi pure
tensor to the normalized vector tensored with its compactly paired dual. -/
theorem leviCoefficientTensorEquiv_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    leviCoefficientTensorEquiv h hU A K huni hK hP hm hPK hH hδ hA
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)) =
      (normalizedInductionLeviEquiv h hU huni A).symm f ⊗ₜ[ℂ]
        leviInducedSmoothDualEquiv h hU A K huni hK hP hm hPK hH hδ hA ℓ := by
  change coefficientTensorEquiv h hU A K hK hP hm hPK hH hδ hA
    ((productInducedCoefficientLeviEquiv h hU A huni).symm
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
        (f ⊗ₜ[ℂ] ℓ))) = _
  rw [productInducedCoefficientLeviEquiv_symm_tensor, externalInductionLeviEquiv_symm_tmul]
  change dualTensorEquiv h hU A K hK hP hm hPK hH hδ hA
    ((normalizedProductInductionTensorEquiv h h hU hU A A.contragredient).symm
      (normalizedProductInductionTensorEquiv h h hU hU A A.contragredient
        ((normalizedInductionLeviEquiv h hU huni A).symm f ⊗ₜ[ℂ]
          (normalizedInductionLeviEquiv h hU huni A.contragredient).symm ℓ))) = _
  rw [Representation.Equiv.symm_apply_apply]
  rfl

end CompactInduction

namespace ActualCommonLeviV3

universe u uV

open DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor
open CompactInduction

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

variable (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

local notation "Az" => twistObject χ z.val A
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
set_option quotPrecheck false in
local notation "I₀" => (normalizedInductionFunctor h₀ hU₀).obj Az
set_option quotPrecheck false in
local notation "I₁" => (normalizedInductionFunctor h₁ hU₁).obj Az
set_option quotPrecheck false in
local notation "I₀d" => (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (Az).contragredient
set_option quotPrecheck false in
local notation "I₁d" => (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj (Az).contragredient
local notation "e₀" => normalizedInductionLeviEquiv h₀ hU₀ hδ₀ Az
local notation "e₁" => normalizedInductionLeviEquiv h₁ hU₁ hδ₁ Az
set_option quotPrecheck false in
local notation "J" => ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p
  ⟨z.val, z.property.choose.1⟩
set_option quotPrecheck false in
local notation "R" => reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
  ⟨z.val, z.property.choose⟩
local notation "T" => genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
set_option quotPrecheck false in
local notation "iR" => reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az R z.property.choose_spec.2

/-- The exact generic forward standard operator, transported to the normalized
induction representations and made an equivalence by its genuine-locus witness. -/
def genericNormalizedForwardEquiv : (I₀).representation.Equiv (I₁).representation :=
  (e₀).trans (((J).ofBijective z.property.choose_spec.1).trans (e₁).symm)

local notation "e" => genericNormalizedForwardEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z

variable (hA : (twistObject χ z.val A).IsAdmissible)

local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "hPK₀" => iwasawa_sets K ψ hψK
local notation "hPK₁" => iwasawa_sets K ψ' hψ'K
local notation "hH" => ambient_modularCharacter hG
local notation "hmod₀" => common_modularCharacter χ hG ψ hψ
local notation "hmod₁" => common_modularCharacter χ hG ψ' hψ'
local notation "d₀" => leviInducedSmoothDualEquiv h₀ hU₀ Az K hδ₀ hK hP₀ hr₀ hPK₀ hH hmod₀ hA
local notation "d₁" => leviInducedSmoothDualEquiv h₁ hU₁ Az K hδ₁ hK hP₁ hr₁ hPK₁ hH hmod₁ hA
local notation "E₀" => leviCoefficientTensorEquiv h₀ hU₀ Az K hδ₀ hK hP₀ hr₀ hPK₀ hH hmod₀ hA
local notation "E₁" => leviCoefficientTensorEquiv h₁ hU₁ Az K hδ₁ hK hP₁ hr₁ hPK₁ hH hmod₁ hA

/-- If the bilinear adjunction has scale `r`, the original generic tensor is
transport by the forward equivalence and inverse pullback with that same scale.
The smooth-dual identifications use the specified compact Haar probability. -/
theorem genericComparison_coefficientTensor_of_scaledAdjunction
    (r : ℂ)
    (hadj : ∀ (f : I₀) (ℓ : I₁d),
      smoothDualPairing (I₁).representation (d₁ ℓ) (e f) =
        r * smoothDualPairing (I₀).representation (d₀ (R ℓ)) f)
    (v : coefficientFiber χ ψ hψ A z.val) :
    E₁ (T v) = r • coefficientTensorCongr e (E₀ v) := by
  have hdual (ℓ : I₀d) : d₁ (iR ℓ) = r • contragredientMap (e).symm.toIntertwiningMap (d₀ ℓ) := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    let f := (e).symm w
    have hf : e f = w := (e).apply_symm_apply w
    have hℓ : R (iR ℓ) = ℓ := reverseInducedDualInverse_apply h₀ h₁ hU₀ hU₁ Az Az
      R z.property.choose_spec.2 ℓ
    change smoothDualPairing (I₁).representation (d₁ (iR ℓ)) w =
      r * smoothDualPairing (I₀).representation (d₀ ℓ) f
    exact (congrArg (smoothDualPairing (I₁).representation (d₁ (iR ℓ))) hf.symm).trans
      ((hadj f (iR ℓ)).trans (congrArg (fun t : I₀d =>
        r * smoothDualPairing (I₀).representation (d₀ t) f) hℓ))
  let := quotientCompact K hK ψ hψK
  let := quotientCompact K hK ψ' hψ'K
  let E := tensorEquiv χ hG K hK ψ hψ hψK A z.val
  let v₀ := E.symm v
  let lhs := (E₁).toLinearMap.comp ((T).toLinearMap.comp E.toLinearMap)
  let rhs := r • (coefficientTensorCongr e).toLinearMap.comp ((E₀).toLinearMap.comp E.toLinearMap)
  have h : lhs = rhs := by
    apply TensorProduct.ext'
    intro f ℓ
    have hT := genericComparison_tmul χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z f ℓ
    have ht₀ := leviCoefficientTensorEquiv_tmul h₀ hU₀ Az K hδ₀ hK hP₀ hr₀ hPK₀ hH hmod₀ hA f ℓ
    have ht₁ := leviCoefficientTensorEquiv_tmul h₁ hU₁ Az K hδ₁ hK hP₁ hr₁ hPK₁ hH hmod₁ hA
      (J f) (iR ℓ)
    have he : (e₁).symm (J f) = e ((e₀).symm f) :=
      (congrArg (fun w => (e₁).symm (J w)) ((e₀).apply_symm_apply f)).symm
    let m := contragredientMap (e).symm.toIntertwiningMap (d₀ ℓ)
    have hpair : ((e₁).symm (J f) ⊗ₜ[ℂ] d₁ (iR ℓ) : CoefficientTensor I₁) =
        e ((e₀).symm f) ⊗ₜ[ℂ] (r • m) :=
      congrArg₂ (fun (w : I₁) (n : (I₁).contragredient) => w ⊗ₜ[ℂ] n) he (hdual ℓ)
    have hsmul : (e ((e₀).symm f) ⊗ₜ[ℂ] (r • m) : CoefficientTensor I₁) =
        r • (e ((e₀).symm f) ⊗ₜ[ℂ] m) :=
      TensorProduct.tmul_smul r _ _
    have hcongr : r • (e ((e₀).symm f) ⊗ₜ[ℂ] m : CoefficientTensor I₁) =
        r • coefficientTensorCongr e ((e₀).symm f ⊗ₜ[ℂ] d₀ ℓ) :=
      congrArg (fun w : CoefficientTensor I₁ => r • w)
        (coefficientTensorCongr_tmul e ((e₀).symm f) (d₀ ℓ)).symm
    change E₁ (T (E (f ⊗ₜ[ℂ] ℓ))) = r • coefficientTensorCongr e (E₀ (E (f ⊗ₜ[ℂ] ℓ)))
    refine (congrArg (E₁) hT).trans (ht₁.trans (hpair.trans (hsmul.trans (hcongr.trans ?_))))
    exact congrArg (fun w : CoefficientTensor I₀ => r • coefficientTensorCongr e w) ht₀.symm
  have h' : E₁ (T (E v₀)) = r • coefficientTensorCongr e (E₀ (E v₀)) :=
    congrArg (fun L : _ →ₗ[ℂ] _ => L v₀) h
  have hv : E v₀ = v := E.apply_symm_apply v
  exact (congrArg (fun x : coefficientFiber χ ψ hψ A z.val => E₁ (T x)) hv.symm).trans
    (h'.trans (congrArg (fun x : coefficientFiber χ ψ hψ A z.val =>
      r • coefficientTensorCongr e (E₀ x)) hv))

local notation "C₀" => leviCoefficientMap h₀ hU₀ Az K hδ₀ hK hP₀ hr₀ hPK₀ hH hmod₀ hA
local notation "C₁" => leviCoefficientMap h₁ hU₁ Az K hδ₁ hK hP₁ hr₁ hPK₁ hH hmod₁ hA

/-- The bilinear adjunction scale appears in every generic coefficient of
the original tensor. Scale one gives the exact coefficient identity. -/
theorem genericComparison_coefficient_of_scaledAdjunction
    (r : ℂ)
    (hadj : ∀ (f : I₀) (ℓ : I₁d),
      smoothDualPairing (I₁).representation (d₁ ℓ) (e f) =
        r * smoothDualPairing (I₀).representation (d₀ (R ℓ)) f)
    (v : coefficientFiber χ ψ hψ A z.val) :
    C₁ (T v) = r • (C₀ v) := by
  change coefficientTensorMap I₁ (E₁ (T v)) = r • coefficientTensorMap I₀ (E₀ v)
  have he := genericComparison_coefficientTensor_of_scaledAdjunction χ hG A K hK
    ψ hψ hψK ψ' hψ' hψ'K p q z hA r hadj v
  exact (congrArg (coefficientTensorMap I₁) he).trans
    ((map_smul (coefficientTensorMap I₁) r _).trans
      (congrArg (fun w : LocallyConstant (RationalPoint F G.X) ℂ => r • w)
        (coefficientTensorMap_congr e (E₀ v))))

variable
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC (twistObject χ z.val A).representation qMeasure)
  (hi : (twistObject χ z.val A).representation.IsIrreducible)

local notation "hcof" => compactOpenCofinal_of_nonarchimedean (levi χ)
local notation "hcofG" => compactOpenCofinal_of_nonarchimedean (RationalPoint F G.X)
local notation "B₀" =>
  leviFormalDegreeProductForm h₀ hU₀ Az K hδ₀ hK hP₀ hPK₀ hH hmod₀ hcof C hC qMeasure hsq hi
local notation "B₁" =>
  leviFormalDegreeProductForm h₁ hU₁ Az K hδ₁ hK hP₁ hPK₁ hH hmod₁ hcof C hC qMeasure hsq hi

/-- The actual generic comparison preserves the compact probability
coefficients and exact inverse-formal-degree forms from the unscaled
bilinear adjunction and positive similarity of the forward operator. -/
theorem genericComparison_preserves_of_adjunction_similitude
    (bz : InvariantPositiveForm (Az).representation) (a : ℝ) (ha : 0 < a)
    (hadj : ∀ (f : I₀) (ℓ : I₁d),
      smoothDualPairing (I₁).representation (d₁ ℓ) (e f) =
        smoothDualPairing (I₀).representation (d₀ (R ℓ)) f)
    (hsim : (invariantPositiveForm h₁ hU₁ hP₁ K hK hPK₁ hH hmod₁ Az bz).ofEquiv e =
      (invariantPositiveForm h₀ hU₀ hP₀ K hK hPK₀ hH hmod₀ Az bz).rescale a ha) :
    (∀ v : coefficientFiber χ ψ hψ A z.val, C₁ (T v) = C₀ v) ∧
    ∀ v w : coefficientFiber χ ψ hψ A z.val,
      (B₁).inner (T v) (T w) = (B₀).inner v w := by
  have ht (v : coefficientFiber χ ψ hψ A z.val) : E₁ (T v) = coefficientTensorCongr e (E₀ v) :=
    (genericComparison_coefficientTensor_of_scaledAdjunction χ hG A K hK ψ hψ hψK
      ψ' hψ' hψ'K p q z hA 1 (fun f ℓ => (hadj f ℓ).trans (one_mul _).symm) v).trans
      (one_smul _ _)
  exact (levi_preserves_of_coefficientTensor_similitude h₀ h₁ hU₀ hU₁ Az K hδ₀ hδ₁ hK
    hP₀ hP₁ hr₀ hr₁ hPK₀ hPK₁ hH hmod₀ hmod₁ hcof hcofG C hC qMeasure hsq hi T e bz a ha ht hsim).2

end ActualCommonLeviV3
end Langlands.Plancherel
