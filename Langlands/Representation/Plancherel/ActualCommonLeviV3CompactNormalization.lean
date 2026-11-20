import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.FormalDegreeFixedCompactForm
import Langlands.Representation.Unitary.Completion

/-! # Fixed compact normalization for the actual common-Levi tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV uI

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor
open HarishChandraSchwartz

section ProductRestriction

variable {H₀ : Type u} [Group H₀] [TopologicalSpace H₀] [NonarchimedeanGroup H₀]
  [LocallyCompactSpace H₀] [SecondCountableTopology H₀]
  {P M U : Subgroup H₀} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (h : IsSemidirectDecomposition P M U) (K₀ : OpenSubgroup H₀)
  (hP₀ : IsClosed (P : Set H₀)) (hK₀ : IsCompact (K₀ : Set H₀))
  (hν₀ : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hU₀ : IsClosed (U : Set H₀)) (huni : IsUnimodularModulus U hU₀)
  (hPK₀ : ∀ g : H₀, ∃ p : P, ∃ k : K₀, g = (p : H₀) * (k : H₀))
  (t : unramifiedCharacters ν) (A₀ : SmoothRep.{0, u, uV} ℂ M)

set_option quotPrecheck false in
local notation "At" => A₀.twist t.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν t)
set_option quotPrecheck false in
local notation "ρt" => leviInflatedInducingRepresentation
  (h.prod h) (hU₀.prod hU₀) (productLeviObject At (At).contragredient)

private def productRestriction :
    leviProductInducedCoefficientObject h hU₀ At ≃ₗ[ℂ] ProductInducedCompactPicture h K₀ A₀ :=
  (productInducedCoefficientLeviEquiv h hU₀ At huni).symm.toLinearEquiv.trans
    (productInducedCompactEquiv ν h K₀ hP₀ hK₀ hν₀ hr hU₀ hPK₀ t A₀).toLinearEquiv

private theorem productRestriction_eval (v : leviProductInducedCoefficientObject h hU₀ At)
    (k : K₀.prod K₀) :
    eval _ _ (productRestriction ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v) k =
      productCompactTwistTensorEquiv ν t A₀ (eval (P.prod P) ρt v (k : H₀ × H₀)) := by
  refine (productInducedCompactEquiv_eval ν h K₀ hP₀ hK₀ hν₀ hr hU₀ hPK₀ t A₀
    ((productInducedCoefficientLeviEquiv h hU₀ At huni).symm v) k).trans ?_
  exact congrArg (productCompactTwistTensorEquiv ν t A₀)
    (normalizedInductionLeviEquiv_symm_eval (h.prod h) (hU₀.prod hU₀)
      (isUnimodularModulus_prod hU₀ hU₀ huni huni) (productLeviObject At (At).contragredient)
      v (k : H₀ × H₀))

private theorem productRestriction_pairing (v : leviProductInducedCoefficientObject h hU₀ At)
    (k : K₀.prod K₀) :
    TensorProduct.lift (smoothDualPairing A₀.representation).flip
        (eval _ _ (productRestriction ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v) k) =
      TensorProduct.lift (smoothDualPairing (At).representation).flip
        (eval (P.prod P) ρt v (k : H₀ × H₀)) := by
  let value : CoefficientTensor At := Induction.eval (P.prod P) ρt v (k : H₀ × H₀)
  have he := productRestriction_eval ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v k
  have hp := productCompactTwistTensorEquiv_pairing ν t A₀ value
  exact (congrArg (TensorProduct.lift (smoothDualPairing A₀.representation).flip) he).trans hp

variable [T2Space H₀] [MeasurableSpace H₀] [BorelSpace H₀] [LocallyCompactSpace P]
  (hsets : ∀ g : H₀, ∃ p ∈ P, ∃ k ∈ K₀, g = p * k)
  (hmodH : ∀ g : H₀, Measure.modularCharacter g = 1)
  (hmod : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU₀ P h.le_normalizer p : ℝ≥0))

private theorem productRestriction_coefficient_one (hadm : (At).IsAdmissible)
    (v : leviProductInducedCoefficientObject h hU₀ At) :
    CompactInduction.leviCoefficientMap h hU₀ At K₀ huni hK₀ hP₀ hr hsets hmodH hmod hadm v 1 =
      ∫ k : K₀, TensorProduct.lift (smoothDualPairing A₀.representation).flip
        (eval _ _ (productRestriction ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v)
          (⟨((k : H₀), (k : H₀)), k.property, k.property⟩ : K₀.prod K₀))
        ∂CompactInduction.measure K₀ hK₀ := by
  refine (CompactInduction.leviCoefficientMap_integral h hU₀ At K₀ huni hK₀ hP₀ hr
    hsets hmodH hmod hadm v 1).trans ?_
  apply integral_congr_ae
  filter_upwards [] with k
  let kk : K₀.prod K₀ := ⟨((k : H₀), (k : H₀)), k.property, k.property⟩
  change TensorProduct.lift (smoothDualPairing (At).representation).flip
    (eval (P.prod P) ρt v ((k : H₀) * 1, (k : H₀))) =
    TensorProduct.lift (smoothDualPairing A₀.representation).flip
      (eval _ _ (productRestriction ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v) kk)
  rw [mul_one]
  exact (productRestriction_pairing ν h K₀ hP₀ hK₀ hν₀ hr hU₀ huni hPK₀ t A₀ v kk).symm

end ProductRestriction

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

local notation "H" => RationalPoint F G.X
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "d" => commonDecomposition χ ψ hψ
local notation "hU" => radical_isClosed ψ
local notation "hUmod" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hP" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hpr" => commonProjection_continuous χ ψ hψ
set_option quotPrecheck false in
local notation "hν" => fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
  (parameterHomeomorph χ).symm.continuous
local notation "V" => compactFiber χ K ψ hψ A
local notation "W" => ProductInducedCompactPicture d K A
local notation "Az" z => twistObject χ z A
set_option quotPrecheck false in
local notation "ρz" z => leviInflatedInducingRepresentation
  (IsSemidirectDecomposition.prod d d) (IsClosed.prod hU hU)
  (productLeviObject (Az z) (Az z).contragredient)

attribute [local instance] ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

/-- The actual positive-Levi section restricted in the fixed compact product
picture, transporting the smooth-dual twist by its underlying functional. -/
def compactProductRestriction (z : X) : coefficientFiber χ ψ hψ A z ≃ₗ[ℂ] W :=
  productRestriction (leviNormCharacters χ) d K hP hK hν hpr hU hUmod hψK
    (parameterTransport χ z) A

theorem compactProductRestriction_eval (z : X) (v : coefficientFiber χ ψ hψ A z)
    (k : K.prod K) :
    eval _ _ (compactProductRestriction χ hG A K hK ψ hψ hψK z v) k =
      productCompactTwistTensorEquiv (leviNormCharacters χ) (parameterTransport χ z) A
        (eval ((parabolic ψ).prod (parabolic ψ)) (ρz z) v (k : H × H)) :=
  productRestriction_eval (leviNormCharacters χ) d K hP hK hν hpr hU hUmod hψK
    (parameterTransport χ z) A v k

private theorem compactProductRestriction_tensor (z : X)
    (f : (DynamicNormalization.leviTwistedInductionFunctor d hU).obj (Az z))
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor d hU).obj (Az z).contragredient)
    (k : K.prod K) :
    eval _ _ (compactProductRestriction χ hG A K hK ψ hψ hψK z
      (tensorEquiv χ hG K hK ψ hψ hψK A z (f ⊗ₜ[ℂ] ℓ))) k =
      (eval _ _ (compactEquiv χ hG K hK ψ hψ hψK z A f) ⟨k.1.1, k.2.1⟩) ⊗ₜ[ℂ]
        (eval _ _ (dualCompactEquiv χ hG K hK ψ hψ hψK A z ℓ) ⟨k.1.2, k.2.2⟩) := by
  let := quotientCompact K hK ψ hψK
  have he := leviNormalizedProductInductionTensorEquiv_tmul_eval d d hU hU hUmod hUmod
    (Az z) (Az z).contragredient f ℓ (k : H × H)
  exact (compactProductRestriction_eval χ hG A K hK ψ hψ hψK z
      (tensorEquiv χ hG K hK ψ hψ hψK A z (f ⊗ₜ[ℂ] ℓ)) k).trans
    ((congrArg (productCompactTwistTensorEquiv (leviNormCharacters χ) (parameterTransport χ z) A)
      he).trans rfl)

/-- Identify the fixed tensor and product-section carriers by transporting
through one parameter. Its evaluations are pointwise tensors. -/
def compactProductTensorEquiv : V ≃ₗ[ℂ] W :=
  (compactTensorEquiv χ hG K hK ψ hψ hψK A 1).symm.trans
    (compactProductRestriction χ hG A K hK ψ hψ hψK 1)

private theorem productRestriction_after_tensor_symm_tmul (z : X)
    (v : CompactInductionPicture d K A)
    (w : CompactInductionPicture d K A.contragredient) (k : K.prod K) :
    eval _ _ (compactProductRestriction χ hG A K hK ψ hψ hψK z
      ((compactTensorEquiv χ hG K hK ψ hψ hψK A z).symm (v ⊗ₜ[ℂ] w))) k =
      (eval _ _ v ⟨k.1.1, k.2.1⟩) ⊗ₜ[ℂ] (eval _ _ w ⟨k.1.2, k.2.2⟩) := by
  obtain ⟨f, rfl⟩ := (compactEquiv χ hG K hK ψ hψ hψK z A).surjective v
  obtain ⟨ℓ, rfl⟩ := (dualCompactEquiv χ hG K hK ψ hψ hψK A z).surjective w
  rw [← compactTensorEquiv_tmul χ hG K hK ψ hψ hψK A z f ℓ,
    LinearEquiv.symm_apply_apply]
  exact compactProductRestriction_tensor χ hG A K hK ψ hψ hψK z f ℓ k

/-- At every parameter the exact restriction in the product picture is the
fixed comparison composed with the actual theorem's compact tensor map. -/
theorem compactProductTensorEquiv_compactTensorEquiv (z : X)
    (v : coefficientFiber χ ψ hψ A z) :
    compactProductTensorEquiv χ hG A K hK ψ hψ hψK
      (compactTensorEquiv χ hG K hK ψ hψ hψK A z v) =
      compactProductRestriction χ hG A K hK ψ hψ hψK z v := by
  obtain ⟨w, rfl⟩ := (compactTensorEquiv χ hG K hK ψ hψ hψK A z).symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  induction w using TensorProduct.inductionOn with
  | tmul v w =>
    apply Subtype.ext
    apply Subtype.ext
    funext k
    exact (productRestriction_after_tensor_symm_tmul χ hG A K hK ψ hψ hψK 1 v w k).trans
      (productRestriction_after_tensor_symm_tmul χ hG A K hK ψ hψ hψK z v w k).symm
  | add v w hv hw => simp only [map_add, hv, hw]

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)

local notation "hPK" => iwasawa_sets K ψ hψK
local notation "hmodG" => ambient_modularCharacter hG
local notation "hmodP" => common_modularCharacter χ hG ψ hψ
local notation "hcof" => compactOpenCofinal_of_nonarchimedean (levi χ)
local notation "B" => CompactInduction.formalDegreeFixedProductCompactForm
  d hU hP K hK hPK hmodG hmodP A hcof C hC qMeasure hsq hi

/-- Put the fixed tensor in the normed carrier of the degree-normalized
compact product form for the same central quotient Haar measure. -/
def compactFormalDegreeModel : V ≃ₗ[ℂ] InvariantPositiveForm.NormedCarrier B :=
  (compactProductTensorEquiv χ hG A K hK ψ hψ hψK).trans
    (InvariantPositiveForm.toNormedCarrier B)

/-- Every unitary twist has its exact degree-normalized form in the same
compact normed model. -/
theorem compactFormalDegreeModel_inner (z : Xu)
    (v w : coefficientFiber χ ψ hψ A (unitaryParameter χ z)) :
    inner ℂ
      (compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi
        (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) v))
      (compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi
        (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) w)) =
      (formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK z).inner v w := by
  change (B).inner
    (compactProductTensorEquiv χ hG A K hK ψ hψ hψK
      (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) v))
    (compactProductTensorEquiv χ hG A K hK ψ hψ hψK
      (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) w)) = _
  rw [compactProductTensorEquiv_compactTensorEquiv, compactProductTensorEquiv_compactTensorEquiv]
  exact CompactInduction.formalDegreeProductInducedCompactEquiv_inner
    d hU hP K hK hPK hmodG hmodP A hcof C hC qMeasure hsq hi (leviNormCharacters χ)
    hν hpr (parameterTransport χ (unitaryParameter χ z)) (unitary_parameter_norm χ z)
    ((productInducedCoefficientLeviEquiv d hU (Az (unitaryParameter χ z)) hUmod).symm v)
    ((productInducedCoefficientLeviEquiv d hU (Az (unitaryParameter χ z)) hUmod).symm w)

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
private theorem coefficientMap_one_integral (z : Xu)
    (v : coefficientFiber χ ψ hψ A (unitaryParameter χ z)) :
    coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK z v 1 =
      ∫ k : K, TensorProduct.lift (smoothDualPairing A.representation).flip
        (eval _ _ (compactProductRestriction χ hG A K hK ψ hψ hψK (unitaryParameter χ z) v)
          (⟨((k : H), (k : H)), k.property, k.property⟩ : K.prod K))
        ∂CompactInduction.measure K hK :=
  productRestriction_coefficient_one (leviNormCharacters χ) d K hP hK hν hpr hU hUmod hψK
    (parameterTransport χ (unitaryParameter χ z)) A hPK hmodG hmodP
    (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1 v

/-- Coefficient evaluation at the identity, transported through the actual
compact tensor equivalence at the trivial unitary parameter. -/
def compactCoefficientAtOne : V →ₗ[ℂ] ℂ :=
  (LocallyConstant.evalₗ ℂ (1 : H)).comp
    ((coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK 1).comp
      (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ 1)).symm.toLinearMap)

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
/-- The fixed functional computes the published coefficient at the identity
for every unitary twist, using the original compact probability. -/
theorem compactCoefficientAtOne_compactTensorEquiv (z : Xu)
    (v : coefficientFiber χ ψ hψ A (unitaryParameter χ z)) :
    compactCoefficientAtOne χ hG A K hK ψ hψ hψK C hC qMeasure hsq
        (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) v) =
      coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK z v 1 := by
  let E := compactTensorEquiv χ hG K hK ψ hψ hψK A
  let v₁ := (E (unitaryParameter χ 1)).symm (E (unitaryParameter χ z) v)
  change coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK 1 v₁ 1 = _
  have h := compactProductTensorEquiv_compactTensorEquiv χ hG A K hK ψ hψ hψK
    (unitaryParameter χ 1) v₁
  change compactProductTensorEquiv χ hG A K hK ψ hψ hψK
    (E (unitaryParameter χ 1) ((E (unitaryParameter χ 1)).symm (E (unitaryParameter χ z) v))) =
    compactProductRestriction χ hG A K hK ψ hψ hψK (unitaryParameter χ 1) v₁ at h
  rw [LinearEquiv.apply_symm_apply, compactProductTensorEquiv_compactTensorEquiv] at h
  rw [coefficientMap_one_integral, coefficientMap_one_integral, ← h]

end Langlands.Plancherel.ActualCommonLeviV3
