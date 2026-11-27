import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericPoles
import Langlands.Representation.Plancherel.ActualCommonLeviCompactNorm

/-! # Norms of pure compact tensors in the common-Levi comparison -/

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction CompactInduction HarishChandraSchwartz
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviIwasawa

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
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : rationalPoints G, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))

set_option hygiene false in
local notation "d" => commonDecomposition χ ψ hψ
set_option hygiene false in
local notation "hU" => radical_isClosed ψ
set_option hygiene false in
local notation "hP" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
set_option hygiene false in
local notation "hr" => commonProjection_continuous χ ψ hψ
set_option hygiene false in
local notation "hδ" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
set_option hygiene false in
local notation "hPK" => iwasawa_sets K ψ hψK
set_option hygiene false in
local notation "hmod" => common_modularCharacter χ hG ψ hψ
set_option hygiene false in
local notation "V" => compactFiber χ K ψ hψ A
local notation "E" z => compactTensorEquiv χ hG K hK ψ hψ hψK A z
local notation "T" => compactProductTensorEquiv χ hG A K hK ψ hψ hψK
local notation "Xt" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "Vf" => CompactInductionPicture d K A
local notation "Vd" => CompactInductionPicture d K A.contragredient
local notation "hcof" => compactOpenCofinal_of_nonarchimedean (levi χ)

private theorem compactProductTensorEquiv_tmul_eval (v : Vf) (ℓ : Vd)
    (k : K.prod K) :
    eval _ _ (T (v ⊗ₜ[ℂ] ℓ)) k =
      eval _ _ v ⟨k.1.1, k.2.1⟩ ⊗ₜ[ℂ] eval _ _ ℓ ⟨k.1.2, k.2.2⟩ := by
  let z : Xt := 1
  obtain ⟨f, rfl⟩ := (compactEquiv χ hG K hK ψ hψ hψK z A).surjective v
  obtain ⟨m, rfl⟩ := (dualCompactEquiv χ hG K hK ψ hψ hψK A z).surjective ℓ
  rw [← compactTensorEquiv_tmul χ hG K hK ψ hψ hψK A z f m,
    compactProductTensorEquiv_compactTensorEquiv]
  have hs := compactProductRestriction_eval χ hG A K hK ψ hψ hψK z
    (tensorEquiv χ hG K hK ψ hψ hψK A z (f ⊗ₜ[ℂ] m)) k
  let := quotientCompact K hK ψ hψK
  have he := leviNormalizedProductInductionTensorEquiv_tmul_eval d d hU hU hδ hδ
    (twistObject χ z A) (twistObject χ z A).contragredient f m
    (k : rationalPoints G × rationalPoints G)
  exact hs.trans ((congrArg (productCompactTwistTensorEquiv (leviNormCharacters χ)
    (parameterTransport χ z) A) he).trans rfl)

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)

local notation "M" => compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi
local notation "deg" => representationFormalDegree C hC qMeasure hcof hsq hi

set_option backward.isDefEq.respectTransparency.types false in
/-- The norm of an actual compact pure tensor is the product of the two
probability norms times the inverse square root of the prescribed formal degree. -/
theorem compactFormalDegreeModel_norm_tmul
    (b : InvariantPositiveForm A.representation) (v : Vf) (ℓ : Vd) :
    ‖M (v ⊗ₜ[ℂ] ℓ)‖ = Real.sqrt deg⁻¹ *
      (‖compactNormModel χ hG A K hK ψ hψ hψK b v‖ *
        ‖compactNormModel χ hG A.contragredient K hK ψ hψ hψK
          (dualInvariantForm b hcof hsq.1) ℓ‖) := by
  let v₁ := compactNormModel χ hG A K hK ψ hψ hψK b v
  let ℓ₁ := compactNormModel χ hG A.contragredient K hK ψ hψ hψK
    (dualInvariantForm b hcof hsq.1) ℓ
  have hinner : inner ℂ (M (v ⊗ₜ[ℂ] ℓ)) (M (v ⊗ₜ[ℂ] ℓ)) =
      (deg : ℂ)⁻¹ * (inner ℂ v₁ v₁ * inner ℂ ℓ₁ ℓ₁) := by
    change (formalDegreeFixedProductCompactForm d hU hP K hK hPK (ambient_modularCharacter hG)
      hmod A hcof C hC qMeasure hsq hi).inner (T (v ⊗ₜ[ℂ] ℓ)) (T (v ⊗ₜ[ℂ] ℓ)) = _
    rw [formalDegreeFixedProductCompactForm_inner_integral d hU hP K hK hPK
      (ambient_modularCharacter hG) hmod A hcof C hC qMeasure hsq hi b]
    change _ = (deg : ℂ)⁻¹ *
      (inner ℂ (compactNormModel χ hG A K hK ψ hψ hψK b v)
        (compactNormModel χ hG A K hK ψ hψ hψK b v) *
       inner ℂ (compactNormModel χ hG A.contragredient K hK ψ hψ hψK
         (dualInvariantForm b hcof hsq.1) ℓ)
        (compactNormModel χ hG A.contragredient K hK ψ hψ hψK
          (dualInvariantForm b hcof hsq.1) ℓ))
    rw [compactNormModel_inner, compactNormModel_inner]
    congr 1
    let f (k : K) : ℂ := b.inner (eval _ _ v k) (eval _ _ v k)
    let g (k : K) : ℂ :=
      (dualInvariantForm b hcof hsq.1).inner
        (eval ((parabolic ψ).subgroupOf K) (compactPictureInducingRepresentation d K A.contragredient) ℓ k)
        (eval ((parabolic ψ).subgroupOf K) (compactPictureInducingRepresentation d K A.contragredient) ℓ k)
    change _ = (∫ k, f k ∂measure K hK) * (∫ k, g k ∂measure K hK)
    refine (integral_congr_ae (ae_of_all _ fun k => ?_)).trans
      (integral_prod_mul f g)
    let kk : K.prod K := ⟨((k.1 : rationalPoints G), (k.2 : rationalPoints G)),
      k.1.property, k.2.property⟩
    let Hf := coefficientTensorInvariantForm A hcof hsq.1 b
    have hk := compactProductTensorEquiv_tmul_eval χ hG A K hK ψ hψ hψK v ℓ kk
    exact (congrArg₂ Hf.inner hk hk).trans
      (coefficientTensorInvariantForm_inner_tmul A hcof hsq.1 b _ _ _ _)
  change ‖M (v ⊗ₜ[ℂ] ℓ)‖ = Real.sqrt deg⁻¹ * (‖v₁‖ * ‖ℓ₁‖)
  have numeric (a r s : ℝ) :
      (a : ℂ)⁻¹ * ((r : ℂ) ^ 2 * (s : ℂ) ^ 2) = ((a⁻¹ * (r ^ 2 * s ^ 2) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  have hnum := (congrArg₂ (fun x y : ℂ => (deg : ℂ)⁻¹ * (x * y))
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v₁) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ℓ₁)).trans
    (numeric deg ‖v₁‖ ‖ℓ₁‖)
  calc
    _ = Real.sqrt (deg⁻¹ * (‖v₁‖ ^ 2 * ‖ℓ₁‖ ^ 2)) :=
      (norm_eq_sqrt_re_inner (𝕜 := ℂ) _).trans
        (congrArg (fun x : ℂ => Real.sqrt x.re) (hinner.trans hnum))
    _ = _ := by
      rw [Real.sqrt_mul (inv_nonneg.mpr (representationFormalDegree_pos C hC qMeasure hcof hsq hi).le),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : rationalPoints G, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (gData : GenericComparisonData χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)

local notation "M'" => compactFormalDegreeModel χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi
local notation "pF" => gData.forward
local notation "qR" => gData.reverse
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 5000000 in
/-- The actual generic compact comparison, represented by the two continued
standard operators, preserves the fixed norms on the unitary locus. -/
theorem compactComparison_norm_eq
    (z : Xu) (hz : unitaryParameter χ z ∈ D) (v : V) :
    ‖M' (J ⟨unitaryParameter χ z, hz⟩ v)‖ = ‖M v‖ := by
  let w := unitaryParameter χ z
  let wz : D := ⟨w, hz⟩
  let x := (E w).symm v
  let y := genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR wz x
  let E' := compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A w
  have hv : (E w) x = v := (E w).apply_symm_apply v
  have hJ : E' y = J wz v :=
    (compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR wz x).trans
      (congrArg (J wz) hv)
  have hinner : inner ℂ (M' (E' y)) (M' (E' y)) = inner ℂ (M ((E w) x)) (M ((E w) x)) :=
    (compactFormalDegreeModel_inner χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi z y y).trans
      (((genericComparison_preserves_unitary χ hG A C hC qMeasure K hK ψ hψ hψK
        ψ' hψ' hψ'K gData hsq hi z hz).2 x x).trans
        (compactFormalDegreeModel_inner χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi z x x).symm)
  calc
    ‖M' (J wz v)‖ = ‖M' (E' y)‖ := congrArg (fun a => ‖M' a‖) hJ.symm
    _ = ‖M ((E w) x)‖ := (norm_eq_sqrt_re_inner (𝕜 := ℂ) (M' (E' y))).trans
      ((congrArg (fun a : ℂ => Real.sqrt a.re) hinner).trans
        (norm_eq_sqrt_re_inner (𝕜 := ℂ) (M ((E w) x))).symm)
    _ = ‖M v‖ := congrArg (fun a => ‖M a‖) hv

include hi in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse comparison preserves the product of the two compact
probability norms on pure tensors. -/
theorem compactComparison_inverse_product_norm
    (b : InvariantPositiveForm A.representation)
    (z : Xu) (hz : unitaryParameter χ z ∈ D)
    (v₀ : Vf) (v₁ : CompactInductionPicture (commonDecomposition χ ψ' hψ') K A)
    (ℓ : CompactInductionPicture (commonDecomposition χ ψ' hψ') K A.contragredient)
    (hv : (pF).presentation.continuedOperator ⟨unitaryParameter χ z, hz.choose.1⟩ v₀ = v₁) :
    ‖compactNormModel χ hG A K hK ψ hψ hψK b v₀‖ *
      ‖compactNormModel χ hG A.contragredient K hK ψ hψ hψK (dualInvariantForm b hcof hsq.1)
        ((qR).presentation.continuedOperator ⟨(unitaryParameter χ z)⁻¹, hz.choose.2⟩ ℓ)‖ =
    ‖compactNormModel χ hG A K hK ψ' hψ' hψ'K b v₁‖ *
      ‖compactNormModel χ hG A.contragredient K hK ψ' hψ' hψ'K
        (dualInvariantForm b hcof hsq.1) ℓ‖ := by
  let w : D := ⟨unitaryParameter χ z, hz⟩
  let Q := (qR).presentation.continuedOperator ⟨(unitaryParameter χ z)⁻¹, hz.choose.2⟩
  have hmap : J w (v₀ ⊗ₜ[ℂ] Q ℓ) = v₁ ⊗ₜ[ℂ] ℓ := by
    change (TensorProduct.map ((pF).presentation.continuedOperator
      ⟨unitaryParameter χ z, hz.choose.1⟩)
      (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR w))
      (v₀ ⊗ₜ[ℂ] Q ℓ) = _
    rw [TensorProduct.map_tmul, hv]
    exact congrArg (TensorProduct.tmul ℂ v₁)
      (compactReverseInverse_left χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A pF qR w ℓ)
  have hh := compactComparison_norm_eq χ hG A K hK ψ hψ hψK
    C hC qMeasure hsq hi ψ' hψ' hψ'K gData z hz (v₀ ⊗ₜ[ℂ] Q ℓ)
  change ‖M' (J w (v₀ ⊗ₜ[ℂ] Q ℓ))‖ = ‖M (v₀ ⊗ₜ[ℂ] Q ℓ)‖ at hh
  rw [hmap, compactFormalDegreeModel_norm_tmul χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi b,
    compactFormalDegreeModel_norm_tmul χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi b] at hh
  exact mul_left_cancel₀
    (Real.sqrt_pos.2 (inv_pos.2 (representationFormalDegree_pos C hC qMeasure hcof hsq hi))).ne'
    hh.symm

end Langlands.Plancherel.ActualCommonLeviV3
