import Langlands.Representation.Plancherel.ActualCommonLeviTensor
import Langlands.Representation.Plancherel.RationalScalarCompositeInverse

/-! # Fixed compact carriers for the actual normalized tensor -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCompactTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor UnramifiedOperatorFamily

private theorem inverseTransport_left
    {V W X Y : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (R : W → V) (S : V → W) (hSR : ∀ w, S (R w) = w)
    (E₀ : V ≃ₗ[ℂ] X) (E₁ : W ≃ₗ[ℂ] Y) (Q : Y → X)
    (hsq : ∀ w, E₀ (R w) = Q (E₁ w)) (y : Y) :
    E₁ (S (E₀.symm (Q y))) = y := by
  have h := congrArg E₀.symm (hsq (E₁.symm y))
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at h
  rw [← h, hSR, LinearEquiv.apply_symm_apply]

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
  (hG : IsConnectedReductive G)
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
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'

/-- The fixed tensor of the two actual compact induction spaces. -/
abbrev compactFiber :=
  CompactInductionPicture h₀ K A ⊗[ℂ] CompactInductionPicture h₀ K A.contragredient

/-- Restrict the induced smooth dual after the functional-preserving inverse
parameter identification. -/
def dualCompactEquiv (z : unramifiedCharacters (normCharacters χ)) :
    (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
        (twistObject χ z A).contragredient ≃ₗ[ℂ]
      CompactInductionPicture h₀ K A.contragredient :=
  (dualInductionEquiv χ hG ψ hψ A z).toLinearEquiv.trans
    (compactEquiv χ hG K hK ψ hψ hψK z⁻¹ A.contragredient)

/-- The actual coefficient fiber is identified with the fixed tensor by the
published positive-Levi product equivalence and actual compact restrictions. -/
def compactTensorEquiv (z : unramifiedCharacters (normCharacters χ)) :
    coefficientFiber χ ψ hψ A z ≃ₗ[ℂ] compactFiber χ K ψ hψ A :=
  (tensorEquiv χ hG K hK ψ hψ hψK A z).toLinearEquiv.symm.trans
    (TensorProduct.congr (compactEquiv χ hG K hK ψ hψ hψK z A)
      (dualCompactEquiv χ hG K hK ψ hψ hψK A z))

@[simp]
theorem compactTensorEquiv_tmul (z : unramifiedCharacters (normCharacters χ))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (twistObject χ z A))
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (twistObject χ z A).contragredient) :
    compactTensorEquiv χ hG K hK ψ hψ hψK A z
        (tensorEquiv χ hG K hK ψ hψ hψK A z (f ⊗ₜ[ℂ] ℓ)) =
      compactEquiv χ hG K hK ψ hψ hψK z A f ⊗ₜ[ℂ]
        dualCompactEquiv χ hG K hK ψ hψ hψK A z ℓ := by
  change TensorProduct.congr _ _
    ((tensorEquiv χ hG K hK ψ hψ hψK A z).toLinearEquiv.symm
      ((tensorEquiv χ hG K hK ψ hψ hψK A z).toLinearEquiv (f ⊗ₜ[ℂ] ℓ))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.congr_tmul]

variable
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

/-- The original compact square for the actual forward continuation. -/
theorem forward_compact_square (z : p.regularRegion)
    (f : UnramifiedLeviInduction h₀ hU₀ (leviNormCharacters χ)
      (parameterTransport χ z.val) A) :
    compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A
        (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z f) =
      p.presentation.continuedOperator z
        (compactEquiv χ hG K hK ψ hψ hψK z.val A f) := by
  have h := congrArg (fun T => T (compactEquiv χ hG K hK ψ hψ hψK z.val A f))
    (ContinuedPair.operator_compact χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, Representation.IntertwiningMap.toLinearMap_apply] using h

/-- The reverse dual square identifies this actual operator, including the
inverse parameter and both canonical smooth-dual twist identifications. -/
theorem reverseDual_compact_square
    (z : regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj
      (twistObject χ z.val A).contragredient) :
    dualCompactEquiv χ hG K hK ψ hψ hψK A z.val
        (reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z ℓ) =
      q.presentation.continuedOperator ⟨z.val⁻¹, z.property.2⟩
        (dualCompactEquiv χ hG K hK ψ' hψ' hψ'K A z.val ℓ) := by
  change compactEquiv χ hG K hK ψ hψ hψK z.val⁻¹ A.contragredient
    ((dualInductionEquiv χ hG ψ hψ A z.val)
      ((dualInductionEquiv χ hG ψ hψ A z.val).symm
        (ContinuedPair.operator χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient q
          ⟨z.val⁻¹, z.property.2⟩ (dualInductionEquiv χ hG ψ' hψ' A z.val ℓ)))) = _
  rw [Representation.Equiv.apply_symm_apply]
  exact forward_compact_square χ hG K hK ψ' hψ' hψ'K ψ hψ hψK
    A.contragredient q ⟨z.val⁻¹, z.property.2⟩ _

section Generic

variable (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

local notation "Az" => twistObject χ z.val A
set_option quotPrecheck false in
local notation "Rz" => reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
  A p q ⟨z.val, z.property.choose⟩
set_option quotPrecheck false in
local notation "hz" => z.property.choose_spec.2
set_option quotPrecheck false in
local notation "Qz" => q.presentation.continuedOperator ⟨z.val⁻¹, z.property.choose.2⟩
local notation "E₀" => dualCompactEquiv χ hG K hK ψ hψ hψK A z.val
local notation "E₁" => dualCompactEquiv χ hG K hK ψ' hψ' hψ'K A z.val

/-- Transport the inverse of precisely the actual reverse dual operator to
the fixed compact carriers. This is not an independently chosen inverse. -/
def compactReverseInverse :
    CompactInductionPicture h₀ K A.contragredient →ₗ[ℂ]
      CompactInductionPicture h₁ K A.contragredient :=
  (E₁).toLinearMap.comp
    ((reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz).toLinearMap.comp
      (E₀).symm.toLinearMap)

/-- The transported map is a right inverse of the actual compact reverse
continuation. -/
theorem compactReverseInverse_right
    (ℓ : CompactInductionPicture h₀ K A.contragredient) :
    Qz (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z ℓ) = ℓ := by
  change Qz (E₁ (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz
    ((E₀).symm ℓ))) = ℓ
  rw [← reverseDual_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    A p q ⟨z.val, z.property.choose⟩,
    reverseInducedDualInverse_apply, LinearEquiv.apply_symm_apply]

/-- It is also a left inverse of that compact continuation. -/
theorem compactReverseInverse_left
    (ℓ : CompactInductionPicture h₁ K A.contragredient) :
    compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z (Qz ℓ) = ℓ := by
  exact inverseTransport_left Rz
    (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz)
    (reverseInducedDualInverse_apply_reverse h₀ h₁ hU₀ hU₁ Az Az Rz hz)
    E₀ E₁ Qz
    (reverseDual_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      A p q ⟨z.val, z.property.choose⟩) ℓ

/-- Bijectivity is proved by the two inverse laws for this particular map. -/
theorem compactReverse_bijective : Function.Bijective Qz := by
  have hl : Function.LeftInverse
      (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z) Qz :=
    compactReverseInverse_left χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
  have hr : Function.RightInverse
      (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z) Qz :=
    compactReverseInverse_right χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
  exact ⟨hl.injective, hr.surjective⟩

/-- Tensor the actual forward compact continuation with the transported
inverse of the actual reverse dual continuation. -/
def compactComparison :
    compactFiber χ K ψ hψ A →ₗ[ℂ] compactFiber χ K ψ' hψ' A :=
  TensorProduct.map
    (p.presentation.continuedOperator ⟨z.val, z.property.choose.1⟩)
    (compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)

/-- Conjugacy on pure tensors identifies the constructed fixed-carrier map
with the actual normalized generic comparison. -/
theorem compactComparison_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj Az)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (Az).contragredient) :
    compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A z.val
        (genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
          (tensorEquiv χ hG K hK ψ hψ hψK A z.val (f ⊗ₜ[ℂ] ℓ))) =
      compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
        (compactTensorEquiv χ hG K hK ψ hψ hψK A z.val
          (tensorEquiv χ hG K hK ψ hψ hψK A z.val (f ⊗ₜ[ℂ] ℓ))) := by
  have h := congrArg (compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A z.val)
    (genericComparison_tmul χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z f ℓ)
  have ht := compactTensorEquiv_tmul χ hG K hK ψ' hψ' hψ'K A z.val
    (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p
      ⟨z.val, z.property.choose.1⟩ f)
    (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz ℓ)
  have hi : compactReverseInverse χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
      A p q z (E₀ ℓ) =
      E₁ (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz ℓ) :=
    congrArg (fun v => E₁ (reverseInducedDualInverse h₀ h₁ hU₀ hU₁ Az Az Rz hz v))
      ((E₀).symm_apply_apply ℓ)
  have hf := forward_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K
    A p ⟨z.val, z.property.choose.1⟩ f
  have hmap := congrArg₂ (TensorProduct.tmul ℂ) hf.symm hi
  have hin := congrArg
    (compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)
    (compactTensorEquiv_tmul χ hG K hK ψ hψ hψK A z.val f ℓ)
  exact (h.trans ht).trans (hin.trans hmap).symm

/-- The square holds on every actual product-induced coefficient vector. -/
theorem compactComparison_square (v : coefficientFiber χ ψ hψ A z.val) :
    compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A z.val
        (genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z v) =
      compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
        (compactTensorEquiv χ hG K hK ψ hψ hψK A z.val v) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv χ hG K hK ψ hψ hψK A z.val).surjective v
  induction t using TensorProduct.inductionOn with
  | tmul f ℓ =>
      exact compactComparison_tmul χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z f ℓ
  | add t s ht hs => simp only [map_add, ht, hs]

end Generic

end Langlands.Plancherel.ActualCommonLeviCompactTensor
