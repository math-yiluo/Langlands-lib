import Langlands.Representation.Plancherel.ActualCommonLeviContinuedTests
import Langlands.Representation.Plancherel.ActualCommonLeviCompactTensor
import Langlands.Representation.Plancherel.ActualCommonLeviV3AdjunctionScale

/-! # Unscaled compact probability adjunction for the genuine generic pair -/

noncomputable section

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining CompactInduction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation ActualCommonLeviTensor ActualCommonLeviCompactTensor
open ActualCommonLeviIwasawa

section Duality

variable {X : Type u} [Group X] [TopologicalSpace X] [LocallyCompactSpace X]
  [NonarchimedeanGroup X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  {P M U : Subgroup X} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set X))
  (T : SmoothRep.{0, u, uV} ℂ M) (K : OpenSubgroup X)
  (hu : IsUnimodularModulus U hU) (hK : IsCompact (K : Set X))
  (hP : IsClosed (P : Set X)) (hm : Continuous h.projection)
  (hPK : ∀ g : X, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
  (hX : ∀ x : X, modularCharacter x = 1)
  (hδ : ∀ p : P, modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (hT : T.IsAdmissible)

private theorem leviInducedSmoothDualEquiv_pairing_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj T)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj T.contragredient) :
    smoothDualPairing ((normalizedInductionFunctor h hU).obj T).representation
      (leviInducedSmoothDualEquiv h hU T K hu hK hP hm hPK hX hδ hT ℓ)
      ((normalizedInductionLeviEquiv h hU hu T).symm f) =
        ∫ k : K, smoothDualPairing T.representation
          (eval P (leviInflatedInducingRepresentation h hU T.contragredient) ℓ (k : X))
          (eval P (leviInflatedInducingRepresentation h hU T) f (k : X)) ∂(CompactInduction.measure K hK) := by
  let a := (normalizedInductionLeviEquiv h hU hu T.contragredient).symm ℓ
  let e := integralDualEquiv h hU hP hm K hK hPK hX hδ T hT
  let b := e.symm a
  have hb : e b = a := e.apply_symm_apply a
  have he := integralDualEquiv_pairing h hU hP hm K hK hPK hX hδ T hT b
    ((normalizedInductionLeviEquiv h hU hu T).symm f)
  change _ = ∫ k : K, smoothDualPairing T.representation
    (eval P (inducingRepresentation h hU T.contragredient) (e b) (k : X))
    (eval P (inducingRepresentation h hU T) ((normalizedInductionLeviEquiv h hU hu T).symm f) (k : X))
      ∂(CompactInduction.measure K hK) at he
  rw [hb] at he
  refine he.trans (integral_congr_ae (ae_of_all _ fun k => ?_))
  exact congrArg₂ (fun x y => smoothDualPairing T.representation x y)
    (normalizedInductionLeviEquiv_symm_eval h hU hu T.contragredient ℓ (k : X))
    (normalizedInductionLeviEquiv_symm_eval h hU hu T f (k : X))

end Duality

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
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)

local notation "Γ" => RationalPoint F G.X
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "hU₀" => radical_isClosed ψ
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "Z" => unramifiedCharacters (normCharacters χ)

private theorem compactPictureDualPairing_dualInductionEquiv
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : ∀ g : Γ, ∃ p : parabolic ψ, ∃ k : K, g = (p : Γ) * (k : Γ))
    (w : Z) (hA : (twistObject χ w A).IsAdmissible)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (twistObject χ w A))
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (twistObject χ w A).contragredient) :
    smoothDualPairing ((normalizedInductionFunctor h₀ hU₀).obj (twistObject χ w A)).representation
      (leviInducedSmoothDualEquiv h₀ hU₀ (twistObject χ w A) K
        (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK hP₀ hr₀
        (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) hA ℓ)
      ((normalizedInductionLeviEquiv h₀ hU₀ (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG)
        (twistObject χ w A)).symm f) =
      compactPictureDualPairing h₀ K hK A
        (compactEquiv χ hG K hK ψ hψ hψK w A f)
        (dualCompactEquiv χ hG K hK ψ hψ hψK A w ℓ) := by
  let B := twistObject χ w A
  let huni := DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
  let d := dualInductionEquiv χ hG ψ hψ A w
  refine (leviInducedSmoothDualEquiv_pairing_eval h₀ hU₀ B K huni hK hP₀ hr₀
    (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) hA f ℓ).trans ?_
  unfold compactPictureDualPairing
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have hf := compactEquiv_eval χ hG K hK ψ hψ hψK w A f k
  have hℓ := compactEquiv_eval χ hG K hK ψ hψ hψK w⁻¹ A.contragredient (d ℓ) k
  have hl := CoefficientConjugation.leviInductionCongr_eval h₀ hU₀ huni (dualTwistEquiv χ w A) ℓ (k : Γ)
  let v := eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ B) f (k : Γ)
  let ℓw := eval (parabolic ψ) (leviInflatedInducingRepresentation h₀ hU₀ B.contragredient) ℓ (k : Γ)
  have hv : smoothDualPairing B.representation ℓw v =
      smoothDualPairing A.representation (dualTwistEquiv χ w A ℓw) v :=
    (dualTwistEquiv_apply χ w A ℓw v).symm
  exact hv.trans (congrArg₂ (fun l x => smoothDualPairing A.representation l x)
    (hℓ.trans hl).symm hf.symm)

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)

local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₁" => radical_isClosed ψ'
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "Iwasawa[" P "]" => ∀ g : Γ, ∃ p : P, ∃ k : K, g = (p : Γ) * (k : Γ)
local notation "Norm[" h "," hU "," w "]" => (normalizedInductionFunctor h hU).obj (twistObject χ w A)
local notation "Dual[" h "," hU "," w "]" =>
  (DynamicNormalization.leviTwistedInductionFunctor h hU).obj (twistObject χ w A).contragredient

/-- The actual fixed adjunction tests in the source normalized induction
and the target positive-Levi induction of the twisted smooth dual. -/
def normalizedCompactAdjunctionTest
    (hG : IsConnectedReductive G) (t : CompactAdjunctionTest χ K ψ hψ ψ' hψ' A) (w : Z) :
    Norm[h₀, hU₀, w] × Dual[h₁, hU₁, w] :=
  ⟨(normalizedInductionLeviEquiv h₀ hU₀ (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG)
      (twistObject χ w A)).symm (sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t w),
    (dualInductionEquiv χ hG ψ' hψ' A w).symm (targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t w)⟩

local notation "E[" g "," k "," i "," i' "," p "," q "," z "]" =>
  genericNormalizedForwardEquiv χ g A K k ψ hψ i ψ' hψ' i' p q z
local notation "hUnimod[" ψ "," g "]" => DynamicOppositeCanonicalScalar.radical_unimodular ψ g

set_option maxHeartbeats 1800000 in
/-- The actual generic compact probability adjunction has scale one. -/
theorem genericAdjunction_exact [Nontrivial A]
    (hG : IsConnectedReductive G) (hK : IsCompact (K : Set Γ))
    (hψK : Iwasawa[parabolic ψ]) (hψ'K : Iwasawa[parabolic ψ'])
    (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
    (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)
    (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)
    (hA : (twistObject χ z.val A).IsAdmissible) (hirr : (Norm[h₁, hU₁, z.val]).IsIrreducible) :
    let B := twistObject χ z.val A
    let e := E[hG, hK, hψK, hψ'K, p, q, z]
    let d₀ := leviInducedSmoothDualEquiv h₀ hU₀ B K hUnimod[ψ, hG] hK hP₀ hr₀
      (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) hA
    let d₁ := leviInducedSmoothDualEquiv h₁ hU₁ B K hUnimod[ψ', hG] hK hP₁ hr₁
      (iwasawa_sets K ψ' hψ'K) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ' hψ') hA
    let R := reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨z.val, z.property.choose⟩
    ∀ (f : Norm[h₀, hU₀, z.val]) (ℓ : Dual[h₁, hU₁, z.val]),
      smoothDualPairing (Norm[h₁, hU₁, z.val]).representation (d₁ ℓ) (e f) =
        smoothDualPairing (Norm[h₀, hU₀, z.val]).representation (d₀ (R ℓ)) f := by
  dsimp only
  let B := twistObject χ z.val A
  let e := E[hG, hK, hψK, hψ'K, p, q, z]
  let d₀ := leviInducedSmoothDualEquiv h₀ hU₀ B K hUnimod[ψ, hG] hK hP₀ hr₀
    (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ) hA
  let d₁ := leviInducedSmoothDualEquiv h₁ hU₁ B K hUnimod[ψ', hG] hK hP₁ hr₁
    (iwasawa_sets K ψ' hψ'K) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ' hψ') hA
  let R := reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q ⟨z.val, z.property.choose⟩
  let t := chooseCompactAdjunctionTest χ K ψ hψ ψ' hψ' A hG
  let x := sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z.val
  let y := targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t z.val
  let f₀ := (normalizedCompactAdjunctionTest χ A K ψ hψ ψ' hψ' hG t z.val).1
  let ℓ₀ := (normalizedCompactAdjunctionTest χ A K ψ hψ ψ' hψ' hG t z.val).2
  let s₀ := sourceAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t hG hK hψK
  let s₁ := targetAdjunctionCompactTest χ K ψ hψ ψ' hψ' A t hG hK hψ'K
  let C := compactAdjunctionTestValue χ K hK ψ hψ ψ' hψ' A t
  let w₀ : p.regularRegion := ⟨z.val, z.property.choose.1⟩
  let w₁ : q.regularRegion := ⟨z.val⁻¹, z.property.choose.2⟩
  let J₀ := ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p w₀
  let a₀ := normalizedInductionLeviEquiv h₀ hU₀ hUnimod[ψ, hG] B
  let a₁ := normalizedInductionLeviEquiv h₁ hU₁ hUnimod[ψ', hG] B
  let b₁ := dualInductionEquiv χ hG ψ' hψ' A z.val
  let c₀ := compactEquiv χ hG K hK ψ hψ hψK z.val A
  let c₁ := compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A
  let c₁d := compactEquiv χ hG K hK ψ' hψ' hψ'K z.val⁻¹ A.contragredient
  let cd₀ := dualCompactEquiv χ hG K hK ψ hψ hψK A z.val
  let cd₁ := dualCompactEquiv χ hG K hK ψ' hψ' hψ'K A z.val
  have hsrc : c₀ x = s₀ := compactEquiv_sourceAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψK z.val
  have htgt : c₁d y = s₁ := compactEquiv_targetAdjunctionTestSection χ K ψ hψ ψ' hψ' A t hG hK hψ'K z.val
  have hf : e f₀ = a₁.symm (J₀ x) := by
    change a₁.symm (J₀ (a₀ (a₀.symm x))) = _
    rw [Representation.Equiv.apply_symm_apply]
  have hl : b₁ ℓ₀ = y := b₁.apply_symm_apply y
  have hd : cd₁ ℓ₀ = s₁ := (congrArg c₁d hl).trans htgt
  have hu₀ : c₁ (J₀ x) = p.presentation.continuedOperator w₀ s₀ :=
    (forward_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p w₀ x).trans
      (congrArg (fun v : CompactInductionPicture h₀ K A => p.presentation.continuedOperator w₀ v) hsrc)
  have hu₁ : cd₀ (R ℓ₀) = q.presentation.continuedOperator w₁ s₁ :=
    (reverseDual_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
      ⟨z.val, z.property.choose⟩ ℓ₀).trans
      (congrArg (fun v : CompactInductionPicture h₁ K A.contragredient =>
        q.presentation.continuedOperator w₁ v) hd)
  have htarget : smoothDualPairing (Norm[h₁, hU₁, z.val]).representation (d₁ ℓ₀) (e f₀) = C := by
    rw [hf]
    refine (compactPictureDualPairing_dualInductionEquiv χ A K ψ' hψ' hG hK hψ'K
      z.val hA (J₀ x) ℓ₀).trans ?_
    change compactPictureDualPairing h₁ K hK A (c₁ (J₀ x)) (cd₁ ℓ₀) = C
    exact (congrArg₂ (compactPictureDualPairing h₁ K hK A) hu₀ hd).trans
      (continuedPair_forwardTest_eq χ K ψ hψ ψ' hψ' A t hG hK hψK hψ'K p w₀)
  have hsource : smoothDualPairing (Norm[h₀, hU₀, z.val]).representation (d₀ (R ℓ₀)) f₀ = C := by
    refine (compactPictureDualPairing_dualInductionEquiv χ A K ψ hψ hG hK hψK
      z.val hA x (R ℓ₀)).trans ?_
    change compactPictureDualPairing h₀ K hK A (c₀ x) (cd₀ (R ℓ₀)) = C
    exact (congrArg₂ (compactPictureDualPairing h₀ K hK A) hsrc hu₁).trans
      (continuedPair_reverseTest_eq χ K ψ hψ ψ' hψ' A t hG hK hψK hψ'K q p.modulus w₁)
  have hne : C ≠ 0 := compactAdjunctionTestValue_ne_zero χ K hK ψ hψ ψ' hψ' A t
  exact genericAdjunction_of_test χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z hA hirr f₀ ℓ₀
    (fun h => hne (hsource.symm.trans h)) (htarget.trans hsource.symm)

end Langlands.Plancherel.ActualCommonLeviV3
