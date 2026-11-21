import Langlands.Representation.Plancherel.TranslatedCoefficientValue
import Langlands.Representation.Plancherel.ActualTranslatedCompactChart
import Langlands.Representation.Plancherel.ActualCompactTranslationFactorization
import Langlands.Representation.Plancherel.ActualCommonLeviV3CompactNormalization

/-! # Reindexing the compact product section under actual translation -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 280000
set_option backward.isDefEq.respectTransparency.types true

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCompactTranslationFactorization

open Aubert.General Induction
open ActualConjugateLeviTensor TranslatedCoefficientValue

private def productSectionEval {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {P M U : Subgroup H} (d : IsSemidirectDecomposition P M U)
    (hc : IsClosed (U : Set H)) (B : SmoothRep.{0, u, uV} ℂ M)
    (f : leviProductInducedCoefficientObject d hc B) (x : H × H) :=
  Induction.eval (P.prod P)
    (leviInflatedInducingRepresentation (d.prod d) (hc.prod hc)
      (productLeviObject B B.contragredient)) f x

private theorem translation_factors {H : Type*} [Group H] {X I J W : Type*}
    {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (e : I → H) (e' : J → H) (k₀ : J → I) (g : H)
    (hk : ∀ k, e (k₀ k) = g⁻¹ * e' k * g)
    (evalS : V → I → W) (evalT : V' → J → W) (hT : Function.Injective evalT)
    (ρ : X → H → V →ₗ[ℂ] V) (L : X → V →ₗ[ℂ] V') (F : X → V → H → W)
    (hρ : ∀ z x f y, F z (ρ z x f) y = F z f (y * x))
    (hS : ∀ z f k, F z f (e k) = evalS f k)
    (hL : ∀ z f k, evalT (L z f) k = F z f (g⁻¹ * e' k))
    (z₀ z : X) : L z = ((L z₀).comp (ρ z₀ g)).comp (ρ z g⁻¹) := by
  apply LinearMap.ext
  intro f
  apply hT
  funext k
  change evalT (L z f) k = evalT (L z₀ (ρ z₀ g (ρ z g⁻¹ f))) k
  calc
    evalT (L z f) k = F z f (g⁻¹ * e' k) := hL z f k
    _ = F z f (e (k₀ k) * g⁻¹) := by rw [hk]; simp [mul_assoc]
    _ = evalS (ρ z g⁻¹ f) (k₀ k) := (hρ z g⁻¹ f _).symm.trans (hS z _ _)
    _ = F z₀ (ρ z g⁻¹ f) (g⁻¹ * e' k * g) := by rw [← hk, hS]
    _ = F z₀ (ρ z₀ g (ρ z g⁻¹ f)) (g⁻¹ * e' k) := (hρ z₀ g _ _).symm
    _ = evalT (L z₀ (ρ z₀ g (ρ z g⁻¹ f))) k := (hL z₀ _ k).symm

private theorem inverseChart_action
    {H S V : Type*} [Monoid H] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H S} {σ : Representation ℂ H V}
    (e : ρ.Equiv σ) (chart : S ≃ₗ[ℂ] V) (hc : e.toLinearEquiv = chart) (x : H) (v : V) :
    chart.symm (σ x v) = ρ x (chart.symm v) := by
  rw [← hc]
  exact DFunLike.congr_fun (e.symm.isIntertwining' x) v

private theorem evaluate_via_fixed_chart
    {S V W Y : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (C : S ≃ₗ[ℂ] V) (J : V ≃ₗ[ℂ] W) (R : S ≃ₗ[ℂ] W)
    (evalCompact : W → Y) (evalAmbient : S → Y)
    (hchart : ∀ f, J (C f) = R f)
    (heval : ∀ f, evalCompact (R f) = evalAmbient f) (v : S) :
    evalCompact (J (C v)) = evalAmbient v :=
  (congrArg evalCompact (hchart v)).trans (heval v)

private theorem evaluation_in_compact_chart
    {S V W Y : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (C : S ≃ₗ[ℂ] V) (J : V ≃ₗ[ℂ] W) (R : S ≃ₗ[ℂ] W)
    (evalCompact : W → Y) (evalAmbient : S → Y)
    (hchart : ∀ f, J (C f) = R f)
    (heval : ∀ f, evalCompact (R f) = evalAmbient f) (v : V) :
    evalAmbient (C.symm v) = evalCompact (J v) := by
  rw [← heval, ← hchart, C.apply_symm_apply]

private theorem evaluation_after_chart_map
    {S T V W Y : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (C : S ≃ₗ[ℂ] V) (C' : T ≃ₗ[ℂ] W) (L : S →ₗ[ℂ] T) (Lc : V →ₗ[ℂ] W)
    (evalCompact : W → Y) (evalAmbient : T → Y)
    (hL : Lc = C'.toLinearMap.comp (L.comp C.symm.toLinearMap))
    (heval : ∀ f, evalCompact (C' f) = evalAmbient f) (v : V) :
    evalCompact (Lc v) = evalAmbient (L (C.symm v)) := by
  rw [hL]
  exact heval _

private def compactSectionEval
    {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {P M U : Subgroup H} (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
    (B : SmoothRep.{0, u, uV} ℂ M) (f : ProductInducedCompactPicture d K B) (k : K.prod K) :=
  Induction.eval _ _ f k

private theorem compactSectionEval_injective
    {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {P M U : Subgroup H} (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
    (B : SmoothRep.{0, u, uV} ℂ M) :
    Function.Injective (compactSectionEval d K B) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

section Untwisting

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M N : Subgroup H} {I J : Type*} (ν : I → (M →* ℝ≥0ˣ)) (ν' : J → (N →* ℝ≥0ˣ))
  (g : H) (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (A : SmoothRep.{0, u, uV} ℂ M)
  (z : unramifiedCharacters ν) (w : unramifiedCharacters ν')

set_option quotPrecheck false in
local notation "Ag" => (conjugationFunctor g hM).obj A
set_option quotPrecheck false in
local notation "Az" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
set_option quotPrecheck false in
local notation "Agw" => (Ag).twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' w)

private theorem untwist_of_linear_heq
    (e : ((conjugationFunctor g hM).obj Az).representation.Equiv (Agw).representation)
    (he : HEq e.toLinearEquiv (LinearEquiv.refl ℂ A)) (v : CoefficientTensor Az) :
    productCompactTwistTensorEquiv ν' w Ag
        (productCoefficientLeviEquiv e (conjugateValue g hM Az v)) =
      conjugateValue g hM A (productCompactTwistTensorEquiv ν z A v) := by
  have h : e.toLinearEquiv = LinearEquiv.refl ℂ A := eq_of_heq he
  exact untwist_conjugateValue ν ν' g hM A z w e (fun v => DFunLike.congr_fun h v) v

end Untwisting

section ActualPoints

open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviV3 ActualConjugateLeviTwist
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
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

local notation "H₀" => RationalPoint F G.X
local notation "d₀" => decomposition χ
set_option hygiene false in
local notation "d₁" => decomposition χg
local notation "hU₀" => radical_isClosed χ
set_option hygiene false in
local notation "hU₁" => radical_isClosed χg
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular χ hG
set_option hygiene false in
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular χg hG
local notation "hM" => DynamicCoefficientConjugation.levi_mem_conjugation χ g
set_option hygiene false in
local notation "B₀" z => twistObject χ z A
set_option hygiene false in
local notation "B₁" z => twistObject χg (conjugateParameter χ g z) Ag
set_option hygiene false in
local notation "e₀" z => conjugateTwistEquiv χ g z A
set_option hygiene false in
local notation "F₀" z => coefficientFiber χ χ rfl A z
set_option hygiene false in
local notation "F₁" z => coefficientFiber χg χg rfl Ag (conjugateParameter χ g z)
set_option hygiene false in
local notation "T" => translatedCoefficient χ g hG A K hK hPK

private abbrev valueTransport (z : X) := productCoefficientLeviEquiv (e₀ z)

private def anchoredCoefficientEval
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (B : SmoothRep.{0, u, uV} ℂ (levi ξ)) (w : unramifiedCharacters (normCharacters ξ))
    (f : coefficientFiber ξ ξ rfl B w) (x : H₀ × H₀) :=
  productSectionEval (commonDecomposition ξ ξ rfl) (radical_isClosed ξ) (twistObject ξ w B) f x

set_option hygiene false in
local notation "sourceEval" => anchoredCoefficientEval χ A

set_option hygiene false in
local notation "Lt" z => DynamicCoefficientConjugation.coefficientLeftTranslation
  χ g hG (B₀ z) K hK hPK
set_option hygiene false in
local notation "Ct" z => coefficientCongr (commonDecomposition χg χg rfl) hU₁ hδ₁ (e₀ z)

set_option maxHeartbeats 420000 in
private theorem translatedMap_eq (z : X) :
    (T z).toLinearMap = (Ct z).toLinearMap.comp (Lt z).toLinearMap := by
  delta ActualConjugateLeviTensor.translatedCoefficient
  simp only [Representation.Equiv.toLinearMap_trans]

set_option maxHeartbeats 500000 in
private theorem expandedProduct_eval (z : X) (f : F₀ z) (x : H₀ × H₀) :
    anchoredCoefficientEval χg Ag (conjugateParameter χ g z) ((Ct z) ((Lt z) f)) x =
      (valueTransport χ g A z) (conjugateValue g hM (B₀ z)
        (sourceEval z f ((g, g)⁻¹ * x))) := by
  let : CompactSpace (LeftQuotient (parabolic χ)) :=
    DynamicCoefficientConjugation.sourceQuotientCompact χ K hK hPK
  let : CompactSpace (LeftQuotient (parabolic χg)) :=
    DynamicCoefficientConjugation.targetQuotientCompact χ g K hK hPK
  delta anchoredCoefficientEval productSectionEval
    DynamicCoefficientConjugation.coefficientLeftTranslation
  have h := translatedProduct_eval (commonDecomposition χ χ rfl)
    (commonDecomposition χg χg rfl) g
    (DynamicCoefficientConjugation.parabolic_mem_conjugation χ g) hM
    (DynamicCoefficientConjugation.radical_mem_conjugation χ g)
    hU₀ hU₁ hδ₀ hδ₁ (B₀ z) (B₁ z) (e₀ z) f x
  exact h

private theorem ambientTranslatedProduct_eval (z : X) (f : F₀ z) (x : H₀ × H₀) :
    anchoredCoefficientEval χg Ag (conjugateParameter χ g z) ((T z).toLinearMap f) x =
      (valueTransport χ g A z) (conjugateValue g hM (B₀ z)
        (sourceEval z f ((g, g)⁻¹ * x))) := by
  have hm := congrArg (fun S : (F₀ z) →ₗ[ℂ] (F₁ z) =>
    anchoredCoefficientEval χg Ag (conjugateParameter χ g z) (S f) x)
    (translatedMap_eq χ g hG A K hK hPK z)
  exact hm.trans (expandedProduct_eval χ g hG A K hK hPK z f x)

set_option hygiene false in
local notation "untwist₀" z => productCompactTwistTensorEquiv (leviNormCharacters χ)
  (parameterTransport χ z) A
set_option hygiene false in
local notation "untwist₁" z => productCompactTwistTensorEquiv (leviNormCharacters χg)
  (parameterTransport χg (conjugateParameter χ g z)) Ag

set_option maxHeartbeats 600000 in
private theorem untwistedAmbientValue (z : X) (v : CoefficientTensor (B₀ z)) :
    (untwist₁ z) ((valueTransport χ g A z) (conjugateValue g hM (B₀ z) v)) =
      conjugateValue g hM A ((untwist₀ z) v) := by
  have h := untwist_of_linear_heq (leviNormCharacters χ) (leviNormCharacters χg) g hM A
    (parameterTransport χ z) (parameterTransport χg (conjugateParameter χ g z))
    (e₀ z) (conjugateTwistEquiv_linear_heq χ g z A) v
  exact h

set_option hygiene false in
local notation "C₀" => compactTensorEquiv χ hG K hK χ rfl hPK A
set_option hygiene false in
local notation "C₁" => compactTensorEquiv χg hG K' hK' χg rfl hχgK' Ag
set_option hygiene false in
local notation "J₀" => compactProductTensorEquiv χ hG A K hK χ rfl hPK
set_option hygiene false in
local notation "R₀" => compactProductRestriction χ hG A K hK χ rfl hPK
set_option hygiene false in
local notation "Lc" => ActualTranslatedCompactTensor.compactTranslation χ g hG A K hK hPK
  K' hK' hχgK'
set_option hygiene false in
local notation "ρ" => compactTensorRepresentation χ hG K hK χ rfl hPK A
set_option hygiene false in
local notation "V₀" => compactFiber χ K χ rfl A
set_option hygiene false in
local notation "V₁" => compactFiber χg K' χg rfl Ag
set_option hygiene false in
local notation "conjValue" => conjugateValue g hM A

private def compactSourceValue (v : V₀) (k : K.prod K) :=
  conjValue (compactSectionEval (commonDecomposition χ χ rfl) K A (J₀ v) k)

private def compactTensorValue
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (B : SmoothRep.{0, u, uV} ℂ (levi ξ)) (J : OpenSubgroup H₀)
    (hJ : IsCompact (J : Set H₀))
    (hPJ : ∀ x : H₀, ∃ p : parabolic ξ, ∃ j : J, x = (p : H₀) * (j : H₀))
    (v : compactFiber ξ J ξ rfl B) (k : J.prod J) :=
  compactSectionEval (commonDecomposition ξ ξ rfl) J B
    (compactProductTensorEquiv ξ hG B J hJ ξ rfl hPJ v) k

private theorem compactTensorValue_injective
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (B : SmoothRep.{0, u, uV} ℂ (levi ξ)) (J : OpenSubgroup H₀)
    (hJ : IsCompact (J : Set H₀))
    (hPJ : ∀ x : H₀, ∃ p : parabolic ξ, ∃ j : J, x = (p : H₀) * (j : H₀)) :
    Function.Injective (compactTensorValue hG ξ B J hJ hPJ) :=
  (compactSectionEval_injective (commonDecomposition ξ ξ rfl) J B).comp
    (compactProductTensorEquiv ξ hG B J hJ ξ rfl hPJ).injective

set_option maxHeartbeats 500000 in
private theorem compactTensorValue_restriction
    (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (B : SmoothRep.{0, u, uV} ℂ (levi ξ)) (J : OpenSubgroup H₀)
    (hJ : IsCompact (J : Set H₀))
    (hPJ : ∀ x : H₀, ∃ p : parabolic ξ, ∃ j : J, x = (p : H₀) * (j : H₀))
    (z : unramifiedCharacters (normCharacters ξ)) (f : coefficientFiber ξ ξ rfl B z)
    (k : J.prod J) :
    compactTensorValue hG ξ B J hJ hPJ (compactTensorEquiv ξ hG J hJ ξ rfl hPJ B z f) k =
      productCompactTwistTensorEquiv (leviNormCharacters ξ) (parameterTransport ξ z) B
        (anchoredCoefficientEval ξ B z f k.val) := by
  have h := evaluate_via_fixed_chart (compactTensorEquiv ξ hG J hJ ξ rfl hPJ B z)
    (compactProductTensorEquiv ξ hG B J hJ ξ rfl hPJ)
    (compactProductRestriction ξ hG B J hJ ξ rfl hPJ z)
    (fun j => compactSectionEval (commonDecomposition ξ ξ rfl) J B j k)
    (fun j => productCompactTwistTensorEquiv
      (leviNormCharacters ξ) (parameterTransport ξ z) B (anchoredCoefficientEval ξ B z j k.val))
    (compactProductTensorEquiv_compactTensorEquiv ξ hG B J hJ ξ rfl hPJ z)
    (fun j => compactProductRestriction_eval ξ hG B J hJ ξ rfl hPJ z j k) f
  exact h

private def compactTargetValue (v : V₁) (k : K'.prod K') :=
  compactTensorValue hG χg Ag K' hK' hχgK' v k

private def ambientSourceValue (z : X) (v : V₀) (x : H₀ × H₀) :=
  conjValue ((untwist₀ z) (sourceEval z ((C₀ z).symm v) x))

set_option maxHeartbeats 500000 in
private theorem ambient_on_compact (z : X) (v : V₀) (k : K.prod K) :
    ambientSourceValue χ g hG A K hK hPK z v k.val =
      compactSourceValue χ g hG A K hK hPK v k := by
  have h := evaluation_in_compact_chart (C₀ z) J₀ (R₀ z)
    (fun f => compactSectionEval (commonDecomposition χ χ rfl) K A f k)
    (fun f => (untwist₀ z) (sourceEval z f k.val))
    (compactProductTensorEquiv_compactTensorEquiv χ hG A K hK χ rfl hPK z)
    (fun f => compactProductRestriction_eval χ hG A K hK χ rfl hPK z f k) v
  exact congrArg conjValue h

private theorem ambient_eval_action (z : X) (x : H₀ × H₀) (f : F₀ z) (y : H₀ × H₀) :
    sourceEval z ((coefficientFiber χ χ rfl A z).representation x f) y =
      sourceEval z f (y * x) := rfl

set_option maxHeartbeats 500000 in
private theorem right_action_eval (z : X) (x : H₀ × H₀) (v : V₀) (y : H₀ × H₀) :
    ambientSourceValue χ g hG A K hK hPK z (ρ z x v) y =
      ambientSourceValue χ g hG A K hK hPK z v (y * x) := by
  let e := compactTensorRepresentationEquiv χ hG K hK χ rfl hPK A z
  have hc := compactTensorRepresentationEquiv_toLinearEquiv χ hG K hK χ rfl hPK A z
  have he := inverseChart_action e (C₀ z) hc x v
  have h := (congrArg (fun f : F₀ z => sourceEval z f y) he).trans
    (ambient_eval_action χ A z x ((C₀ z).symm v) y)
  exact congrArg (fun σ => conjValue ((untwist₀ z) σ)) h

set_option maxHeartbeats 450000 in
private theorem compactTranslation_map_eq (z : X) :
    Lc z = (C₁ (conjugateParameter χ g z)).toLinearMap.comp
      ((T z).toLinearMap.comp (C₀ z).symm.toLinearMap) := by
  delta ActualTranslatedCompactTensor.compactTranslation
  with_reducible rfl

private theorem compact_target_restriction (z : X) (f : F₁ z) (k : K'.prod K') :
    compactTargetValue χ g hG A K' hK' hχgK' (C₁ (conjugateParameter χ g z) f) k =
      (untwist₁ z) (anchoredCoefficientEval χg Ag (conjugateParameter χ g z) f k.val) :=
  compactTensorValue_restriction hG χg Ag K' hK' hχgK' (conjugateParameter χ g z) f k

set_option maxHeartbeats 650000 in
private theorem evaluate_compactTranslation (z : X) (v : V₀) (k : K'.prod K') :
    compactTargetValue χ g hG A K' hK' hχgK' (Lc z v) k =
      ambientSourceValue χ g hG A K hK hPK z v ((g, g)⁻¹ * k.val) := by
  let f := (C₀ z).symm v
  let x := (k : H₀ × H₀)
  have hc := evaluation_after_chart_map (C₀ z) (C₁ (conjugateParameter χ g z))
    (T z).toLinearMap (Lc z) (fun j => compactTargetValue χ g hG A K' hK' hχgK' j k)
    (fun j => (untwist₁ z) (anchoredCoefficientEval χg Ag (conjugateParameter χ g z) j x))
    (compactTranslation_map_eq χ g hG A K hK hPK K' hK' hχgK' z)
    (fun j => compact_target_restriction χ g hG A K' hK' hχgK' z j k) v
  have hf := congrArg (untwist₁ z) (ambientTranslatedProduct_eval χ g hG A K hK hPK z f x)
  exact hc.trans (hf.trans (untwistedAmbientValue χ g A z (sourceEval z f ((g, g)⁻¹ * x))))

private def sourceCompactPair (hKK' : RationalDynamicSource.conjugateCompact g K = K')
    (k : K'.prod K') : K.prod K := by
  have hmem (x : H₀) (hx : x ∈ K') : g⁻¹ * x * g ∈ K := by
    have hx' : x ∈ RationalDynamicSource.conjugateCompact g K := hKK'.symm ▸ hx
    exact (RationalDynamicSource.mem_conjugateCompact g (g⁻¹ * x * g) K).mp
      (by simpa [mul_assoc] using hx')
  exact ⟨(g, g)⁻¹ * k.val * (g, g), hmem k.val.1 k.property.1, hmem k.val.2 k.property.2⟩

private theorem targetEval_injective :
    Function.Injective (compactTargetValue χ g hG A K' hK' hχgK') :=
  compactTensorValue_injective hG χg Ag K' hK' hχgK'

set_option maxHeartbeats 700000 in
/-- Reindexing the actual compact coefficient sections after simultaneous
right translation gives a map independent of the inducing parameter. -/
theorem translationFactorization_of_conjugateCompact
    (hKK' : RationalDynamicSource.conjugateCompact g K = K') :
    TranslationFactorization χ g hG A K hK hPK K' hK' hχgK' := by
  intro z
  exact translation_factors (fun k : K.prod K => k.val) (fun k : K'.prod K' => k.val)
    (sourceCompactPair g K K' hKK') (g, g) (fun _ => rfl)
    (compactSourceValue χ g hG A K hK hPK) (compactTargetValue χ g hG A K' hK' hχgK')
    (targetEval_injective χ g hG A K' hK' hχgK') (fun z x => ρ z x) Lc
    (ambientSourceValue χ g hG A K hK hPK)
    (right_action_eval χ g hG A K hK hPK) (ambient_on_compact χ g hG A K hK hPK)
    (evaluate_compactTranslation χ g hG A K hK hPK K' hK' hχgK') 1 z

/-- The compact leg of the actual translated tensor is polynomial on each
subset of the full source parameter space. -/
theorem compactTranslation_polynomial
    (hKK' : RationalDynamicSource.conjugateCompact g K = K') (Ω : Set X) :
    IsPolynomialOperatorOn Ω (fun z => Lc z.val) :=
  compactTranslation_polynomial_of_factorization χ g hG A K hK hPK K' hK' hχgK'
    (translationFactorization_of_conjugateCompact χ g hG A K hK hPK K' hK' hχgK' hKK') Ω

open ActualConjugateLeviRationalParameter

set_option maxHeartbeats 600000 in
/-- Use the actual polynomial compact translation to carry the standard
numerator and its whole-operator denominator into the V.3 chart. -/
def compactChartContinuation_of_conjugateCompact
    (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χg)
    (hψK : ∀ x : H₀, ∃ p : parabolic ψ, ∃ k : K', x = (p : H₀) * (k : H₀))
    (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK Ag)
    (q : ContinuedPair χg hG K' hK' ψ hψ hψK χg rfl hχgK' (Ag).contragredient)
    (hKK' : RationalDynamicSource.conjugateCompact g K = K')
    (standard : RationalOperatorContinuationData
      (ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK p q)
      (pulledBackStandardTensor χ g hG A K' hK' hχgK' ψ hψ hψK p q)) :
    RationalOperatorContinuationData
      (ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK p q)
      (ActualConjugateLeviV3.compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK p q) := by
  have hpoly := compactTranslation_polynomial χ g hG A K hK hPK K' hK' hχgK' hKK' Set.univ
  exact ActualTranslatedCompactTensor.compactChartContinuation
    χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK p q standard hpoly

end ActualPoints

end Langlands.Plancherel.ActualCompactTranslationFactorization
