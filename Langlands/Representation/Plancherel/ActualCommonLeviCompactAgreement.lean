import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericData
import Langlands.Representation.Plancherel.ActualCommonLeviContinuedTests

/-! # Agreement of actual compact intertwiners on irreducible fibers -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction ActualCommonLeviIwasawa
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviV3
open DynamicCommonLeviContinuation UnramifiedOperatorFamily DynamicOppositeCanonicalScalar

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
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.leviMeasurable ActualCommonLeviV3.leviBorel
  ActualCommonLeviV3.leviLocallyCompact ActualCommonLeviV3.parabolicLocallyCompact

open private compactFamily_forwardTest_eq
  from Langlands.Representation.Plancherel.ActualCommonLeviContinuedTests

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (x y : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (he₀ : Dynamic.centralizer x = Dynamic.centralizer χ)
  (he₁ : Dynamic.centralizer y = Dynamic.centralizer χ)
  (hx : ∀ g : rationalPoints G, ∃ p : parabolic x, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hy : ∀ g : rationalPoints G, ∃ p : parabolic y, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (z : unramifiedCharacters (normCharacters χ))

local notation "D₀" => commonDecomposition χ x he₀
local notation "D₁" => commonDecomposition χ y he₁
local notation "V₀" => CompactInductionPicture D₀ K A
local notation "V₁" => CompactInductionPicture D₁ K A
local notation "I₀" => UnramifiedLeviInduction D₀ (radical_isClosed x)
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "I₁" => UnramifiedLeviInduction D₁ (radical_isClosed y)
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "e₀" => compactEquiv χ hG K hK x he₀ hx z A
local notation "e₁" => compactEquiv χ hG K hK y he₁ hy z A
local notation "t" => chooseCompactAdjunctionTest χ K x he₀ y he₁ A hG
local notation "s₀" => sourceAdjunctionCompactTest χ K x he₀ y he₁ A t hG hK hx
local notation "s₁" => targetAdjunctionCompactTest χ K x he₀ y he₁ A t hG hK hy
local notation "ℓ" => (compactPictureDualBilin D₁ K hK A).flip s₁
local notation "c" => compactAdjunctionTestValue χ K hK x he₀ y he₁ A t

set_option backward.isDefEq.respectTransparency.types false in
private theorem compact_eq_of_same_test [Nontrivial A]
    (hi : (I₀).IsIrreducible) (T S : (I₀).representation.IntertwiningMap (I₁).representation)
    (hT : Function.Bijective T) (P Q : V₀ →ₗ[ℂ] V₁)
    (hP : ∀ f, (e₁) (T f) = P ((e₀) f)) (hQ : ∀ f, (e₁) (S f) = Q ((e₀) f))
    (hp : (ℓ) (P s₀) = c) (hq : (ℓ) (Q s₀) = c) : P = Q := by
  let e := Representation.IntertwiningMap.ofBijective T hT
  obtain ⟨b, hb, _⟩ := Schur.separableSmooth_scalarEndomorphism (I₀).representation
    (I₀).isSmooth hi (e.symm.toIntertwiningMap.comp S)
  have he (f : I₀) : S f = b • T f := by
    have hf : e.symm (S f) = b • f := congrArg (fun h : (I₀).representation.IntertwiningMap
      (I₀).representation => h f) hb
    have hh := congrArg e hf
    rw [Representation.Equiv.apply_symm_apply, map_smul] at hh
    exact hh
  have hQP (v : V₀) : Q v = b • P v := by
    obtain ⟨f, rfl⟩ := (e₀).surjective v
    rw [← hQ f, ← hP f, he f, map_smul]
  have h := congrArg (ℓ) (hQP s₀)
  rw [hq, map_smul, hp] at h
  have hc := compactAdjunctionTestValue_ne_zero χ K hK x he₀ y he₁ A t
  have hb' : b = 1 := (mul_right_cancel₀ hc ((one_mul _).trans h)).symm
  apply LinearMap.ext
  intro v
  rw [hQP v, hb', one_smul]

variable (p : ContinuedPair χ hG K hK x he₀ hx y he₁ hy A)
  (hz : z ∈ p.regularRegion)
  (hi : (I₀).IsIrreducible) (hi' : (I₁).IsIrreducible)

local notation "P" => p.presentation.continuedOperator ⟨z, hz⟩
local notation "T" => ContinuedPair.operator χ hG K hK x he₀ hx y he₁ hy A p ⟨z, hz⟩
local notation "hT" => continuedPair_operator_bijective_of_irreducible χ hG K hK x he₀ hx y he₁ hy A p
  ⟨z, hz⟩ hi hi'
local notation "hP" => forward_compact_square χ hG K hK x he₀ hx y he₁ hy A p ⟨z, hz⟩
local notation "hp" => continuedPair_forwardTest_eq χ K x he₀ y he₁ A t hG hK hx hy p ⟨z, hz⟩

include hi hi' in
set_option backward.isDefEq.respectTransparency.types false in
/-- Independently continued compact operators of one ordered pair agree at
common regular, irreducible parameters. -/
theorem continuedPair_eq_on_irreducible [Nontrivial A]
    (q : ContinuedPair χ hG K hK x he₀ hx y he₁ hy A) (h : z ∈ q.regularRegion) :
    P = q.presentation.continuedOperator ⟨z, h⟩ :=
  compact_eq_of_same_test χ hG A K hK x y he₀ he₁ hx hy z hi T
    (ContinuedPair.operator χ hG K hK x he₀ hx y he₁ hy A q ⟨z, h⟩) hT P _ hP
    (forward_compact_square χ hG K hK x he₀ hx y he₁ hy A q ⟨z, h⟩) hp
    (continuedPair_forwardTest_eq χ K x he₀ y he₁ A t hG hK hx hy q ⟨z, h⟩)

include hi hi' in
set_option backward.isDefEq.respectTransparency.types false in
/-- The continued compact operator agrees with the full-domain integral
at every common regular, irreducible parameter. -/
theorem continuedPair_eq_fullDomain_on_irreducible [Nontrivial A]
    (h : z ∈ pairFullDomainRegion χ K hK x he₀ y A) :
    P = compactFamily χ hG K hK x he₀ hx y he₁ hy p.modulus A ⟨z, h⟩ :=
  compact_eq_of_same_test χ hG A K hK x y he₀ he₁ hx hy z hi T
    (pairFamily χ K hK x he₀ y he₁ p.modulus A ⟨z, h⟩) hT P _ hP
    (fun f => by
      let J := pairFamily χ K hK x he₀ y he₁ p.modulus A ⟨z, h⟩
      change (e₁) (J f) = (e₁) (J ((e₀).symm ((e₀) f)))
      rw [LinearEquiv.symm_apply_apply]) hp
    (compactFamily_forwardTest_eq χ K x he₀ y he₁ A t hG hK hx hy p.modulus ⟨z, h⟩)

end Langlands.Plancherel.ActualCommonLeviV3
