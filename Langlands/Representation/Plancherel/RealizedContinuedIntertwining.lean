import Langlands.Representation.Plancherel.RealizedNestedIntegral
import Langlands.Representation.Plancherel.NestedContinuedIntertwiningComparison

/-! # Continued compact operators and restriction to a represented Levi -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation DynamicOppositeCanonicalScalar
open QuotientIntegration

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G L : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  (o : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (Dynamic.centralizer o).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (x y : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (a b : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hx : Dynamic.parabolic x = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic a) ∧
    Dynamic.centralizer x = (Dynamic.centralizer a).map j ∧
    Dynamic.unipotent x = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent a))
  (hy : Dynamic.parabolic y = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic b) ∧
    Dynamic.centralizer y = (Dynamic.centralizer b).map j ∧
    Dynamic.unipotent y = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent b))

open UnramifiedOperatorFamily

local notation "Gpt" => rationalPoints G
local notation "Lpt" => rationalPoints L
local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
local notation "QG" => QuotientSpace (U := radical x) (radical y)
local notation "QL" => QuotientSpace (U := radical a) (radical b)
local notation "E" => realizedNestedQuotientHomeomorph o j hj hjc x y a b hx hy

variable {M : Subgroup Gpt} {M' : Subgroup Lpt}
  (dG₀ : IsSemidirectDecomposition (parabolic x) M (radical x))
  (dG₁ : IsSemidirectDecomposition (parabolic y) M (radical y))
  (dL₀ : IsSemidirectDecomposition (parabolic a) M' (radical a))
  (dL₁ : IsSemidirectDecomposition (parabolic b) M' (radical b))
  (eM : M' ≃ₜ* M) (muG : Measure QG) (muL : Measure QL)
  (K : OpenSubgroup Gpt) (KL : OpenSubgroup Lpt)
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uV} ℂ M')
  (H : GroupScheme (Spec (CommRingCat.of F))) [TopologicalSpace (rationalPoints H)]
  (hp : Continuous (rationalValuationImageProjection H)) (hH : IsConnectedReductive H)

local notation "U" => unramifiedCharacters (fun a => (rationalNormCharacters H a).toMul)
variable (Az : U → SmoothRep.{0, u, uV} ℂ M)
local notation "Al" z => SmoothRep.pullback eM (Az z)
local notation "VG₀" => CompactInductionPicture dG₀ K A
local notation "VG₁" => CompactInductionPicture dG₁ K A
local notation "VL₀" => CompactInductionPicture dL₀ KL B
local notation "VL₁" => CompactInductionPicture dL₁ KL B
local notation "uG₀" => radical_isClosed x
local notation "uG₁" => radical_isClosed y
local notation "uL₀" => radical_isClosed a
local notation "uL₁" => radical_isClosed b
local notation "I₀" z => (DynamicNormalization.leviTwistedInductionFunctor dG₀ uG₀).obj (Az z)
local notation "I₁" z => (DynamicNormalization.leviTwistedInductionFunctor dG₁ uG₁).obj (Az z)
local notation "L₀" z => (DynamicNormalization.leviTwistedInductionFunctor dL₀ uL₀).obj (Al z)
local notation "L₁" z => (DynamicNormalization.leviTwistedInductionFunctor dL₁ uL₁).obj (Al z)

variable (Eg₀ : ∀ z : U, (I₀ z) ≃ₗ[ℂ] VG₀) (Eg₁ : ∀ z : U, (I₁ z) ≃ₗ[ℂ] VG₁)
  (El₀ : ∀ z : U, (L₀ z) ≃ₗ[ℂ] VL₀) (El₁ : ∀ z : U, (L₁ z) ≃ₗ[ℂ] VL₁)
  (R₀ : VG₀ →ₗ[ℂ] VL₀) (R₁ : VG₁ →ₗ[ℂ] VL₁)
  (hR₀ : ∀ z (f : I₀ z), RealizedRestrictionFormula o j hj hjc x a dG₀ dL₀ (Az z) eM f 1
    ((El₀ z).symm (R₀ (Eg₀ z f))))
  (hR₁ : ∀ z (f : I₁ z), RealizedRestrictionFormula o j hj hjc y b dG₁ dL₁ (Az z) eM f 1
    ((El₁ z).symm (R₁ (Eg₁ z f))))
  (t : ℝ≥0) (hscale : muG.map E = t • muL)
  (hlim : Jacquet.Localization.IsLimitOfCompactSubgroups (radical y))
  (hM' : IsClosed (M' : Set Lpt))

local notation "GJ[" z "," J "]" => (Eg₁ z).symm.toLinearMap.comp ((J).comp (Eg₀ z).toLinearMap)
local notation "LJ[" z "," J "]" => (El₁ z).symm.toLinearMap.comp ((J).comp (El₀ z).toLinearMap)

include hR₀ hR₁ hscale hlim hM' in
set_option backward.isDefEq.respectTransparency.types false in
private theorem realizedCompactIntertwiner_square (z : U)
    (J : VG₀ →ₗ[ℂ] VG₁) (J' : VL₀ →ₗ[ℂ] VL₁)
    (hJ : RepresentsStandardIntegral dG₀ uG₀ dG₁ uG₁ (Az z) muG GJ[z,J])
    (hJ' : RepresentsStandardIntegral dL₀ uL₀ dL₁ uL₁ (Al z) muL LJ[z,J']) :
    J'.comp ((t : ℂ) • R₀) = R₁.comp J := by
  apply LinearMap.ext
  intro v
  let f := (Eg₀ z).symm v
  let v₀ := Eg₀ z f
  let fl := (El₀ z).symm (R₀ v₀)
  let g := GJ[z,J] f
  let gl := (El₁ z).symm (R₁ (Eg₁ z g))
  let gl' := LJ[z,J'] fl
  have h₀ := HasIntegral.realized_restriction o j hj hjc x y a b hx hy dG₀ dL₀
    (Az z) eM muG hlim (hJ f) 1 fl (hR₀ z f)
  have h₁ := HasIntegral.smul_measure_nnreal dL₀ uL₀ (radical b) (Al z) muL (hJ' fl) t
  have hsame (l : Lpt) := (h₀ l).unique (compactCofinal hM') (Al z).isSmooth
    (show HarmonicAnalysis.SmoothWeakIntegral.HasIntegral (Al z).representation (muG.map E)
      (integrand dL₀ uL₀ (radical b) (Al z) l fl)
      ((t : ℂ) • eval (parabolic b) (leviInflatedInducingRepresentation dL₁ uL₁ (Al z)) gl' l) from
      hscale.symm ▸ h₁ l)
  have hEq : gl = (t : ℂ) • gl' := by
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change eval (parabolic b) (leviInflatedInducingRepresentation dL₁ uL₁ (Al z)) gl l =
      (t : ℂ) • eval (parabolic b) (leviInflatedInducingRepresentation dL₁ uL₁ (Al z)) gl' l
    have ht := hR₁ z g l
    rw [mul_one] at ht
    exact ht.trans (by simpa only [mul_one] using hsame l)
  have hgl : El₁ z gl = R₁ (J v) := by
    change El₁ z ((El₁ z).symm (R₁ (Eg₁ z ((Eg₁ z).symm (J v₀))))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (fun q => R₁ (J q)) ((Eg₀ z).apply_symm_apply v)
  have hgl' : El₁ z gl' = J' (R₀ v) := by
    change El₁ z ((El₁ z).symm (J' (El₀ z ((El₀ z).symm (R₀ v₀))))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (fun q => J' (R₀ q)) ((Eg₀ z).apply_symm_apply v)
  change J' ((t : ℂ) • R₀ v) = R₁ (J v)
  rw [map_smul, ← hgl, hEq, map_smul, hgl']

include hp hH hR₀ hR₁ hscale hlim hM' in
/-- The fixed compact restrictions commute with both continuations wherever
the two denominators are regular. The scalar is the positive comparison of
the specified quotient measures, inserted in the source restriction. -/
theorem realizedContinuedIntertwining_square {Ω Λ : Set U}
    (J : Ω → VG₀ →ₗ[ℂ] VG₁) (J' : Λ → VL₀ →ₗ[ℂ] VL₁)
    (p : RationalOperatorContinuationData Ω J) (q : RationalOperatorContinuationData Λ J')
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hsub : Ω ⊆ Λ)
    (hJ : ∀ z : Ω, RepresentsStandardIntegral dG₀ uG₀ dG₁ uG₁ (Az z.val) muG
      GJ[z.val,J z])
    (hJ' : ∀ z : Ω, RepresentsStandardIntegral dL₀ uL₀ dL₁ uL₁ (Al z.val) muL
      LJ[z.val,J' ⟨z.val, hsub z.property⟩])
    (z : ↥(p.regularRegion ∩ q.regularRegion)) :
    (q.continuedOperator ⟨z.val, z.property.2⟩).comp ((t : ℂ) • R₀) =
      R₁.comp (p.continuedOperator ⟨z.val, z.property.1⟩) :=
  rationalOperatorContinuationData_natural H hp hH p q ((t : ℂ) • R₀) R₁
    hΩ hne subset_rfl hsub
    (fun w hw => realizedCompactIntertwiner_square o j hj hjc x y a b hx hy dG₀ dG₁ dL₀ dL₁ eM
      muG muL K KL A B H Az Eg₀ Eg₁ El₀ El₁ R₀ R₁ hR₀ hR₁ t hscale hlim hM' w
      (J ⟨w, hw⟩) (J' ⟨w, hsub hw⟩) (hJ ⟨w, hw⟩) (hJ' ⟨w, hw⟩)) z

end Langlands.Plancherel.StandardIntertwining
