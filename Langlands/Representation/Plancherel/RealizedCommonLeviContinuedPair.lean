import Langlands.Representation.Plancherel.RealizedCommonLeviCompactCharts
import Langlands.Representation.Plancherel.RealizedContinuedIntertwining
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Actual continued standard pairs through a represented intermediate Levi -/

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

open UnramifiedOperatorFamily ActualCommonLeviTensor

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hG : IsConnectedReductive G) (hL : IsConnectedReductive L)
  (hxG : Dynamic.centralizer x = Dynamic.centralizer χ)
  (hyG : Dynamic.centralizer y = Dynamic.centralizer χ)
  (haL : Dynamic.centralizer a = Dynamic.centralizer ξ)
  (hbL : Dynamic.centralizer b = Dynamic.centralizer ξ)
  (eM : levi ξ ≃ₜ* levi χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (B : SmoothRep.{0, u, uV} ℂ (levi ξ))
  (eB : (SmoothRep.pullback eM A).representation.Equiv B.representation)
  (fParam : parameterScheme ξ ⟶ parameterScheme χ)
  (hpar : ∀ z m,
    (parameterTransport ξ (rationalUnramifiedCharacterRestrict fParam z)).val m =
      (parameterTransport χ z).val (eM m))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))
  (hxK : ∀ g : rationalPoints G, ∃ p : parabolic x, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hyK : ∀ g : rationalPoints G, ∃ p : parabolic y, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (haK : ∀ g : rationalPoints L, ∃ p : parabolic a, ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))
  (hbK : ∀ g : rationalPoints L, ∃ p : parabolic b, ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))

local notation "d₀" => commonDecomposition χ x hxG
local notation "d₁" => commonDecomposition χ y hyG
local notation "h₀" => commonDecomposition ξ a haL
local notation "h₁" => commonDecomposition ξ b hbL
local notation "u₀" => radical_isClosed x
local notation "u₁" => radical_isClosed y
local notation "k₀" => radical_isClosed a
local notation "k₁" => radical_isClosed b
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xl" => unramifiedCharacters (normCharacters ξ)
local notation "τ" => rationalUnramifiedCharacterRestrict fParam
local notation "Ag[" z "]" => twistObject χ z A
local notation "Bl[" z "]" => twistObject ξ ((τ) z) B
local notation "Al[" z "]" => SmoothRep.pullback eM Ag[z]
local notation "eTw[" z "]" => realizedTwistCoefficientEquiv χ ξ eM A B eB τ hpar z
local notation "eg₀[" z "]" => compactEquiv χ hG K hK x hxG hxK z A
local notation "eg₁[" z "]" => compactEquiv χ hG K hK y hyG hyK z A
local notation "el₀[" z "]" => realizedLowerCompactEquiv a hL χ ξ haL eM A B eB τ hpar K' hK' haK z
local notation "el₁[" z "]" => realizedLowerCompactEquiv b hL χ ξ hbL eM A B eB τ hpar K' hK' hbK z
local notation "vl₀" => CompactInductionPicture h₀ K' B
local notation "vl₁" => CompactInductionPicture h₁ K' B
local notation "vg₀" => CompactInductionPicture d₀ K A
local notation "vg₁" => CompactInductionPicture d₁ K A
local notation "ig₀[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor d₀ u₀).obj Ag[z]
local notation "ig₁[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor d₁ u₁).obj Ag[z]
local notation "il₀[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor h₀ k₀).obj Al[z]
local notation "il₁[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor h₁ k₁).obj Al[z]
local notation "qG" => pairQuotientMeasure K hK x y
local notation "qL" => pairQuotientMeasure K' hK' a b
local notation "EqQ" => realizedNestedQuotientHomeomorph o j hj hjc x y a b hx hy

variable (R₀ : vg₀ →ₗ[ℂ] vl₀) (R₁ : vg₁ →ₗ[ℂ] vl₁) (hRsurj : Function.Surjective R₀)
  (hR₀ : ∀ z (f : ig₀[z]), RealizedRestrictionFormula o j hj hjc x a d₀ h₀ Ag[z] eM f 1
    ((el₀[z]).symm (R₀ ((eg₀[z]) f))))
  (hR₁ : ∀ z (f : ig₁[z]), RealizedRestrictionFormula o j hj hjc y b d₁ h₁ Ag[z] eM f 1
    ((el₁[z]).symm (R₁ ((eg₁[z]) f))))
  (p : ContinuedPair χ hG K hK x hxG hxK y hyG hyK A)
  (modL : SquaredModulusCompatibility h₀ k₀ h₁ k₁)

local notation "LFull" => pairFullDomainRegion ξ K' hK' a haL b B
local notation "LJ" => compactFamily ξ hL K' hK' a haL haK b hbL hbK modL B
local notation "GJ" => compactFamily χ hG K hK x hxG hxK y hyG hyK p.modulus A

variable (q : RationalOperatorContinuationData LFull LJ)

local notation "Lu" => ((τ) ⁻¹' LFull : Set X)
local notation "LJτ" => fun z : Lu => (LJ) ⟨(τ) z.val, z.property⟩
local notation "qτ" => continuationRestrict fParam q (A' := LJτ) (fun _ h => h) (fun _ => rfl)

include hx hy hRsurj hR₀ in
set_option backward.isDefEq.respectTransparency.types false in
private theorem continuedPair_region_mem_lower
    (t : ℝ≥0) (ht : 0 < t) (he : (qG).map EqQ = t • qL) : p.region ⊆ Lu := by
  intro z hz
  let r := (el₀[z]).symm.toLinearMap.comp (R₀.comp (eg₀[z]).toLinearMap)
  have hlim := BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
    BruhatTits.dynamicUnipotentCompactOpenContainment F G hG y
  have hl := realizedNested_domain_eq_top o j hj hjc x y a b hx hy d₀ h₀ Ag[z] eM qG hlim r
    ((el₀[z]).symm.surjective.comp (hRsurj.comp (eg₀[z]).surjective)) (hR₀ z) qL t ht he
    (p.converges hz)
  change domain h₀ k₀ (radical b) Bl[z] qL = ⊤
  exact domain_eq_top_of_equiv h₀ k₀ (radical b) qL eTw[z] hl

set_option backward.isDefEq.respectTransparency.types false in
private theorem lowerCompactFamily_represents (z : Lu) :
    RepresentsStandardIntegral h₀ k₀ h₁ k₁ Al[z.val] qL
      ((el₁[z.val]).symm.toLinearMap.comp ((LJτ z).comp (el₀[z.val]).toLinearMap)) := by
  intro f
  let w := z.val
  let ez := eTw[w]
  let S₀ := leviInflatedInductionEquivOfEquiv h₀ k₀ ez
  let S₁ := leviInflatedInductionEquivOfEquiv h₁ k₁ ez
  let c₀ := compactEquiv ξ hL K' hK' a haL haK ((τ) w) B
  let c₁ := compactEquiv ξ hL K' hK' b hbL hbK ((τ) w) B
  let v := c₀ (S₀ f)
  let g := c₁.symm (LJτ z v)
  have hgl := compactFamily_spec ξ hL K' hK' a haL haK b hbL hbK modL B ⟨(τ) w, z.property⟩ v
  have hsrc : c₀.symm v = S₀ f := c₀.symm_apply_apply _
  have hJ : HasIntegral h₀ k₀ (radical b) Bl[w] qL (S₀ f)
      (fun l => eval (parabolic b) (leviInflatedInducingRepresentation h₁ k₁ Bl[w]) g l) := by
    change HasIntegral h₀ k₀ (radical b) Bl[w] qL (c₀.symm v) _ at hgl
    exact (congrArg (fun f => HasIntegral h₀ k₀ (radical b) Bl[w] qL f
      (fun l => eval (parabolic b) (leviInflatedInducingRepresentation h₁ k₁ Bl[w]) g l)) hsrc).mp hgl
  have hpull := HasIntegral.map_induced h₀ k₀ (radical b) qL ez.symm.toIntertwiningMap hJ
  have hf : inducedMap h₀ k₀ ez.symm.toIntertwiningMap (S₀ f) = f := by
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change ez.symm (ez (eval (parabolic a) (leviInflatedInducingRepresentation h₀ k₀ Al[w]) f l)) = _
    exact ez.symm_apply_apply _
  have hresult (l : rationalPoints L) :
      eval (parabolic b) (leviInflatedInducingRepresentation h₁ k₁ Al[w]) (S₁.symm g) l =
        ez.symm (eval (parabolic b) (leviInflatedInducingRepresentation h₁ k₁ Bl[w]) g l) := rfl
  change HasIntegral h₀ k₀ (radical b) Al[w] qL f
    (fun l => eval (parabolic b) (leviInflatedInducingRepresentation h₁ k₁ Al[w]) (S₁.symm g) l)
  exact (congrArg₂ (HasIntegral h₀ k₀ (radical b) Al[w] qL) hf (funext hresult).symm).mp hpull

include hx hy hRsurj hR₀ hR₁ in
set_option backward.isDefEq.respectTransparency.types false in
/-- The continued common-Levi pair commutes with the fixed restrictions
through the intermediate Levi on the common regular region. -/
theorem realizedContinuedPair_square
    (t : ℝ≥0) (ht : 0 < t) (he : (qG).map EqQ = t • qL)
    (z : ↥(p.regularRegion ∩ (qτ).regularRegion)) :
    ((qτ).continuedOperator ⟨z.val, z.property.2⟩).comp ((t : ℂ) • R₀) =
     R₁.comp (p.presentation.continuedOperator ⟨z.val, z.property.1⟩) := by
  have hsub := continuedPair_region_mem_lower o j hj hjc x y a b hx hy χ ξ hG hL hxG hyG haL eM A B
    eB fParam hpar K hK K' hK' hxK hyK haK R₀ hRsurj hR₀ p t ht he
  have hl := BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
    BruhatTits.dynamicUnipotentCompactOpenContainment F G hG y
  refine realizedContinuedIntertwining_square o j hj hjc x y a b hx hy d₀ d₁ h₀ h₁ eM qG qL
    K K' A B (parameterScheme χ) (parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) (fun z => Ag[z]) (fun z => eg₀[z]) (fun z => eg₁[z])
    (fun z => el₀[z]) (fun z => el₁[z]) R₀ R₁ hR₀ hR₁ t he hl (levi_isClosed ξ)
    (fun w => GJ ⟨w.val, p.converges w.property⟩) LJτ p.presentation qτ
    p.isOpen_region p.nonempty_region hsub ?_ ?_ z
  · intro w f
    let ew := eg₀[w.val]
    have h := compactFamily_spec χ hG K hK x hxG hxK y hyG hyK p.modulus A
      ⟨w.val, p.converges w.property⟩ (ew f)
    have hf : ew.symm (ew f) = f := ew.symm_apply_apply f
    exact (congrArg (fun f => HasIntegral d₀ u₀ (radical y) Ag[w.val] qG f _) hf).mp h
  · intro w
    exact lowerCompactFamily_represents a b χ ξ hL haL hbL eM A B eB fParam hpar K' hK' haK hbK
      modL ⟨w.val, hsub w.property⟩

variable (hRsurj' : Function.Surjective R₁)
  (p' : ContinuedPair χ hG K hK y hyG hyK x hxG hxK A)
  (modL' : SquaredModulusCompatibility h₁ k₁ h₀ k₀)

local notation "LFull'" => pairFullDomainRegion ξ K' hK' b hbL a B
local notation "LJ'" => compactFamily ξ hL K' hK' b hbL hbK a haL haK modL' B

variable (q' : RationalOperatorContinuationData LFull' LJ') [Nontrivial vl₀]

include hx hy hRsurj hRsurj' hR₀ hR₁ in
set_option backward.isDefEq.respectTransparency.types false in
/-- The round-trip scalar of the two actual ambient continuations equals
the corresponding scalar of the prescribed lower continuations times the
product of the two positive Haar comparison factors. -/
theorem exists_realizedContinuedRoundTrip_scalar_scale :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (z : X)
      (hz : z ∈ p.regularRegion ∩ p'.regularRegion)
      (hz' : (τ) z ∈ q.regularRegion ∩ q'.regularRegion)
      (sG sL : ℂ),
      p.presentation.continuedComposite p'.presentation ⟨z, hz⟩ = sG • LinearMap.id →
      q.continuedComposite q' ⟨(τ) z, hz'⟩ = sL • LinearMap.id →
      sG = (c : ℂ) * sL := by
  obtain ⟨t, ht, he⟩ := exists_realizedNestedQuotientMeasure_eq_smul o j hj hjc x y a b hx hy K hK K' hK'
  obtain ⟨r, hr, he'⟩ := exists_realizedNestedQuotientMeasure_eq_smul o j hj hjc y x b a hy hx K hK K' hK'
  refine ⟨r * t, mul_pos hr ht, ?_⟩
  intro z hz hz' sG sL hGsc hLsc
  have hF := realizedContinuedPair_square o j hj hjc x y a b hx hy χ ξ hG hL hxG hyG haL hbL eM A B
    eB fParam hpar K hK K' hK' hxK hyK haK hbK R₀ R₁ hRsurj hR₀ hR₁ p modL q t ht he
    ⟨z, ⟨hz.1, hz'.1⟩⟩
  have hR := realizedContinuedPair_square o j hj hjc y x b a hy hx χ ξ hG hL hyG hxG hbL haL eM A B
    eB fParam hpar K hK K' hK' hyK hxK hbK haK R₁ R₀ hRsurj' hR₁ hR₀ p' modL' q' r hr he'
    ⟨z, ⟨hz.2, hz'.2⟩⟩
  let J₀ := p.presentation.continuedOperator ⟨z, hz.1⟩
  let J₁ := p'.presentation.continuedOperator ⟨z, hz.2⟩
  let L₀ := q.continuedOperator ⟨(τ) z, hz'.1⟩
  let L₁ := q'.continuedOperator ⟨(τ) z, hz'.2⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : vl₀)
  obtain ⟨v, hv⟩ := hRsurj w
  have hforward (u : vg₀) : R₁ (J₀ u) = (t : ℂ) • L₀ (R₀ u) := by
    have h : L₀ ((t : ℂ) • R₀ u) = R₁ (J₀ u) := LinearMap.congr_fun hF u
    rw [map_smul] at h
    exact h.symm
  have hreverse (u : vg₁) : R₀ (J₁ u) = (r : ℂ) • L₁ (R₁ u) := by
    have h : L₁ ((r : ℂ) • R₁ u) = R₀ (J₁ u) := LinearMap.congr_fun hR u
    rw [map_smul] at h
    exact h.symm
  have hGv : J₁ (J₀ v) = sG • v := LinearMap.congr_fun hGsc v
  have hLv : L₁ (L₀ w) = sL • w := LinearMap.congr_fun hLsc w
  apply smul_left_injective ℂ hw
  calc
    sG • w = R₀ (J₁ (J₀ v)) := by rw [hGv, map_smul, hv]
    _ = ((↑(r * t) : ℂ) * sL) • w := by
      rw [hreverse, hforward, hv, map_smul, hLv, smul_smul, smul_smul]
      push_cast
      rw [mul_assoc]

include hx hy eB hpar in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inclusion of the lower compact subgroup supplies the two fixed
restrictions used in the continued round-trip comparison. -/
theorem exists_realizedContinuedRoundTrip_scalar_scale_of_compact_inclusion
    (heM : ∀ l, (eM l : rationalPoints G) =
      (RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
        (l : rationalPoints L) : rationalPoints G))
    (hKK' : ∀ k : K', (RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
      (k : rationalPoints L) : rationalPoints G) ∈ K) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (z : X)
      (hz : z ∈ p.regularRegion ∩ p'.regularRegion)
      (hz' : (τ) z ∈ q.regularRegion ∩ q'.regularRegion)
      (sG sL : ℂ),
      p.presentation.continuedComposite p'.presentation ⟨z, hz⟩ = sG • LinearMap.id →
      q.continuedComposite q' ⟨(τ) z, hz'⟩ = sL • LinearMap.id →
      sG = (c : ℂ) * sL := by
  obtain ⟨S₀, hS₀, hS₀eq⟩ := exists_realizedCommonLeviFixedCompactRestriction
    o j hj hjc x a hx hG hL χ ξ hxG haL eM A B eB τ hpar
    K hK K' hK' hxK haK heM hKK'
  obtain ⟨S₁, hS₁, hS₁eq⟩ := exists_realizedCommonLeviFixedCompactRestriction
    o j hj hjc y b hy hG hL χ ξ hyG hbL eM A B eB τ hpar
    K hK K' hK' hyK hbK heM hKK'
  exact exists_realizedContinuedRoundTrip_scalar_scale o j hj hjc x y a b hx hy χ ξ hG hL
    hxG hyG haL hbL eM A B eB fParam hpar K hK K' hK' hxK hyK haK hbK
    S₀ S₁ hS₀ hS₀eq hS₁eq p modL q hS₁ p' modL' q'

end Langlands.Plancherel.StandardIntertwining
