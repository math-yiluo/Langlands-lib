import Langlands.Representation.Plancherel.DynamicCommonLeviGalleryComposite

/-! # Cleared actual endpoint operators on the represented regular locus -/

noncomputable section

universe u uV

set_option quotPrecheck false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviContinuation
open DynamicCommonLeviCompact DynamicCommonLeviStructuralComparison
open ActualCommonLeviTensor UnramifiedOperatorFamily StandardIntertwining

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  equalitySubgroupMeasurable equalitySubgroupBorel
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (x y : GalleryVertex χ)

set_option hygiene false in
local notation "Γ" => rationalPoints G
local notation "d" => galleryVertexData hG ha
local notation "V" => representedComplement (d x.opposite) (d y)
local notation "μV" => galleryPairHaar hG ha K hK x y
local notation "h₀" => commonDecomposition χ x.val x.property
local notation "h₁" => commonDecomposition χ y.val y.property
local notation "hU₀" => radical_isClosed x.val
local notation "hU₁" => radical_isClosed y.val
local notation "hδ₀" => radical_unimodular x.val hG
local notation "hδ₁" => radical_unimodular y.val hG
local notation "hP₀" => parabolic_isClosed x.val
local notation "hP₁" => parabolic_isClosed y.val
local notation "hr₀" => commonProjection_continuous χ x.val x.property
local notation "hr₁" => commonProjection_continuous χ y.val y.property
local notation "L" => parameterScheme χ
local notation "e" => parameterHomeomorph χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "hProj" => parameterProjection_continuous χ
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "νM" => leviNormCharacters χ
local notation "hν" => normCharacters_continuous χ
local notation "hνM" => fun i => (normCharacters_continuous χ i).comp (parameterHomeomorph χ).symm.continuous

variable
  (hxK : ∀ g : Γ, ∃ r : parabolic x.val, ∃ k : K, g = (r : Γ) * (k : Γ))
  (hyK : ∀ g : Γ, ∃ r : parabolic y.val, ∃ k : K, g = (r : Γ) * (k : Γ))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A)
  (q : PairContinuation χ hG K hK x.val x.property hxK y.val y.property hyK p.modulus A
    p.region p.converges)

local notation "B" => twistObject χ
local notation "σ" => fun z : X => SmoothRep.pullback e (B z A)
local notation "C₀" => CompactInductionPicture h₀ K A
local notation "C₁" => CompactInductionPicture h₁ K A
local notation "κ₀" => fun z => compactEquiv χ hG K hK x.val x.property hxK z A
local notation "κ₁" => fun z => compactEquiv χ hG K hK y.val y.property hyK z A
local notation "E₀" => compactRepresentedGalleryEquiv hG ha K hK A x hxK
local notation "E₁" => compactRepresentedGalleryEquiv hG ha K hK A y hyK
local notation "ρ₀" => fun z : X => unramifiedCompactRepresentation h₀ hU₀ hδ₀ K hP₀ hK hxK
  νM hνM hr₀ A (parameterTransport χ z)
local notation "ρ₁" => fun z : X => unramifiedCompactRepresentation h₁ hU₁ hδ₁ K hP₁ hK hyK
  νM hνM hr₁ A (parameterTransport χ z)
local notation "J" => fun z : p.region =>
  pairFamily χ K hK x.val x.property y.val y.property p.modulus A ⟨z.val, p.converges z.property⟩
local notation "Jc" => compactInductionIntertwinerFamily L h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
  hP₀ hP₁ hxK hyK hr₀ hr₁ e hν A J

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency.types false in
private def clearedCompactPairOperator (z : X) : (ρ₀ z).IntertwiningMap (ρ₁ z) where
  toLinearMap := q.numerator z
  isIntertwining' g := by
    refine rationalOperatorContinuation_numerator_commutes L hProj hL
      p.isOpen_region p.nonempty_region (fun _ h => h) (fun w => (Jc w).toLinearMap) q
      (fun w => ρ₀ w g) (fun w => ρ₁ w g) ?_ ?_ (fun w => (Jc w).isIntertwining' g) z
    · exact unramifiedCompactRepresentation_transport_polynomial h₀ hU₀ hδ₀ K hP₀ hK hxK
        e (normCharacters χ) hν hr₀ A g
    · exact unramifiedCompactRepresentation_transport_polynomial h₁ hU₁ hδ₁ K hP₁ hK hyK
        e (normCharacters χ) hν hr₁ A g

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Conjugate the entire cleared numerator to a represented intertwiner at
every parameter, with the original compact carrier. -/
def representedClearedPairOperator (z : X) :
    (representedInduction hG (d x) (σ z)).representation.IntertwiningMap
      (representedInduction hG (d y) (σ z)).representation :=
  let transport := compactInductionIntertwinerEquiv h₀ hU₀ hδ₀ h₁ hU₁ hδ₁ K hK
    hP₀ hP₁ hxK hyK hr₀ hr₁ νM hνM A (parameterTransport χ z)
  representedDynamicIntertwiner hG (d x) (d y) x.property y.property (B z A)
    (transport.symm (clearedCompactPairOperator hG K hK x y hxK hyK A p q z))

local notation "N" => representedClearedPairOperator hG ha K hK x y hxK hyK A p q

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The represented cleared map has exactly the original compact numerator. -/
theorem representedClearedPairOperator_compact_apply (z : X) (v : C₀) :
    N z (E₀ z v) = E₁ z (q.numerator z v) := by
  let e₀ := representedDynamicInductionEquiv hG (d x) x.property (B z A)
  let e₁ := representedDynamicInductionEquiv hG (d y) y.property (B z A)
  change e₁.symm ((κ₁ z).symm (q.numerator z ((κ₀ z) (e₀ (e₀.symm ((κ₀ z).symm v)))))) =
    e₁.symm ((κ₁ z).symm (q.numerator z v))
  rw [e₀.apply_symm_apply, LinearEquiv.apply_symm_apply]

local notation "j" => (Subtype.val : V → Γ)
local notation "E" => compactEvalLinear h₁ K A 1
local notation "samples" =>
  fun f : C₀ => compactTestSectionValues L h₀ hU₀ hδ₀ K hP₀ hK hxK hr₀ e hν A f j

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compactNumerator_zeroEval_of_compactTest
    (z : X) (hz : q.denominator.val z = 0) (f : C₀)
    (hf : HasCompactSupport (fun v : V => samples f v z)) :
    E (q.numerator z f) = 0 := by
  let c := galleryQuotientChart hG ha K hK x y
  let measure := c.scale • μV
  let q' : ContinuedPair χ hG K hK x.val x.property hxK y.val y.property hyK A :=
    { p with presentation := q }
  obtain ⟨S, hS, htests⟩ := exists_compactTestPolynomialIntegral L h₀ hU₀ hδ₀ K hP₀ hK hxK hr₀
    e hν A f j measure continuous_subtype_val z hf
  have htest (w : p.region) :
      E (q.continuedOperator ⟨w.val, q.subset_regularRegion w.property⟩ f) = S w.val := by
    let wr : q'.regularRegion := ⟨w.val, q.subset_regularRegion w.property⟩
    let fw := (κ₀ w.val).symm f
    have hfw : HasCompactSupport (fun v : V => eval _ _ fw v.val) := (htests w.val).1
    have hcomp := ContinuedPair.operator_compact χ hG K hK x.val x.property hxK
      y.val y.property hyK A q' wr
    let Jw := ContinuedPair.operator χ hG K hK x.val x.property hxK y.val y.property hyK A q' wr
    have hVal : E (q.continuedOperator ⟨w.val, q.subset_regularRegion w.property⟩ f) =
        eval _ _ (Jw fw) 1 :=
      (congrArg (fun J₀ : C₀ →ₗ[ℂ] C₁ => E (J₀ f)) hcomp).symm
    apply Module.eval_apply_injective ℂ
    ext ℓ
    change ℓ (E (q.continuedOperator ⟨w.val, q.subset_regularRegion w.property⟩ f)) = ℓ (S w.val)
    rw [hVal]
    have hJ := (continuedPair_compactTest_integral hG ha K hK x y c hxK hyK A q' wr fw hfw ℓ).2
    exact hJ.trans ((htests w.val).2 ℓ).symm
  have hZero := rationalUnramifiedPolynomial_eq_zero_of_isOpen L hProj hL
    p.isOpen_region p.nonempty_region (show p.region ⊆ Set.univ from Set.subset_univ _)
    (fun w => E (q.numerator w.val f) - q.denominator.val w.val • S w.val)
    (((q.polynomial f).linearMap E).sub (hS.regular_smul q.denominator)) (by
      intro w hw
      let w' : p.region := ⟨w, hw⟩
      change E (q.numerator w f) - q.denominator.val w • S w = 0
      rw [LinearMap.congr_fun (q.clears w') f, LinearMap.smul_apply, map_smul,
        ← htest w', q.continuedOperator_agrees w', sub_self])
    ⟨z, Set.mem_univ z⟩
  change E (q.numerator z f) - q.denominator.val z • S z = 0 at hZero
  simpa only [hz, zero_smul, sub_zero] using hZero

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency.types false in
private theorem representedClearedPairOperator_zeroEval (z : X) (hz : q.denominator.val z = 0)
    (f : representedInduction hG (d x) (σ z))
    (hf : f ∈ representedBoundaryVanishing hG (d x) (d y) (σ z)) :
    eval _ _ (N z f) 1 = 0 := by
  let e₀ := representedDynamicInductionEquiv hG (d x) x.property (B z A)
  let e₁ := representedDynamicInductionEquiv hG (d y) y.property (B z A)
  let f₀ := (κ₀ z) (e₀ f)
  have he : (κ₀ z).symm f₀ = e₀ f := (κ₀ z).symm_apply_apply _
  obtain ⟨D, hD, hvan⟩ := (representedBoundaryVanishing_iff hG (d x) (d y) (d x.opposite)
    x.property (σ z) f).mp hf
  have hsupport : HasCompactSupport (fun v : V => samples f₀ v z) := by
    refine HasCompactSupport.intro hD (fun v hv => ?_)
    change eval _ _ ((κ₀ z).symm f₀) v.val = 0
    rw [he]
    exact (representedDynamicInductionEquiv_eval hG (d x) x.property (B z A) f v.val).trans
      (hvan v hv)
  have hin : E₀ z f₀ = f := by
    change e₀.symm ((κ₀ z).symm f₀) = f
    rw [he, e₀.symm_apply_apply]
  have hOut := representedClearedPairOperator_compact_apply hG ha K hK x y hxK hyK A p q z f₀
  rw [hin] at hOut
  let w := q.numerator z f₀
  have hEval : eval _ _ (E₁ z w) 1 = E w := by
    have ht := representedDynamicInductionEquiv_eval hG (d y) y.property (B z A) (E₁ z w) 1
    change eval _ _ (e₁ (e₁.symm ((κ₁ z).symm w))) 1 = eval _ _ (E₁ z w) 1 at ht
    rw [e₁.apply_symm_apply] at ht
    have h := compactEquiv_eval χ hG K hK y.val y.property hyK z A ((κ₁ z).symm w) 1
    change E ((κ₁ z) ((κ₁ z).symm w)) = eval _ _ ((κ₁ z).symm w) 1 at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact ht.symm.trans h.symm
  exact (congrArg (fun g : representedInduction hG (d y) (σ z) => eval _ _ g 1) hOut).trans
    (hEval.trans (compactNumerator_zeroEval_of_compactTest hG ha K hK x y hxK hyK A p q z hz f₀ hsupport))

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- At a `PQ`-regular parameter, the original numerator vanishes if its
denominator vanishes. -/
theorem compactPairNumerator_eq_zero_of_PQRegular (z : X)
    (hPQ : representedIsPQRegular hG (d x) (d y) (σ z))
    (hz : q.denominator.val z = 0) : q.numerator z = 0 := by
  let Jg := galleryIntegralOperator hG ha K hK (σ z) x y
  have hJg := galleryIntegralOperator_spec hG ha K hK (σ z) x y hPQ
  have hJ : representedIsIntegralIntertwiner hG (d x) (d y) (d x.opposite) μV (σ z) (Jg + N z) := by
    intro f hf ℓ
    have h := hJg f hf ℓ
    refine ⟨h.1, ?_⟩
    change ℓ (eval _ _ (Jg f) 1 + eval _ _ (N z f) 1) = _
    rw [representedClearedPairOperator_zeroEval hG ha K hK x y hxK hyK A p q z hz f hf, add_zero]
    exact h.2
  have hEq : Jg + N z = Jg :=
    (existsUnique_representedIntegralOperator hG (d x) (d y) (d x.opposite) x.property ha μV
      (σ z) hPQ).unique hJ hJg
  have hN : N z = 0 := add_left_cancel (hEq.trans (add_zero Jg).symm)
  apply LinearMap.ext
  intro v
  apply (E₁ z).injective
  have hv := representedClearedPairOperator_compact_apply hG ha K hK x y hxK hyK A p q z v
  rw [hN] at hv
  exact hv.symm.trans ((E₁ z).map_zero).symm

end Langlands.Plancherel.DynamicCommonLeviPresentations
