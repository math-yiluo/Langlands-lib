import Langlands.Representation.Plancherel.ProductInducedOrbitForm
import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport

/-! # Compact action on actual coherent smooth orbit sections -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory MeasureTheory
open scoped NNReal ENNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- The full product group acts on all actual inducing fibers pointwise. -/
def productInducedOrbitRepresentation :
    Representation ℂ (G × G) (ProductInducedOrbitSections ν π h hU) where
  toFun x :=
    { toFun := fun q A => (productInducedCoefficientObject h hU A.val.obj).representation x (q A)
      map_add' := fun q r => funext fun A => map_add _ _ _
      map_smul' := fun c q => funext fun A => map_smul _ c _ }
  map_one' := by
    ext q A
    exact congrArg (fun T => T (q A))
      (productInducedCoefficientObject h hU A.val.obj).representation.map_one
  map_mul' x y := by
    ext q A
    exact congrArg (fun T => T (q A))
      ((productInducedCoefficientObject h hU A.val.obj).representation.map_mul x y)

/-- Every inducing equivalence intertwines the full action, so coherence is stable. -/
theorem productInducedOrbitRepresentation_coherent (x : G × G)
    {q : ProductInducedOrbitSections ν π h hU}
    (hq : q ∈ coherentProductInducedOrbitSections ν π h hU) :
    productInducedOrbitRepresentation h hU ν π x q ∈
      coherentProductInducedOrbitSections ν π h hU := by
  intro A B a
  change (productInducedCoefficientObject h hU B.val.obj).representation x (q B) = _
  rw [hq A B a]
  exact (productInducedCoefficientTransport_action h hU a x (q A)).symm

/-- The coherent all-representative space carries the full product-group action. -/
def coherentProductInducedOrbitRepresentation :
    Representation ℂ (G × G) (coherentProductInducedOrbitSections ν π h hU) :=
  (productInducedOrbitRepresentation h hU ν π).subrepresentation
    (coherentProductInducedOrbitSections ν π h hU)
    (fun x _ hq => productInducedOrbitRepresentation_coherent h hU ν π x hq)

variable (K : OpenSubgroup G) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

omit [Fintype J] in
/-- Compact restriction intertwines the actual action with one fixed compact
coefficient operator, independent of the character parameter. -/
theorem productInducedOrbitRepresentation_restriction (k : K.prod K)
    (q : ProductInducedOrbitSections ν π h hU) (z : J → Circle) :
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU
          (productInducedOrbitRepresentation h hU ν π k q)) z =
      productInducedCompactRepresentation h K π.obj k
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU q) z) :=
  congrArg (fun T => T (q (unitaryOrbitParameterRepresentative ν π e z)))
    ((productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryTorusParameter ν e z) π.obj).isIntertwining' k)

/-- The actual compact action preserves finite scalar smoothness as well as
coherence, without a continuity assumption on the supplied torus coordinates. -/
theorem productInducedOrbitRepresentation_smooth_mem (k : K.prod K)
    {q : ProductInducedOrbitSections ν π h hU}
    (hq : q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    productInducedOrbitRepresentation h hU ν π k q ∈
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := by
  refine ⟨productInducedOrbitRepresentation_coherent h hU ν π k hq.1, ?_⟩
  have ht := mem_finiteSmoothFamilies_linearMap hq.2
    (productInducedCompactRepresentation h K π.obj k)
  change productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    (productInducedOrbitPullback ν π e h hU
      (productInducedOrbitRepresentation h hU ν π k q)) ∈
      finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)
  have heq := funext (productInducedOrbitRepresentation_restriction
    h hU ν π K hP hK hν hr hPK e k q)
  rw [heq]
  exact ht

/-- The compact product subgroup acts on the existing space of actual coherent
smooth orbit sections, by the original action at every inducing representative. -/
def productInducedSmoothOrbitCompactRepresentation :
    Representation ℂ (K.prod K)
      (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :=
  Representation.subrepresentation
    ((productInducedOrbitRepresentation h hU ν π).comp (K.prod K).toSubgroup.subtype)
    (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (fun k _ hq => productInducedOrbitRepresentation_smooth_mem
      h hU ν π K hP hK hν hr hPK e k hq)

/-- The action is literally the actual product-induced action at each fiber. -/
@[simp]
theorem productInducedSmoothOrbitCompactRepresentation_apply (k : K.prod K)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) :
    (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k q).val A =
      (productInducedCoefficientObject h hU A.val.obj).representation k (q.val A) := rfl

/-- On normalized induced functions the compact action is right translation. -/
theorem productInducedSmoothOrbitCompactRepresentation_eval (k : K.prod K)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) (x : G × G) :
    eval _ _
        ((productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k q).val A) x =
      eval _ _ (q.val A) (x * (k : G × G)) := rfl

/-- Actual parameter pullback followed by compact restriction. -/
def productInducedSmoothOrbitCompactRestriction :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      ((J → Circle) → ProductInducedCompactPicture h K π.obj) :=
  (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).toLinearMap.comp
    ((productInducedOrbitPullback ν π e h hU).comp
      (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK).subtype)

/-- Coherence and faithful actual compact restriction detect every section. -/
theorem productInducedSmoothOrbitCompactRestriction_injective :
    Function.Injective
      (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e) := by
  intro q r hqr
  apply (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK).injective
  apply Subtype.ext
  exact (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).injective hqr

private def compactFamilyRepresentation :
    Representation ℂ (K.prod K) ((J → Circle) → ProductInducedCompactPicture h K π.obj) where
  toFun k :=
    { toFun := fun F z => productInducedCompactRepresentation h K π.obj k (F z)
      map_add' := fun F H => funext fun z => map_add _ _ _
      map_smul' := fun c F => funext fun z => map_smul _ c _ }
  map_one' := by
    apply LinearMap.ext
    intro F
    funext z
    exact congrArg (fun T => T (F z))
      (productInducedCompactRepresentation h K π.obj).map_one
  map_mul' k l := by
    apply LinearMap.ext
    intro F
    funext z
    exact congrArg (fun T => T (F z))
      ((productInducedCompactRepresentation h K π.obj).map_mul k l)

omit [LocallyCompactSpace G] in
private theorem finiteCompactFamily_isSmoothVector
    {F : (J → Circle) → ProductInducedCompactPicture h K π.obj}
    (hF : F ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)) :
    IsSmoothVector (compactFamilyRepresentation h π K (J := J)) F := by
  apply (show finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj) ≤
      smoothVectors (compactFamilyRepresentation h π K (J := J)) from ?_) hF
  apply Submodule.span_le.mpr
  rintro _ ⟨f, v, rfl⟩
  obtain ⟨L, hL⟩ := smoothInduced_smooth _ _ v
  refine ⟨L, ?_⟩
  intro k
  funext z
  change productInducedCompactRepresentation h K π.obj k.val (f.val z • v) = f.val z • v
  exact (map_smul _ _ _).trans (congrArg (fun w => f.val z • w) (hL k))

/-- A single open subgroup of the compact product fixes the entire section,
simultaneously at every parameter and every actual inducing representative. -/
theorem productInducedSmoothOrbitCompactRepresentation_isSmooth :
    IsSmooth (productInducedSmoothOrbitCompactRepresentation
      h hU ν π K hP hK hν hr hPK e) := by
  intro q
  obtain ⟨L, hL⟩ := finiteCompactFamily_isSmoothVector h π K q.property.2
  refine ⟨L, ?_⟩
  intro k
  apply productInducedSmoothOrbitCompactRestriction_injective h hU ν π K hP hK hν hr hPK e
  funext z
  exact (productInducedOrbitRepresentation_restriction
    h hU ν π K hP hK hν hr hPK e k.val q.val z).trans (congrFun (hL k) z)

/-- The actual compact action bundled in the canonical smooth representation category. -/
def productInducedSmoothOrbitCompactObject : SmoothRep ℂ (K.prod K) :=
  ⟨Rep.of (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e),
    productInducedSmoothOrbitCompactRepresentation_isSmooth h hU ν π K hP hK hν hr hPK e⟩

/-- Each smooth orbit section is a smooth vector for the raw full product-group
action. This does not assert full-group stability of parameter smoothness. -/
theorem productInducedSmoothOrbitSections_isSmoothVector
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    IsSmoothVector (productInducedOrbitRepresentation h hU ν π) q.val := by
  obtain ⟨L, hL⟩ := productInducedSmoothOrbitCompactRepresentation_isSmooth
    h hU ν π K hP hK hν hr hPK e q
  let H : OpenSubgroup (G × G) :=
    { toSubgroup := L.toSubgroup.map (K.prod K).toSubgroup.subtype
      isOpen' := (K.prod K).isOpen.isOpenMap_subtype_val _ L.isOpen }
  refine ⟨H, ?_⟩
  intro x
  obtain ⟨k, hk, hkx⟩ := x.property
  change productInducedOrbitRepresentation h hU ν π x.val q.val = q.val
  rw [← hkx]
  exact congrArg Subtype.val (hL ⟨k, hk⟩)

/-- Each entire section has a common stabilizer of the source's form H × H,
with H compact open in G and contained in the chosen compact subgroup. -/
theorem productInducedSmoothOrbitSections_exists_product_stabilizer
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ H : OpenSubgroup G, H ≤ K ∧ IsCompact (H : Set G) ∧
      ∀ x : H.prod H, productInducedOrbitRepresentation h hU ν π x q.val = q.val := by
  obtain ⟨L, hL⟩ := productInducedSmoothOrbitSections_isSmoothVector
    h hU ν π K hP hK hν hr hPK e q
  let H : OpenSubgroup G :=
    (OpenSubgroup.comap (MonoidHom.inl G G) (continuous_id.prodMk continuous_const) L ⊓
      OpenSubgroup.comap (MonoidHom.inr G G) (continuous_const.prodMk continuous_id) L) ⊓ K
  have hHK : H ≤ K := fun _ hg => hg.2
  refine ⟨H, hHK, hK.of_isClosed_subset H.isClosed hHK, ?_⟩
  intro x
  have hxL : x.val ∈ L := by
    have hleft : (x.val.1, 1) ∈ L := x.property.1.1.1
    have hright : (1, x.val.2) ∈ L := x.property.2.1.2
    simpa using L.mul_mem hleft hright
  exact hL ⟨x.val, hxL⟩

section OrbitForm

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P]
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- The compact action preserves the canonical scalar pairing at every actual
discrete-series class, using the original inverse-degree fiber forms. -/
theorem unitaryOrbitProductPairing_compact_action (k : K.prod K)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e
        (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k q)
        (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k r) ω =
      unitaryOrbitProductPairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω := by
  obtain ⟨A, rfl⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitProductPairing_representative, unitaryOrbitProductPairing_representative]
  exact (unitaryOrbitRepresentativeProductForm
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).invariant k (q.val A) (r.val A)

variable [Finite (M ⧸ (commonNormKernel ν ⊔ C))]

/-- The existing entire orbit-integral core is preserved by the actual compact
action, with its original orbit measure and character-measure scale. -/
theorem productInducedSmoothOrbitCore_compact_action (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] (k : K.prod K)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner
        (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k q)
        (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e k r) =
      (productInducedSmoothOrbitCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η).inner q r := by
  rw [productInducedSmoothOrbitCore_inner_integral, productInducedSmoothOrbitCore_inner_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (unitaryOrbitProductPairing_compact_action
      h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq k q r)

/-- The canonical positive orbit-integral form, equipped with its proved
invariance under the compact action on actual coherent smooth sections. -/
def productInducedSmoothOrbitCompactForm (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    InvariantPositiveForm
      (productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e) where
  toInnerProductCore := productInducedSmoothOrbitCore
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η
  invariant := productInducedSmoothOrbitCore_compact_action
    h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq he η

/-- Equipping the form with compact invariance leaves the entire previously
constructed orbit-integral core definitionally unchanged. -/
@[simp]
theorem productInducedSmoothOrbitCompactForm_toInnerProductCore (he : Continuous e)
    (η : Measure (unitaryUnramifiedCharacters ν))
    [IsFiniteMeasure η] [η.IsOpenPosMeasure] :
    (productInducedSmoothOrbitCompactForm
      h hU ν π K hP hK hν hr hPK e hG hδ hcof C hC μ hsq he η).toInnerProductCore =
      productInducedSmoothOrbitCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he η := rfl

end OrbitForm

end Langlands.Plancherel
