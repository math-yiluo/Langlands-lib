import Langlands.Global.Factors.RelativeWeilLocalEpsilonTransport
import Langlands.LocalFactor.BrauerKernel.RamifiedTwist
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof

/-! # Standalone Brauer relations as presentations over the bottom field -/

noncomputable section

universe u w uV

namespace Langlands.LocalFactor.NonabelianBrauer

open VirtualRepresentation CommonClosure Weil.Local FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The generator over the bottom field formed by the image of a standalone extension `E`
and the field characters of the two continuous characters `α`, `β` of `W_E`. -/
def imageGenerator (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (α β : localWeilGroup E →ₜ* ℂˣ) :
    Generator F (Correspondence.baseExtension F) where
  extension := LocalClassField.extensionFiniteIntermediate F E g
  inclusion := baseExtension_le F _
  first := CommonClosureSpectralAnalytic.fieldCharacterEquiv F e _
    (SystemEpsilon.imageCharacter F E g α)
  second := CommonClosureSpectralAnalytic.fieldCharacterEquiv F e _
    (SystemEpsilon.imageCharacter F E g β)

/-- The virtual class of an image generator is the restriction to the bottom field of the
standalone induced class along `W_E → W_F`. -/
theorem generatorClass_imageGenerator (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (α β : localWeilGroup E →ₜ* ℂˣ) :
    generatorClass.{u, uV} F e _ (imageGenerator F e E g α β) =
      ExactGrothendieckGroup.continuousRestrict
        ((Correspondence.baseWeilEquiv F).symm :
          weilSubgroup F (Correspondence.baseExtension F) →ₜ* localWeilGroup F)
        (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
          (extensionWeilMap_isOpenEmbedding F E g)
          (ExactGrothendieckGroup.characterClass.{u, max u uV} α -
            ExactGrothendieckGroup.characterClass.{u, max u uV} β)) := by
  have hc (χ : localWeilGroup E →ₜ* ℂˣ) :
      characterClass.{u, uV} F e (LocalClassField.extensionFiniteIntermediate F E g)
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e _
            (SystemEpsilon.imageCharacter F E g χ)) =
        ExactGrothendieckGroup.characterClass (SystemEpsilon.imageCharacter F E g χ) := by
    rw [characterClass, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv]
  rw [SystemEpsilon.continuousRestrict_continuousInduceAlong, map_sub,
    SystemEpsilon.virtualEquiv_symm_characterClass,
    SystemEpsilon.virtualEquiv_symm_characterClass, ← hc, ← hc]
  rfl

/-- Changing the carrier universe of a standalone induced character line. -/
theorem universeMap_continuousInduceAlong_characterClass (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (χ : localWeilGroup E →ₜ* ℂˣ) :
    (ExactGrothendieckGroup.universeMap
        (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
          (extensionWeilMap_isOpenEmbedding F E g)
          (ExactGrothendieckGroup.characterClass.{u, w} χ)) :
        ExactGrothendieckGroup.Continuous.{u, max u uV} (localWeilGroup F)) =
      ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
        (extensionWeilMap_isOpenEmbedding F E g)
        (ExactGrothendieckGroup.characterClass.{u, max u uV} χ) := by
  unfold ExactGrothendieckGroup.characterClass
  rw [ExactGrothendieckGroup.continuousInduceAlong_ofRepresentation,
    ExactGrothendieckGroup.continuousInduceAlong_ofRepresentation]
  exact ExactGrothendieckGroup.universeMap_ofRepresentation_of_equiv _ _
    (induceAlongEquivOfEquiv _ _ (characterLineUniverseEquiv χ.toMonoidHom))

/-- **Standalone relations are actual presentation relations.** Let `E_j` be standalone
extensions of `F` with embeddings `g_j`, and `α_j`, `β_j` continuous characters of
`W_{E_j}`. If `Σ_j n_j Ind_{E_j/F}([α_j] - [β_j]) = 0` in the continuous exact virtual
group of `W_F`, in any carrier universe, then the corresponding combination of image
generators lies in the kernel of the actual presentation over the bottom field. -/
theorem presentationMap_imageGenerator_eq_zero (e : ReciprocityFamily F) {J : Type*}
    [Fintype J] (E : J → PadicField.{u} p) (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (h : ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (ExactGrothendieckGroup.characterClass.{u, w} (α j) -
          ExactGrothendieckGroup.characterClass.{u, w} (β j)) = 0) :
    presentationMap.{u, uV} F e (Correspondence.baseExtension F)
      (∑ j, n j • Finsupp.single (imageGenerator F e (E j) (g j) (α j) (β j)) 1) = 0 := by
  apply Subtype.ext
  change virtualPresentation F e _ _ = 0
  rw [map_sum]
  have hj : ∀ j, virtualPresentation.{u, uV} F e _
      (n j • Finsupp.single (imageGenerator F e (E j) (g j) (α j) (β j)) 1) =
      ExactGrothendieckGroup.continuousRestrict
        ((Correspondence.baseWeilEquiv F).symm :
          weilSubgroup F (Correspondence.baseExtension F) →ₜ* localWeilGroup F)
        (ExactGrothendieckGroup.universeMap
          (n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
            (extensionWeilMap_isOpenEmbedding F (E j) (g j))
            (ExactGrothendieckGroup.characterClass.{u, w} (α j) -
              ExactGrothendieckGroup.characterClass.{u, w} (β j)))) := by
    intro j
    rw [map_zsmul, virtualPresentation, Finsupp.linearCombination_single, one_smul,
      generatorClass_imageGenerator]
    simp only [map_zsmul, map_sub]
    rw [universeMap_continuousInduceAlong_characterClass.{u, w, uV} F (E j) (g j) (α j),
      universeMap_continuousInduceAlong_characterClass.{u, w, uV} F (E j) (g j) (β j)]
  simp_rw [hj]
  rw [← map_sum, ← map_sum, h, map_zero, map_zero]

/-- The abelian epsilon evaluation of a combination of image generators. -/
theorem evaluationMap_imageGenerator (e : ReciprocityFamily F) {J : Type*} [Fintype J]
    (E : J → PadicField.{u} p) (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (ψ : AdditiveCharacter F (Correspondence.baseExtension F)) (measures : HaarFamily F) :
    evaluationMap F _ ψ measures
        (∑ j, n j • Finsupp.single (imageGenerator F e (E j) (g j) (α j) (β j)) 1) =
      ∑ j, n j • Additive.ofMul
        (generatorValue F _ ψ measures (imageGenerator F e (E j) (g j) (α j) (β j))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, evaluationMap_single, one_smul]

section Standalone

open Correspondence LocalClassField

/-- The image generator of two quasicharacters of a standalone extension, read through the
family's reciprocity component transported to that extension. -/
def standaloneGenerator (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (η η' : QuasiCharacter E) :
    Generator F (baseExtension F) :=
  imageGenerator F e E g (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) η)
    (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) η')

/-- A quasicharacter of a standalone extension, transported to the field character of its
image in the common closure. -/
def transportedCharacter (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (η : QuasiCharacter E) : FieldCharacter F (extensionFiniteIntermediate F E g) :=
  PadicField.ConductorTransport.quasicharacter E
    ((extensionFiniteIntermediate F E g).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E g) η

/-- The transported Weil character of a quasicharacter is the Weil character of the
transported quasicharacter for the family's component at the image. -/
theorem imageCharacter_weilCharacter (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (η : QuasiCharacter E) :
    SystemEpsilon.imageCharacter F E g
        (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) η) =
      weilCharacter F e (extensionFiniteIntermediate F E g)
        (PadicField.ConductorTransport.quasicharacter E
          ((extensionFiniteIntermediate F E g).asPadicField (p := p))
          (extensionIntermediatePadicEquiv F E g) η) := by
  let := E.canonicalTopologicalData.topology
  let := (fieldData F (extensionFiniteIntermediate F E g)).topology
  apply ContinuousMonoidHom.ext
  intro w
  obtain ⟨v, rfl⟩ := (extensionImageWeilEquiv F E g).surjective w
  have hu : (extensionIntermediateUnitsEquiv F E g).symm
      (reciprocityUnits F e _ (extensionImageWeilEquiv F E g v)) =
      RankOne.reciprocityUnits E (extensionReciprocityCandidate F E g e) v :=
    rfl
  apply Units.ext
  change (η (RankOne.reciprocityUnits E (extensionReciprocityCandidate F E g e)
      ((extensionImageWeilEquiv F E g).symm (extensionImageWeilEquiv F E g v))) : ℂ) =
    (η ((extensionIntermediateUnitsEquiv F E g).symm
      (reciprocityUnits F e _ (extensionImageWeilEquiv F E g v))) : ℂ)
  rw [ContinuousMulEquiv.symm_apply_apply, hu]

/-- The field character of a transported Weil character is the transported
quasicharacter. -/
theorem fieldCharacterEquiv_imageCharacter (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (η : QuasiCharacter E) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F e _
        (SystemEpsilon.imageCharacter F E g
          (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) η)) =
      transportedCharacter F E g η := by
  rw [imageCharacter_weilCharacter]
  exact fieldCharacterEquiv_weilCharacter F e _ _

/-- The first character of a standalone generator is the transported quasicharacter. -/
theorem standaloneGenerator_first (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (η η' : QuasiCharacter E) :
    (standaloneGenerator F e E g η η').first = transportedCharacter F E g η :=
  fieldCharacterEquiv_imageCharacter F e E g η

/-- The second character of a standalone generator is the transported quasicharacter. -/
theorem standaloneGenerator_second (e : ReciprocityFamily F) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (η η' : QuasiCharacter E) :
    (standaloneGenerator F e E g η η').second = transportedCharacter F E g η' :=
  fieldCharacterEquiv_imageCharacter F e E g η'

/-- The bottom field has the absolute ramification index of the base field. -/
theorem ramificationIndex_baseExtension :
    (fieldData F (baseExtension F)).ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex :=
  ClassFieldTheory.Local.ArithmeticNormalizationProof.ramificationIndex_eq_of_algEquiv
    (baseFieldPadicEquiv F)

section Image

variable (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)

local instance bridgeImageAlgebra :
    Algebra (Padic p) (extensionFiniteIntermediate F E g).field :=
  ((extensionFiniteIntermediate F E g).asPadicField (p := p)).algebra

local instance bridgeImageTopology : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology

local instance bridgeImageFieldTopology :
    TopologicalSpace (extensionFiniteIntermediate F E g).field :=
  (fieldData F (extensionFiniteIntermediate F E g)).topology

/-- The image of a standalone extension has its absolute ramification index. -/
theorem ramificationIndex_extensionFiniteIntermediate :
    (fieldData F (extensionFiniteIntermediate F E g)).ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex :=
  ClassFieldTheory.Local.ArithmeticNormalizationProof.ramificationIndex_eq_of_algEquiv
    (extensionIntermediatePadicEquiv F E g).symm

/-- The norm from the image of `E` to the bottom field corresponds to the norm of `E / F`
under the field isomorphisms `E ≃ L` and `⊥ ≃ F`. -/
theorem botEquiv_norm_eq (y : (extensionFiniteIntermediate F E g).field) :
    IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
        (@Algebra.norm (baseExtension F).field (extensionFiniteIntermediate F E g).field _ _
          (IntermediateField.inclusion (baseExtension_le F _)).toAlgebra y) =
      @Algebra.norm F.Carrier E.Carrier _ _ (Weil.Local.extensionAlgebra F E g)
        ((extensionIntermediatePadicEquiv F E g).symm y) := by
  let := Weil.Local.extensionAlgebra F E g
  let : Algebra (baseExtension F).field (extensionFiniteIntermediate F E g).field :=
    (IntermediateField.inclusion (baseExtension_le F _)).toAlgebra
  let e₁ : F.Carrier ≃+* (baseExtension F).field :=
    (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.toRingEquiv
  let e₂ : E.Carrier ≃+* (extensionFiniteIntermediate F E g).field :=
    (extensionIntermediatePadicEquiv F E g).toRingEquiv
  have he : (algebraMap (baseExtension F).field
      (extensionFiniteIntermediate F E g).field).comp (e₁ : F.Carrier →+* _) =
      (e₂ : E.Carrier →+* _).comp (algebraMap F.Carrier E.Carrier) := by
    ext a
    change (algebraMap F.Carrier (AlgebraicClosure F.Carrier) a) =
      extensionIntermediatePadicEquiv F E g (algebraMap F.Carrier E.Carrier a)
    rw [extensionIntermediatePadicEquiv_coe]
    exact (Weil.Local.extensionFieldEmbedding_comp F E g a).symm
  have h := Algebra.norm_eq_of_equiv_equiv e₁ e₂ he (e₂.symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- On units: the bottom-field norm of the image corresponds to the standalone norm. -/
theorem baseFieldUnitsEquiv_unitsNorm (y : (extensionFiniteIntermediate F E g).fieldˣ) :
    baseFieldUnitsEquiv F
        ((baseExtension F).unitsNorm (extensionFiniteIntermediate F E g)
          (baseExtension_le F _) y) =
      Units.map (@Algebra.norm F.Carrier E.Carrier _ _ (Weil.Local.extensionAlgebra F E g))
        ((PadicField.ConductorTransport.unitsEquiv E
          ((extensionFiniteIntermediate F E g).asPadicField (p := p))
          (extensionIntermediatePadicEquiv F E g)).symm y) := by
  apply Units.ext
  exact botEquiv_norm_eq F E g y

local instance bridgeImageMeasurable : MeasurableSpace E.Carrier := borel E.Carrier

/-- The generator value of a standalone generator is the ratio of Tate's epsilon factors on
the standalone extension, for the trace character `ψF ∘ Tr_{E/F}` and any Haar measure. -/
theorem generatorValue_standaloneGenerator (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (η η' : QuasiCharacter E)
    (ψF : NontrivialAdditiveCharacter F) (ψ : AdditiveCharacter F (baseExtension F))
    (hψ : IsBaseCharacter F ψF ψ) (measures : HaarFamily F) (μE : LocalAdditiveHaarMeasure E) :
    (generatorValue F (baseExtension F) ψ measures (standaloneGenerator F e E g η η') : ℂ) =
      PadicAbelian.epsilon E.canonicalTopologicalData η
          (SystemEpsilon.standaloneTraceCharacter F E g ψF) μE.measure 0 /
        PadicAbelian.epsilon E.canonicalTopologicalData η'
          (SystemEpsilon.standaloneTraceCharacter F E g ψF) μE.measure 0 := by
  let L := extensionFiniteIntermediate F E g
  have hval : generatorValue F (baseExtension F) ψ measures (standaloneGenerator F e E g η η') =
      (fieldData F L).abelianEpsilonRatio (standaloneGenerator F e E g η η').first
        (standaloneGenerator F e E g η η').second
        (traceCharacter F (baseExtension F) L (baseExtension_le F _) ψ)
        (CommonClosureSystemTransport.imageHaarMeasure F E g μE) :=
    (fieldData F L).abelianEpsilonRatio_haarIndependent _ _ _ _ _
  have hfac (χ : QuasiCharacter E) :
      (fieldData F L).abelianEpsilonExpression
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e L
            (SystemEpsilon.imageCharacter F E g
              (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) χ)))
          (traceCharacter F (baseExtension F) L (baseExtension_le F _) ψ)
          (CommonClosureSystemTransport.imageHaarMeasure F E g μE) =
        PadicAbelian.epsilon E.canonicalTopologicalData χ
          (SystemEpsilon.standaloneTraceCharacter F E g ψF) μE.measure 0 := by
    have h1 : CommonClosureSpectral.character F L 0 *
        SystemEpsilon.imageCharacter F E g
          (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) χ) =
        SystemEpsilon.imageCharacter F E g
          (RankOne.weilCharacter E (extensionReciprocityCandidate F E g e) χ) := by
      apply ContinuousMonoidHom.ext
      intro w
      rw [ContinuousMonoidHom.mul_apply]
      have hw : CommonClosureSpectral.character F L 0 w = 1 := by
        apply Units.ext
        rw [CommonClosureSpectral.character_apply]
        simp
      rw [hw, one_mul]
    rw [SystemEpsilon.traceCharacter_eq_imageAdditiveCharacter F E g ψF ψ hψ,
      ← SystemEpsilon.imageFactor_eq_epsilon F E g e he χ _ μE 0, h1]
  rw [hval]
  simp only [PadicField.TopologicalData.abelianEpsilonRatio, Units.val_div_eq_div_val]
  exact congrArg₂ (· / ·) (hfac η) (hfac η')

end Image

/-- A generator in the support of a combination of single generators is one of them. -/
theorem exists_eq_of_mem_support_sum_single {J : Type*} [Fintype J] {X : Type*}
    (G : J → X) (n : J → ℤ) {a : X}
    (ha : a ∈ (∑ j, n j • Finsupp.single (G j) (1 : ℤ)).support) : ∃ j, a = G j := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum ha)
  exact ⟨j, Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul hj))⟩

section Base

local instance bridgeBaseAlgebra : Algebra (Padic p) (baseExtension F).field :=
  ((baseExtension F).asPadicField (p := p)).algebra

/-- The bottom-field transport of a base quasicharacter is its conductor transport. -/
theorem baseFieldCharacterEquiv_eq_quasicharacter (α : QuasiCharacter F) :
    baseFieldCharacterEquiv F α =
      PadicField.ConductorTransport.quasicharacter F ((baseExtension F).asPadicField (p := p))
        (baseFieldPadicEquiv F).symm α := by
  rfl

/-- The bottom-field transport preserves the conductor. -/
theorem multiplicativeConductor_baseFieldCharacterEquiv (α : QuasiCharacter F) :
    (fieldData F (baseExtension F)).multiplicativeConductor (baseFieldCharacterEquiv F α) =
      F.canonicalTopologicalData.multiplicativeConductor α := by
  rw [baseFieldCharacterEquiv_eq_quasicharacter]
  exact PadicField.ConductorTransport.multiplicativeConductor_eq _ _ _ α

end Base

/-- A transported twist by a norm pullback is the transported twist times the
common-closure norm pullback of the bottom-field transport. -/
theorem quasicharacter_eq_mul_normPullback (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (α : QuasiCharacter F) (η η₀ : QuasiCharacter E)
    (hη : ∀ x, η x = η₀ x *
      α (Units.map (@Algebra.norm F.Carrier E.Carrier _ _ (Weil.Local.extensionAlgebra F E g)) x)) :
    transportedCharacter F E g η =
      transportedCharacter F E g η₀ *
        normPullback F e (baseExtension F) (extensionFiniteIntermediate F E g)
          (baseExtension_le F _) (baseFieldCharacterEquiv F α) := by
  let := E.canonicalTopologicalData.topology
  let := (fieldData F (extensionFiniteIntermediate F E g)).topology
  apply ContinuousMonoidHom.ext
  intro y
  rw [ContinuousMonoidHom.mul_apply, normPullback_apply F e he, baseFieldCharacterEquiv_apply,
    baseFieldUnitsEquiv_unitsNorm]
  exact hη _

/-- **Standalone unramified relations.** Let the standalone extensions `E_j / F` be
unramified, and let the quasicharacters be `η_j = η₀_j · (α ∘ N)` and `η'_j = η₀'_j · (α ∘ N)`
with `η₀_j`, `η₀'_j` unramified and one base quasicharacter `α`. If
`Σ_j n_j Ind_{E_j/F}([η_j ∘ rec] - [η'_j ∘ rec]) = 0`, then the abelian epsilon evaluation of the
corresponding presentation over the bottom field is trivial. -/
theorem evaluationMap_standalone_eq_zero_of_unramified (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier) (η η' : ∀ j, QuasiCharacter (E j))
    (n : J → ℤ)
    (h : ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (ExactGrothendieckGroup.characterClass.{u, w}
            (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e) (η j)) -
          ExactGrothendieckGroup.characterClass.{u, w}
            (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
              (η' j))) = 0)
    (α : QuasiCharacter F)
    (hgen : ∀ j, (E j).canonicalTopologicalData.ramificationIndex =
        F.canonicalTopologicalData.ramificationIndex ∧
      ∃ η₀ η₀' : QuasiCharacter (E j),
        (E j).canonicalTopologicalData.IsUnramifiedQuasicharacter η₀ ∧
        (E j).canonicalTopologicalData.IsUnramifiedQuasicharacter η₀' ∧
        (∀ x, η j x = η₀ x * α (Units.map
          (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
            x)) ∧
        (∀ x, η' j x = η₀' x * α (Units.map
          (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
            x)))
    (ψ : AdditiveCharacter F (baseExtension F)) (measures : HaarFamily F) :
    evaluationMap F (baseExtension F) ψ measures
      (∑ j, n j • Finsupp.single (standaloneGenerator F e (E j) (g j) (η j) (η' j)) 1) = 0 := by
  have hz := presentationMap_imageGenerator_eq_zero.{u, w, 0} F e E g _ _ n h
  refine evaluationMap_eq_zero_of_unramified_normPullback.{u, 0} F e he _ ψ measures _ hz
    (baseFieldCharacterEquiv F α) ?_
  intro x hx
  obtain ⟨j, rfl⟩ := exists_eq_of_mem_support_sum_single _ n hx
  obtain ⟨hram, η₀, η₀', h₀, h₀', h₁, h₂⟩ := hgen j
  let L := extensionFiniteIntermediate F (E j) (g j)
  refine ⟨?_, transportedCharacter F (E j) (g j) η₀, transportedCharacter F (E j) (g j) η₀',
    ?_, ?_, ?_, ?_⟩
  · change (fieldData F L).ramificationIndex = (fieldData F (baseExtension F)).ramificationIndex
    rw [ramificationIndex_extensionFiniteIntermediate, ramificationIndex_baseExtension, hram]
  · exact (PadicField.ConductorTransport.isUnramifiedQuasicharacter_iff _ _ _ η₀).mpr h₀
  · exact (PadicField.ConductorTransport.isUnramifiedQuasicharacter_iff _ _ _ η₀').mpr h₀'
  · exact (standaloneGenerator_first F e (E j) (g j) (η j) (η' j)).trans
      (quasicharacter_eq_mul_normPullback F e he (E j) (g j) α (η j) η₀ h₁)
  · exact (standaloneGenerator_second F e (E j) (g j) (η j) (η' j)).trans
      (quasicharacter_eq_mul_normPullback F e he (E j) (g j) α (η' j) η₀' h₂)

/-- **Standalone relations among small twists of a highly ramified norm pullback.** For
finitely many standalone extensions `E_j / F` and a conductor bound `K` there is `B` with the
following property. Let `a(α) ≥ B`, and let the quasicharacters be `η_j = η₀_j · (α ∘ N)` and
`η'_j = η₀'_j · (α ∘ N)` with `a(η₀_j), a(η₀'_j) ≤ K`. If
`Σ_j n_j Ind_{E_j/F}([η_j ∘ rec] - [η'_j ∘ rec]) = 0`, then the abelian epsilon evaluation of the
corresponding presentation over the bottom field is trivial. -/
theorem exists_bound_evaluationMap_standalone_eq_zero_of_ramified (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (ψ : AdditiveCharacter F (baseExtension F)) (measures : HaarFamily F) (K : ℕ) :
    ∃ B : ℕ, ∀ α : QuasiCharacter F, B ≤ F.canonicalTopologicalData.multiplicativeConductor α →
      ∀ (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ),
        ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong
            (extensionWeilMap F (E j) (g j)) (extensionWeilMap_isOpenEmbedding F (E j) (g j))
            (ExactGrothendieckGroup.characterClass.{u, w}
                (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
                  (η j)) -
              ExactGrothendieckGroup.characterClass.{u, w}
                (RankOne.weilCharacter (E j) (extensionReciprocityCandidate F (E j) (g j) e)
                  (η' j))) = 0 →
        (∀ j, ∃ η₀ η₀' : QuasiCharacter (E j),
          (E j).canonicalTopologicalData.multiplicativeConductor η₀ ≤ K ∧
          (E j).canonicalTopologicalData.multiplicativeConductor η₀' ≤ K ∧
          (∀ x, η j x = η₀ x * α (Units.map
            (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
              x)) ∧
          (∀ x, η' j x = η₀' x * α (Units.map
            (@Algebra.norm F.Carrier (E j).Carrier _ _ (Weil.Local.extensionAlgebra F (E j) (g j)))
              x))) →
        evaluationMap F (baseExtension F) ψ measures
          (∑ j, n j • Finsupp.single (standaloneGenerator F e (E j) (g j) (η j) (η' j)) 1) =
            0 := by
  classical
  obtain ⟨B, hB⟩ := exists_bound_evaluationMap_eq_zero_of_ramified_normPullback.{u, 0} F e he
    (baseExtension F) ψ measures
    (Finset.univ.image fun j => extensionFiniteIntermediate F (E j) (g j)) K
  refine ⟨B, fun α hα η η' n h hgen => ?_⟩
  have hz := presentationMap_imageGenerator_eq_zero.{u, w, 0} F e E g _ _ n h
  refine hB (baseFieldCharacterEquiv F α)
    ((multiplicativeConductor_baseFieldCharacterEquiv F α).symm ▸ hα) _ hz ?_
  intro x hx
  obtain ⟨j, rfl⟩ := exists_eq_of_mem_support_sum_single _ n hx
  obtain ⟨η₀, η₀', h₀, h₀', h₁, h₂⟩ := hgen j
  refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), transportedCharacter F (E j) (g j) η₀,
    transportedCharacter F (E j) (g j) η₀', ?_, ?_, ?_, ?_⟩
  · exact (PadicField.ConductorTransport.multiplicativeConductor_eq _ _ _ η₀).trans_le h₀
  · exact (PadicField.ConductorTransport.multiplicativeConductor_eq _ _ _ η₀').trans_le h₀'
  · exact (standaloneGenerator_first F e (E j) (g j) (η j) (η' j)).trans
      (quasicharacter_eq_mul_normPullback F e he (E j) (g j) α (η j) η₀ h₁)
  · exact (standaloneGenerator_second F e (E j) (g j) (η j) (η' j)).trans
      (quasicharacter_eq_mul_normPullback F e he (E j) (g j) α (η' j) η₀' h₂)

end Standalone

end Langlands.LocalFactor.NonabelianBrauer
