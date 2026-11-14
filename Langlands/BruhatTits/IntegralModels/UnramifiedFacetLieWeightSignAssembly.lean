import Langlands.BruhatTits.IntegralModels.UnramifiedFacetLieWeightSignStatement
import Langlands.BruhatTits.IntegralModels.IncidentFacetRootImages
import Langlands.BruhatTits.IntegralModels.IncidentNegativeRootReduction
import Langlands.BruhatTits.IntegralModels.IncidentFacetKernelSmoothness
import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionProof
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRootSupport
import Langlands.BruhatTits.IntegralModels.IntegralTorusRootSupport
import Langlands.BruhatTits.IntegralModels.RootSpecializationConstruction
import Langlands.GroupScheme.Lie.SchematicImage
import Langlands.GroupScheme.Lie.TargetCoefficients
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.Geometry.Building.IntegerValuationChamberBounded

/-! # Assembly of the unramified Lie-weight sign formula from rootwise images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme.Lie

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  (q : G ⟶ H) (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)

include hT in
/-- Over a residue field, for a split torus, the `χ`-weight part of the
differential range of a homomorphism is the image of the source `χ`-weight
space. -/
theorem residue_weightSpace_inf_range_eq_map_weightSpace (χ : characterLattice T) :
    weightSpace (i ≫ q) χ ⊓
        LinearMap.range (targetMapLinear q (IsLocalRing.ResidueField R)) =
      (weightSpace i χ).map (targetMapLinear q (IsLocalRing.ResidueField R)) := by
  apply le_antisymm
  · rintro X ⟨hX, hXr⟩
    obtain ⟨Y, hY, hYX⟩ := exists_weightSpace_preimage q i hT hX hXr
    exact ⟨Y, hY, hYX⟩
  · rintro X ⟨Y, hY, rfl⟩
    exact ⟨lieKernelHomLinear_mem_weightSpace q i χ hY, Y, rfl⟩

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A weight space lies in the span of the weight spaces of its positive
integer multiples. -/
theorem weightSpace_le_semigroupWeightSpan_cyclicTail (i : S.toGrp ⟶ G)
    (χ : characterLattice S) :
    weightSpace i χ ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail χ 1) :=
  (actionWeightSpace_conjugation i χ).ge.trans
    (le_iSup (fun ψ : cyclicTail χ 1 => actionWeightSpace (AutomorphicAction.conjugation i) ψ.val)
      ⟨χ, 1, le_rfl, one_pos, one_nsmul χ⟩)

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.BruhatTits.IntegralModels

section SchematicImageWeights

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    {H G : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType G.X.hom] (f : H ⟶ G)

private instance signAssembly_image_affine : IsAffineHom (SchematicImage.image f).X.hom :=
  SchematicImage.instSchematicImage10 f

private instance signAssembly_image_lieCommGroup :
    CommGroup (lieKernel (SchematicImage.image f) (IsLocalRing.ResidueField R)) :=
  lieKernelCommGroup _

private instance signAssembly_image_lieModule :
    @Module (IsLocalRing.ResidueField R)
      (Additive (lieKernel (SchematicImage.image f) (IsLocalRing.ResidueField R))) _
      (@Additive.addCommMonoid _ (signAssembly_image_lieCommGroup f).toCommMonoid) :=
  lieKernelModule _

/-- Over a residue field, if the full kernel of `f` is smooth, the nonzero
weights of a torus on the Lie algebra of the actual schematic image of `f` are
the nonzero weights whose weight space meets the differential range of `f`. -/
theorem nonzeroLieImageWeights_schematicImage_of_smooth_kernel
    (hker : Smooth (kernel f).X.hom) (j : S.toGrp ⟶ G) :
    nonzeroLieImageWeights j (SchematicImage.inclusion f) =
      {χ | χ ≠ 0 ∧ weightSpace j χ ⊓
        LinearMap.range (Lie.targetMapLinear f (IsLocalRing.ResidueField R)) ≠ ⊥} := by
  have h := Lie.range_schematicImage_inclusion_of_smooth_kernel f hker
    (IsLocalRing.ResidueField R)
  ext χ
  change (χ ≠ 0 ∧ _ ≠ ⊥) ↔ (χ ≠ 0 ∧ _ ≠ ⊥)
  exact and_congr_right fun _ =>
    not_congr (iff_of_eq (congrArg (fun W => weightSpace j χ ⊓ W = ⊥) h))

end SchematicImageWeights

end Langlands.BruhatTits.IntegralModels

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    {source target :
      RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (φ : RelativeComponentModelHom source target)
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (T : IntegralTorusData source C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)

private instance signAssembly_sourceNeutral_smooth : Smooth source.neutral.group.X.hom :=
  source.neutral_smooth

private instance signAssembly_targetNeutral_smooth : Smooth target.neutral.group.X.hom :=
  target.neutral_smooth

attribute [local instance] neutralSpecialFibre_affine neutralSpecialFibre_isAffine
  quotient_isAffine

private instance signAssembly_sourceSpecialFibre_smooth :
    Smooth source.neutral.specialFibre.X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd source.neutral.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance signAssembly_sourceSpecialFibre_connected :
    ConnectedSpace source.neutral.specialFibre.X.left :=
  source.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres
    source.neutral_connectedFibres

private instance signAssembly_neutralSpecialFibre_finiteType
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G) :
    LocallyOfFiniteType D.neutral.specialFibre.X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

private instance signAssembly_rootSpecialFibre_affine (a : characterLattice C.S) (ha : a ≠ 0) :
    IsAffineHom ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    ((T.toIntegralSplitTorusData hT).rootModel a ha).group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

/-- The roots of the source special-fibre torus of `T` in the quotient `Q` whose
generic character is nonnegative on the real cocharacter vector `v`: the right
side of the Lie-weight sign formula (Kaletha–Prasad Theorem 8.4.19(2)). -/
def nonnegativeQuotientRoots (v : RealTorusSpace.V C.S) :
    Set (characterLattice T.specialFibre) :=
  {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
    0 ≤ RealTorusSpace.eval C.S ((T.characterSpecialization hT).symm χ) v}

theorem mem_nonnegativeQuotientRoots (v : RealTorusSpace.V C.S)
    (χ : characterLattice T.specialFibre) :
    χ ∈ φ.nonnegativeQuotientRoots C T hT Q v ↔
      χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ RealTorusSpace.eval C.S ((T.characterSpecialization hT).symm χ) v :=
  Iff.rfl

/-- The quotient torus inclusion is the source special-fibre torus inclusion
followed by the original composite into the reductive quotient. -/
theorem quotientTorusInclusion_eq_comp :
    φ.quotientTorusInclusion Q T =
      T.specialFibreInclusion ≫ (φ.neutralSpecialFibreMap ≫ Q.projection) :=
  Category.assoc _ _ _

/-- A character whose specialization is a root of the source special fibre
is an actual generic root of `C.S` in `G`. -/
theorem mem_relativeRoots_of_characterSpecialization_mem_source
    {a : characterLattice C.S}
    (ha : T.characterSpecialization hT a ∈ relativeRoots T.specialFibreInclusion) :
    a ∈ relativeRoots C.i :=
  (T.mem_relativeRoots_characterSpecialization_iff hT a).mp ha

include hQ in
/-- A character whose specialization is a root of the target reductive
quotient is an actual generic root of `C.S` in `G`. -/
theorem mem_relativeRoots_of_characterSpecialization_mem_quotient
    {a : characterLattice C.S}
    (ha : T.characterSpecialization hT a ∈ relativeRoots (φ.quotientTorusInclusion Q T)) :
    a ∈ relativeRoots C.i := by
  have h₁ : φ.quotientTorusInclusion Q T =
      (φ.mapIntegralTorus T).specialFibreInclusion ≫ Q.projection := by
    rw [φ.mapIntegralTorus_specialFibreInclusion T]
    rfl
  rw [h₁] at ha
  have h₂ := Q.relativeRoots_subset_specialFibre hQ (φ.mapIntegralTorus T) hT ha
  exact ((φ.mapIntegralTorus T).mem_relativeRoots_characterSpecialization_iff hT a).mp h₂

/-- The source weight space of a specialized nonzero character lies in the
differential range of the corresponding source root-model special fibre. -/
theorem weightSpace_le_range_rootModelMap (a : characterLattice C.S) (ha : a ≠ 0) :
    weightSpace T.specialFibreInclusion (T.characterSpecialization hT a) ≤
      LinearMap.range (Lie.targetMapLinear
        ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) := by
  have h : LinearMap.range (Lie.targetMapLinear
        ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
      RelativeRoot.semigroupWeightSpan
        (AutomorphicAction.conjugation T.specialFibreInclusion)
        (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) :=
    (T.toIntegralSplitTorusData hT).rootModelMap_specialFibre_lie_range a ha
  exact (RelativeRoot.weightSpace_le_semigroupWeightSpan_cyclicTail
    T.specialFibreInclusion (T.characterSpecialization hT a)).trans h.ge

include hQ hT in
/-- The `χ`-weight part of the differential range of the composite into the
reductive quotient is the image of the source `χ`-weight space. -/
theorem weightSpace_quotientTorusInclusion_inf_range (χ : characterLattice T.specialFibre) :
    weightSpace (φ.quotientTorusInclusion Q T) χ ⊓
        LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
      (weightSpace T.specialFibreInclusion χ).map
        (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact (congrArg (fun j : T.specialFibre.toGrp ⟶ Q.quotient => weightSpace j χ ⊓
      LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F))))
    (quotientTorusInclusion_eq_comp φ C T Q)).trans
    (Lie.residue_weightSpace_inf_range_eq_map_weightSpace
      (φ.neutralSpecialFibreMap ≫ Q.projection) T.specialFibreInclusion
      (T.specialFibre_isSplitTorus hT) χ)

/-- The differential range of the source-root composite into the reductive
quotient is the image of the source root-model differential range. -/
theorem range_rootTargetReductiveQuotientMap (a : characterLattice C.S) (ha : a ≠ 0) :
    LinearMap.range (Lie.targetMapLinear (φ.rootTargetReductiveQuotientMap T hT Q a ha)
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
      (LinearMap.range (Lie.targetMapLinear
        ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
          (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
        (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) :=
  (congrArg LinearMap.range (Lie.targetMapLinear_comp
    ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap
    (φ.neutralSpecialFibreMap ≫ Q.projection)
    (IsLocalRing.ResidueField (fixedFieldIntegers F)))).trans (LinearMap.range_comp _ _)

section Assembly

variable (Ωf Ωf' Ω Ω' : Set C.Apartment)
    (hface : AffineRootSystem.IsFaceOf C.affineRoots Ωf Ωf')
    (hsub : Ω ⊆ Ωf) (hsub' : Ω' ⊆ Ωf')
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hP : UnramifiedRootPositiveReductionStatement.{u})

include hQ hface hsub hsource htarget hP in
/-- For a root strictly negative on `v`, the source weight space maps to zero
in the Lie algebra of the reductive quotient. -/
theorem map_weightSpace_eq_bot_of_eval_neg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : RealTorusSpace.eval C.S a v < 0) :
    (weightSpace T.specialFibreInclusion (T.characterSpecialization hT a)).map
        (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) = ⊥ := by
  have hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω) :=
    fun f => (C.isBoundedApartmentSubset_of_isFacet
      (MaximalUnramified.exists_order_ne_zero F) hface.1 f).mono (Set.image_mono hsub)
  have h₁ := φ.rootTargetReductiveQuotientMap_lie_range_of_eval_neg C E T hT Q hQ Ω Ω'
    hsource htarget hb hP x hx v hv a ha
  have h₂ := range_rootTargetReductiveQuotientMap φ C T hT Q a a.2.1
  exact eq_bot_iff.mpr ((Submodule.map_mono
    (weightSpace_le_range_rootModelMap C T hT a a.2.1)).trans (h₂.symm.trans h₁).le)

include hQ hface hsub hsub' hsource htarget in
/-- For a root nonnegative on `v`, the whole quotient weight space lies in the
differential range of the composite into the reductive quotient. -/
theorem weightSpace_le_range_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (a : relativeRoots C.i) (ha : 0 ≤ RealTorusSpace.eval C.S a v) :
    weightSpace (φ.quotientTorusInclusion Q T) (T.characterSpecialization hT a) ≤
      LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) := by
  have h := φ.rootTargetReductiveQuotientMap_lie_range_of_incidentFacets_of_nonneg C E T hT
    Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget Q hQ x hx v hv a ha
  have h₂ := range_rootTargetReductiveQuotientMap φ C T hT Q a a.2.1
  exact (RelativeRoot.weightSpace_le_semigroupWeightSpan_cyclicTail
    (φ.quotientTorusInclusion Q T) (T.characterSpecialization hT a)).trans
      (h.ge.trans (h₂.le.trans LinearMap.map_le_range))

include hQ hface hsub hsource htarget hP in
/-- Forward direction of the sign formula for one character: a nonzero weight
meeting the differential range is a quotient root whose generic character is
nonnegative on `v`. -/
theorem mem_relativeRoots_and_nonneg_of_inf_range_ne_bot
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (χ : characterLattice T.specialFibre) (h0 : χ ≠ 0)
    (hmap : weightSpace (φ.quotientTorusInclusion Q T) χ ⊓
        LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) ≠ ⊥) :
    χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
      0 ≤ RealTorusSpace.eval C.S ((T.characterSpecialization hT).symm χ) v := by
  have hχ : T.characterSpecialization hT ((T.characterSpecialization hT).symm χ) = χ :=
    AddEquiv.apply_symm_apply _ χ
  have hW := weightSpace_quotientTorusInclusion_inf_range φ C T hT Q hQ χ
  have hmap' : (weightSpace T.specialFibreInclusion χ).map
      (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) ≠ ⊥ :=
    fun h => hmap (hW.trans h)
  have hWt : weightSpace T.specialFibreInclusion χ ≠ ⊥ :=
    fun h => hmap' ((congrArg (Submodule.map (Lie.targetMapLinear
      (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))) h).trans (Submodule.map_bot _))
  have ha : (T.characterSpecialization hT).symm χ ∈ relativeRoots C.i :=
    mem_relativeRoots_of_characterSpecialization_mem_source C T hT
      ((congrArg (· ∈ relativeRoots T.specialFibreInclusion) hχ).mpr ⟨h0, hWt⟩)
  refine ⟨⟨h0, fun h => hmap ?_⟩, ?_⟩
  · exact (congrArg (· ⊓ LinearMap.range (Lie.targetMapLinear
      (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))) h).trans (bot_inf_eq _)
  · by_contra hneg
    exact hmap' ((congrArg (fun ψ => (weightSpace T.specialFibreInclusion ψ).map
      (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))) hχ).symm.trans
      (map_weightSpace_eq_bot_of_eval_neg φ C E T hT Q hQ Ωf Ωf' Ω Ω' hface hsub
        hsource htarget hP x hx v hv ⟨_, ha⟩ (not_le.mp hneg)))

include hQ hface hsub hsub' hsource htarget in
/-- Backward direction of the sign formula for one character: a quotient root
whose generic character is nonnegative on `v` has its whole weight space
inside the differential range. -/
theorem inf_range_ne_bot_of_mem_relativeRoots_of_nonneg
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω')
    (χ : characterLattice T.specialFibre)
    (hroot : χ ∈ relativeRoots (φ.quotientTorusInclusion Q T))
    (hnn : 0 ≤ RealTorusSpace.eval C.S ((T.characterSpecialization hT).symm χ) v) :
    weightSpace (φ.quotientTorusInclusion Q T) χ ⊓
        LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
          (IsLocalRing.ResidueField (fixedFieldIntegers F))) ≠ ⊥ := by
  have hχ : T.characterSpecialization hT ((T.characterSpecialization hT).symm χ) = χ :=
    AddEquiv.apply_symm_apply _ χ
  have ha : (T.characterSpecialization hT).symm χ ∈ relativeRoots C.i :=
    mem_relativeRoots_of_characterSpecialization_mem_quotient φ C T hT Q hQ
      ((congrArg (· ∈ relativeRoots (φ.quotientTorusInclusion Q T)) hχ).mpr hroot)
  have hle := weightSpace_le_range_of_nonneg φ C E T hT Q hQ Ωf Ωf' Ω Ω' hface
    hsub hsub' hsource htarget x hx v hv ⟨_, ha⟩ hnn
  have hle' : weightSpace (φ.quotientTorusInclusion Q T) χ ≤
      LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F))) :=
    (congrArg (fun ψ => weightSpace (φ.quotientTorusInclusion Q T) ψ ≤
      LinearMap.range (Lie.targetMapLinear (φ.neutralSpecialFibreMap ≫ Q.projection)
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))) hχ).mp hle
  exact fun h => hroot.2 ((inf_eq_left.mpr hle').symm.trans h)

include hQ hface hsub hsub' hsource htarget hP in
/-- **The Lie-weight sign formula for one model morphism, from a smooth full
kernel.** If the original composite from the source neutral special fibre to
the target reductive quotient has smooth full kernel, then the nonzero weights
of the source torus on the Lie algebra of its actual schematic image are
exactly the quotient roots whose generic character is nonnegative on `v`. -/
theorem nonzeroLieImageWeights_eq_of_smooth_kernel
    (hK : Smooth (kernel (φ.neutralSpecialFibreMap ≫ Q.projection)).X.hom)
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω') :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ RealTorusSpace.eval C.S ((T.characterSpecialization hT).symm χ) v} := by
  have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact (nonzeroLieImageWeights_schematicImage_of_smooth_kernel
    (φ.neutralSpecialFibreMap ≫ Q.projection) hK (φ.quotientTorusInclusion Q T)).trans
    (Set.ext fun χ =>
      ⟨fun h => mem_relativeRoots_and_nonneg_of_inf_range_ne_bot φ C E T hT Q hQ
          Ωf Ωf' Ω Ω' hface hsub hsource htarget hP x hx v hv χ h.1 h.2,
        fun h => ⟨h.1.1, inf_range_ne_bot_of_mem_relativeRoots_of_nonneg φ C E T hT Q hQ
          Ωf Ωf' Ω Ω' hface hsub hsub' hsource htarget x hx v hv χ h.1 h.2⟩⟩)

include hQ hface hsub hsub' hsource htarget in
/-- The Lie-weight sign formula at incident facet subsets, phrased with
`nonnegativeQuotientRoots`. The smoothness of the full kernel comes from
`reductiveComposite_smooth_kernel_of_incidentFacets`, and positive reduction
from `unramifiedRootPositiveReduction`. -/
theorem nonzeroLieImageWeights_eq_nonnegativeQuotientRoots
    (x : C.Apartment) (hx : x ∈ Ω) (v : RealTorusSpace.V C.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω') :
    nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      φ.nonnegativeQuotientRoots C T hT Q v :=
  φ.nonzeroLieImageWeights_eq_of_smooth_kernel C E T hT Q hQ Ωf Ωf' Ω Ω' hface hsub hsub'
    hsource htarget unramifiedRootPositiveReduction
    (φ.reductiveComposite_smooth_kernel_of_incidentFacets C E T hT Q hQ Ω Ω' hsource htarget
      unramifiedRootPositiveReduction Ωf Ωf' hface hsub hsub' x hx v hv) x hx v hv

end Assembly

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

namespace Langlands.BruhatTits.IntegralModels

/-- **The Lie-weight sign formula over the maximal unramified extension**
(Kaletha–Prasad Theorem 8.4.19(2), for the apartment of `C`). -/
theorem unramifiedFacetLieWeightSign : UnramifiedFacetLieWeightSignStatement.{u} := by
  intro F _ _ _ _ G _ C E Ωf Ωf' Ω Ω' hface hsub hsub' D D' _ _ htarget hsource φ Q A hA hQ
    x hx v hv
  exact φ.nonzeroLieImageWeights_eq_nonnegativeQuotientRoots C E A hA Q hQ Ωf Ωf' Ω Ω'
    hface hsub hsub' hsource htarget x hx v hv

end Langlands.BruhatTits.IntegralModels
