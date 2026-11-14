import Langlands.BruhatTits.IntegralModels.UnramifiedPrescribedQuotientImage
import Langlands.GroupScheme.Dynamic.ParabolicQuotient
import Langlands.GroupScheme.SubgroupFunctor.FppfProductImage

/-! # Exact quotient images along prescribed incident cocharacter rays -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

private theorem parabolic_le_quotientImage
    {k : Type u} [Field k]
    {H N R : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [IsAffineHom R.X.hom]
    [Smooth N.X.hom] [Smooth R.X.hom]
    [ConnectedSpace N.X.left] [ConnectedSpace R.X.left]
    (f : H ⟶ N) (q : N ⟶ R)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ N)
    (hqs : Smooth q.hom.hom.left) (hqsurj : Surjective q.hom.hom.left)
    (hP : Dynamic.parabolic χ ≤
      SubgroupFunctor.range (SchematicImage.inclusion f)) :
    Dynamic.parabolic (χ ≫ q) ≤
      SubgroupFunctor.range (SchematicImage.inclusion (f ≫ q)) := by
  let : Mono (SchematicImage.inclusion (f ≫ q)).hom.hom :=
    Over.mono_of_mono_left _
  have himage : SubgroupFunctor.range (SchematicImage.inclusion f ≫ q) ≤
      SubgroupFunctor.range (SchematicImage.inclusion (f ≫ q)) := by
    apply (SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant
      (SchematicImage.projection f) (SchematicImage.inclusion f ≫ q)
      (SchematicImage.inclusion (f ≫ q))
      (inferInstanceAs (IsClosedImmersion
        (SchematicImage.inclusion (f ≫ q)).hom.hom.left))).mp
    rw [← Category.assoc, SchematicImage.projection_inclusion]
    exact SubgroupFunctor.range_le_of_factor (SchematicImage.projection (f ≫ q))
      (SchematicImage.projection_inclusion (f ≫ q))
  apply (Dynamic.parabolic_isFppfImage χ q hqs hqsurj).le_of_map_le
    (SubgroupFunctor.isFppfLocal_range (SchematicImage.inclusion (f ≫ q)))
  rintro T z ⟨y, hy, rfl⟩
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp (hP T hy)
  apply himage T
  exact SubgroupFunctor.mem_range.mpr ⟨t, by
    change t ≫ (SchematicImage.inclusion f ≫ q).hom.hom = y ≫ q.hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc, ht]⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (x : C.Apartment)
    (hN : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))

private instance prescribedAttainment_neutralSmooth :
    Smooth D.neutral.group.X.hom := D.neutral_smooth

private instance prescribedAttainment_neutralSpecialConnected :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

private instance prescribedAttainment_specialAffine
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) :
    IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

private instance prescribedAttainment_specialSmooth
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] : Smooth N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth N.group.X.hom))

variable (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

omit [IsAffineHom G.X.hom] in
include hQ in
private theorem quotientProjection_smooth : Smooth Q.projection.hom.hom.left := by
  let : IsClosedImmersion Q.radicalInclusion.hom.hom.left := hQ.1.isClosedSubgroup
  have hqc : QuasiCompact (Q.projection.hom.hom.left ≫ Q.quotient.X.hom) := by
    rw [Over.w Q.projection.hom.hom]
    infer_instance
  let : QuasiCompact (Q.projection.hom.hom.left ≫ Q.quotient.X.hom) := hqc
  let : QuasiCompact Q.projection.hom.hom.left :=
    QuasiCompact.of_comp Q.projection.hom.hom.left Q.quotient.X.hom
  exact hQ.2.1.smooth_of_smooth_kernel
    (show (SubgroupFunctor.range Q.radicalInclusion).IsRepresentedBy
      Q.radicalInclusion from ⟨Over.mono_of_mono_left _, rfl⟩) hQ.1.smooth

include hQ in
/-- A prescribed residue cocharacter selects one positive incident ray on
which every supplied smooth connected zero-fixer comparison has exactly the
prescribed dynamic parabolic as its schematic reductive-quotient image. -/
theorem exists_pos_incidentFacet_quotientImage_eq_parabolic
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (ν : cocharacterLattice
      (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreTorus) :
    let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
    let w := C.cocharacterDirection (A.cocharacterSpecialization.symm ν)
    ∃ ε : ℝ, 0 < ε ∧
      AffineRootSystem.IsFaceOf C.affineRoots
        (AffineRootSystem.facet C.affineRoots x)
        (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
      ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
        [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
        M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer
          (C.apartmentMap '' {ε • w +ᵥ x}) →
        ∀ φ : M.Hom D.neutral (𝟙 G),
          SubgroupFunctor.range
              (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) =
            Dynamic.parabolic
              ((CommGroupScheme.groupHom ν ≫ A.specialFibreInclusion) ≫ Q.projection) := by
  dsimp only
  let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
  obtain ⟨ε, hε, hface, hlower⟩ :=
    exists_pos_incidentFacet_dynamicParabolic_le_images C E D.neutral {x} hN x
      (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ _)) ν
  refine ⟨ε, hε, hface, ?_⟩
  intro M hsm hgc hM φ
  have hfull := hlower M {ε • C.cocharacterDirection
      (A.cocharacterSpecialization.symm ν) +ᵥ x}
    (Set.singleton_nonempty _)
    (Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ _)) hM φ
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : ConnectedSpace Q.quotient.X.left := hQ.2.2.connectedSpace
  apply le_antisymm
  · exact unramifiedRay_quotientImage_le_parabolic
      (C := C) (E := E) (D := D) (x := x) (hN := hN)
      (A := A)
      (hA := unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup
        C E D.neutral {x} hN)
      (Q := Q) (hQ := hQ) (ν := ν) (ε := ε) (hε := hε)
      (M := M) (hM := hM) (φ := φ)
      (B := unramifiedZeroFixerIntegralSplitTorusData C E M _ hM) hpositive
  · exact parabolic_le_quotientImage φ.specialFibreMap Q.projection
      (CommGroupScheme.groupHom ν ≫ A.specialFibreInclusion)
      (quotientProjection_smooth D Q hQ) hQ.2.1.2.1 hfull

/-- Conditional exact prescribed-cocharacter attainment for all actual
comparisons from a selected incident ray point. -/
def HasPrescribedIncidentQuotientImageEquality : Prop :=
  Q.IsReductiveQuotient → UnramifiedRootPositiveReductionStatement.{u} →
    ∀ ν : cocharacterLattice
      (unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN).specialFibreTorus,
      let A := unramifiedZeroFixerIntegralSplitTorusData C E D.neutral {x} hN
      let w := C.cocharacterDirection (A.cocharacterSpecialization.symm ν)
      ∃ ε : ℝ, 0 < ε ∧
        AffineRootSystem.IsFaceOf C.affineRoots
          (AffineRootSystem.facet C.affineRoots x)
          (AffineRootSystem.facet C.affineRoots (ε • w +ᵥ x)) ∧
        ∀ (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
          [Smooth M.group.X.hom] [GeometricallyConnected M.group.X.hom],
          M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer
            (C.apartmentMap '' {ε • w +ᵥ x}) →
          ∀ φ : M.Hom D.neutral (𝟙 G),
            SubgroupFunctor.range
                (SchematicImage.inclusion (φ.specialFibreMap ≫ Q.projection)) =
              Dynamic.parabolic
                ((CommGroupScheme.groupHom ν ≫ A.specialFibreInclusion) ≫ Q.projection)

theorem hasPrescribedIncidentQuotientImageEquality :
    HasPrescribedIncidentQuotientImageEquality C E D x hN Q := by
  intro hQ hpositive ν
  exact exists_pos_incidentFacet_quotientImage_eq_parabolic C E D x hN Q hQ hpositive ν

end Langlands.BruhatTits.IntegralModels
