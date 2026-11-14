import Langlands.BruhatTits.IntegralModels.FacetParabolicIncidence
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolicOrder
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Actual images and parabolic correspondence through the special-fibre quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}

private instance transfer_neutralSpecialFibre_affine
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance transfer_neutralSpecialFibre_smooth
    (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance transfer_neutralSpecialFibre_connected
    (D : RelativeComponentModelData R K G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G}
  (Q : SpecialFibreQuotientData D)

/-- Full inverse image identifies all parabolics of the supplied quotient with
all parabolics of the actual neutral special fibre. -/
def parabolicComapOrderIso (hQ : Q.IsReductiveQuotient) :
    ParabolicFunctor Q.quotient ≃o ParabolicFunctor D.neutral.specialFibre := by
  have : Flat Q.projection.hom.hom.left := hQ.2.1.1
  have : Surjective Q.projection.hom.hom.left := hQ.2.1.2.1
  have : LocallyOfFinitePresentation Q.projection.hom.hom.left := hQ.2.1.2.2.1
  exact UnipotentQuotientParabolics.parabolicComapOrderIso
    Q.projection (hasSmoothConnectedUnipotentKernel (Q := Q) hQ)

@[simp] theorem parabolicComapOrderIso_apply_coe (hQ : Q.IsReductiveQuotient)
    (P : ParabolicFunctor Q.quotient) :
    (Q.parabolicComapOrderIso hQ P).val = P.val.comap Q.projection :=
  rfl

@[simp] theorem parabolicComapOrderIso_symm_comap (hQ : Q.IsReductiveQuotient)
    (P : ParabolicFunctor D.neutral.specialFibre) :
    ((Q.parabolicComapOrderIso hQ).symm P).val.comap Q.projection = P.val :=
  congrArg Subtype.val ((Q.parabolicComapOrderIso hQ).apply_symm_apply P)

end SpecialFibreQuotientData

namespace RelativeComponentModelHom

variable {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)

/-- A parabolic actual special-fibre image has a parabolic actual quotient image,
whose full inverse image is precisely the original special-fibre image. -/
theorem parabolicReductiveImage_and_comap (hQ : Q.IsReductiveQuotient)
    (hφ : φ.HasParabolicSpecialFibreImage) :
    φ.HasParabolicReductiveImage Q ∧
      (SubgroupFunctor.range (φ.reductiveImageInclusion Q)).comap Q.projection =
        SubgroupFunctor.range φ.specialFibreImageInclusion := by
  have : Flat Q.projection.hom.hom.left := hQ.2.1.1
  have : Surjective Q.projection.hom.hom.left := hQ.2.1.2.1
  have : LocallyOfFinitePresentation Q.projection.hom.hom.left := hQ.2.1.2.2.1
  have : IsAffine source.neutral.specialFibre.X.left :=
    isAffine_of_isAffineHom source.neutral.specialFibre.X.hom
  have : IsAffine target.neutral.specialFibre.X.left :=
    isAffine_of_isAffineHom target.neutral.specialFibre.X.hom
  have : IsAffineHom φ.neutralSpecialFibreMap.hom.hom.left := isAffineHom_of_isAffine _
  have : QuasiCompact φ.neutralSpecialFibreMap.hom.hom.left :=
    quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact
  obtain ⟨I, j, p, hj, hfac, _, hps, _, _, heq, _⟩ :=
    UnipotentQuotientParabolics.exists_parabolic_image Q.projection
      (SpecialFibreQuotientData.hasSmoothConnectedUnipotentKernel (Q := Q) hQ)
      φ.specialFibreImageInclusion hφ
  have : Surjective p.hom.hom.left := hps
  have : Smooth I.X.hom := hj.smooth
  have : IsReduced I.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (IsLocalRing.ResidueField R) I.X.left I.X.hom
  have : IsSchemeTheoreticallyDominant p.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant
      (SchematicImage.projection φ.neutralSpecialFibreMap ≫ p).hom.hom.left := by
    change IsSchemeTheoreticallyDominant
      ((SchematicImage.projection φ.neutralSpecialFibreMap).hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  have hclosed : IsClosedSubgroup (φ.reductiveImageInclusion Q) :=
    inferInstanceAs (IsClosedImmersion (φ.reductiveImageInclusion Q).hom.hom.left)
  have hrange : SubgroupFunctor.range j =
      SubgroupFunctor.range (φ.reductiveImageInclusion Q) :=
    SchematicImage.range_eq_of_dominantFactorizations
      (SchematicImage.projection φ.neutralSpecialFibreMap ≫ p)
      (SchematicImage.projection (φ.neutralSpecialFibreMap ≫ Q.projection))
      j (φ.reductiveImageInclusion Q) hj.isClosedSubgroup hclosed (by
        rw [Category.assoc, ← hfac, ← Category.assoc,
          SchematicImage.projection_inclusion, SchematicImage.projection_inclusion])
  exact ⟨hj.of_range_eq hclosed hrange, by rw [← hrange]; exact heq⟩

end RelativeComponentModelHom

namespace FacetModelData

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsAffineHom G.X.hom] {B : ValuationBuildingData G}
  (M : FacetModelData B R) (F : BuildingFacet B)

/-- The geometric input before passing to the reductive quotient: the actual
special-fibre image parametrizes every parabolic subgroup functor exactly once. -/
def HasFacetSpecialFibreParabolicBijection : Prop :=
  Set.BijOn (M.incidentSpecialFibreImage F) Set.univ
    {P | IsParabolicFunctor P}

/-- Actual image comparison on an incident facet, including its parabolicity
in the specified quotient and its exact full inverse image. -/
theorem incidentParabolicImage_isParabolic_and_comap
    (Q : SpecialFibreQuotientData (M.model F)) (hQ : Q.IsReductiveQuotient)
    (F' : IncidentFacets B F)
    (hF' : IsParabolicFunctor (M.incidentSpecialFibreImage F F')) :
    IsParabolicFunctor (M.incidentParabolicImage F Q F') ∧
      (M.incidentParabolicImage F Q F').comap Q.projection =
        M.incidentSpecialFibreImage F F' := by
  let φ := M.morphism F F'.val F'.property
  have hclosed : IsClosedSubgroup φ.specialFibreImageInclusion :=
    inferInstanceAs (IsClosedImmersion φ.specialFibreImageInclusion.hom.hom.left)
  have hφ : φ.HasParabolicSpecialFibreImage :=
    (isParabolicFunctor_range_iff hclosed).mp hF'
  obtain ⟨hpar, heq⟩ := φ.parabolicReductiveImage_and_comap Q hQ hφ
  exact ⟨⟨φ.reductiveImage Q, φ.reductiveImageInclusion Q, hpar, rfl⟩, heq⟩

/-- A geometric special-fibre bijection transfers to the unchanged facet
parabolic-order predicate for every supplied reductive quotient. -/
theorem hasFacetParabolicOrderBijection_of_specialFibre
    (h : M.HasFacetSpecialFibreParabolicBijection F)
    (Q : SpecialFibreQuotientData (M.model F)) (hQ : Q.IsReductiveQuotient) :
    M.HasFacetParabolicOrderBijection F Q := by
  have hc (F' : IncidentFacets B F) :=
    M.incidentParabolicImage_isParabolic_and_comap F Q hQ F'
      (h.mapsTo (Set.mem_univ F'))
  refine ⟨⟨?_, ?_, ?_⟩, M.incidentParabolicImage_le F Q⟩
  · intro F' _
    exact (hc F').1
  · intro F₁ _ F₂ _ heq
    apply h.injOn (Set.mem_univ F₁) (Set.mem_univ F₂)
    rw [← (hc F₁).2, ← (hc F₂).2, heq]
  · intro P hP
    let e := Q.parabolicComapOrderIso hQ
    obtain ⟨F', _, hF'⟩ := h.surjOn (e ⟨P, hP⟩).property
    refine ⟨F', Set.mem_univ F', ?_⟩
    have he : e ⟨M.incidentParabolicImage F Q F', (hc F').1⟩ = e ⟨P, hP⟩ := by
      apply Subtype.ext
      exact (hc F').2.trans hF'
    exact congrArg Subtype.val (e.injective he)

end FacetModelData
end Langlands.BruhatTits.IntegralModels
