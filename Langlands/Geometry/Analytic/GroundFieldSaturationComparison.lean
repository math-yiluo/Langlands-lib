import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor

/-! # Scalar extension before and after saturation of a small-index atlas -/

noncomputable section

universe u v u'

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, 0} K)

private def saturatedIndexUp : A.saturatedPresentation.atlas.Index ≃
    A.saturationTarget.atlas.Index :=
  (Equiv.ulift : ULift.{0} A.atlas.localDomainFamily ≃ A.atlas.localDomainFamily).symm

private def fromSaturationUnlifted : StrongHom A.saturatedPresentation A.saturationSource :=
  A.fromSaturation.reindex A.saturatedIndexUp (Equiv.refl A.saturationSource.atlas.Index)

/-- Remove the width-zero lift on the saturated charts of the comparison,
retaining the lift of the original chart indices into the ambient universe. -/
def saturatedToLiftedOriginal : CompatibleStrongHom A.saturatedPresentation A.saturationSource :=
  CompatibleStrongHom.ofSaturated A.fromSaturationUnlifted A.atlas.saturatedAtlas_hasAllLocalDomains

@[simp]
theorem saturatedToLiftedOriginal_baseMap :
    A.saturatedToLiftedOriginal.baseMap = ContinuousMap.id A.space := rfl

theorem saturatedToLiftedOriginal_isQuasiIso :
    A.saturatedToLiftedOriginal.toStrongHom.IsQuasiIso :=
  A.isQuasiIso_fromSaturation.reindex _ _

open IndexedAffinoidAtlas (LocalDomain)

theorem saturatedToLiftedOriginal_admissible (i : A.atlas.Index) :
    A.saturatedToLiftedOriginal.baseMap ''
        range (A.saturatedPresentation.atlas.chart (A.atlas.originalSaturatedIndex i)) ⊆
      range (A.saturationSource.atlas.chart (ULift.up i)) := by
  change id '' range (A.atlas.saturatedChart (A.atlas.originalSaturatedIndex i)) ⊆
    range (A.atlas.chart i)
  rw [image_id]
  exact (A.atlas.saturatedAtlas_original_range i).subset

/-- At an original chart this comparison uses the bounded identity, after
identifying the original and the chosen saturated algebra. -/
theorem saturatedToLiftedOriginal_pullback_heq (i : A.atlas.Index) :
    HEq (A.saturatedToLiftedOriginal.pullback (A.atlas.originalSaturatedIndex i) (ULift.up i)
      (A.saturatedToLiftedOriginal_admissible i)) (BoundedAlgHom.id K (A.atlas.algebra i)) := by
  have aux : ∀ (U : LocalDomain A.atlas), U = A.atlas.originalLocalDomain i →
      ∀ (p : U ⟶ A.atlas.originalLocalDomain i),
        HEq p.restriction (BoundedAlgHom.id K (A.atlas.algebra i)) := by
    intro U hU p
    subst U
    let D := A.atlas.originalLocalDomain i
    let q : LocalDomain.Inclusion D D := 𝟙 D
    have hId : (show LocalDomain.Inclusion D D from p) = q := Subsingleton.elim _ _
    have hp : p.restriction = q.restriction := congrArg LocalDomain.Inclusion.restriction hId
    exact heq_of_eq hp
  exact aux _ (A.atlas.saturatedRepresentative_original i) _

namespace GroundFieldExtension

open IndexedAffinoidAtlas.GroundFieldExtension (presentation projection)

variable (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- The actual extension of the saturation comparison, before localization on L. -/
def extendedSaturationComparison : CompatibleStrongHom
    (presentation K L A.saturatedPresentation.atlas)
    (presentation K L A.saturationSource.atlas) :=
  compatibleMap K L A.saturatedToLiftedOriginal

@[simp]
theorem projection_extendedSaturationComparison
    (z : (presentation K L A.saturatedPresentation.atlas).space) :
    projection K L A.saturationSource.atlas ((extendedSaturationComparison A L).baseMap z) =
      projection K L A.saturatedPresentation.atlas z :=
  projection_pointMap K L _ A.saturatedToLiftedOriginal.compatible z

open PresentedAffinoidAlgebra.GroundFieldExtension (algebra map map_id)

omit [CompleteSpace K] in
private theorem map_heq {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') {f : BoundedAlgHom K S R} {g : BoundedAlgHom K S' R'}
    (h : HEq f g) : HEq (map K L f) (map K L g) := by
  cases hR
  cases hS
  cases eq_of_heq h
  rfl

theorem extendedSaturationComparison_admissible (i : A.atlas.Index) :
    (extendedSaturationComparison A L).baseMap ''
      range ((presentation K L A.saturatedPresentation.atlas).atlas.chart
        (A.atlas.originalSaturatedIndex i)) ⊆
      range ((presentation K L A.saturationSource.atlas).atlas.chart (ULift.up i)) :=
  (admissible_iff K L _ A.saturatedToLiftedOriginal.compatible
    (A.atlas.originalSaturatedIndex i) (ULift.up i)).2 (A.saturatedToLiftedOriginal_admissible i)

/-- The extended comparison retains the entire bounded identity at every
original chart, after identifying the extended algebras. -/
theorem extendedSaturationComparison_pullback_heq (i : A.atlas.Index) :
    HEq ((extendedSaturationComparison A L).pullback
      (A.atlas.originalSaturatedIndex i) (ULift.up i)
      (extendedSaturationComparison_admissible A L i))
      (BoundedAlgHom.id L (algebra K L (A.atlas.algebra i))) := by
  change HEq (map K L (A.saturatedToLiftedOriginal.pullback
      (A.atlas.originalSaturatedIndex i) (ULift.up i) (A.saturatedToLiftedOriginal_admissible i))) _
  exact (map_heq L (A.atlas.saturatedAtlas_original_algebra i) rfl
    (A.saturatedToLiftedOriginal_pullback_heq i)).trans (heq_of_eq (map_id K L _))

end GroundFieldExtension
end Langlands.Analytic.AffinoidAtlasPresentation
