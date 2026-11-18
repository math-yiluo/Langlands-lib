import Langlands.GroupScheme.EndomorphismFixedSubgroup
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.AlgebraicGeometry.AffineSmoothRetract

/-! # Actual closed retracts of idempotent group-scheme maps -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The actual closed fixed subgroup and retract image of an idempotent. -/
structure IdempotentRetract (ψ : G ⟶ G) where
  group : GroupScheme S
  inclusion : group ⟶ G
  projection : G ⟶ group
  closed : IsClosedSubgroup inclusion
  factorization : projection ≫ inclusion = ψ
  retraction : inclusion ≫ projection = 𝟙 group
  fixed_eq : SubgroupFunctor.range inclusion = endomorphismFixedSubgroup ψ
  range_eq : SubgroupFunctor.range inclusion = SubgroupFunctor.range ψ

/-- Over any base, an idempotent of a separated group has an actual closed
retract image, equal to its fixed subgroup and its full pointwise image. -/
def idempotentRetract [IsSeparated G.X.hom] (ψ : G ⟶ G) (hidem : ψ ≫ ψ = ψ) :
    IdempotentRetract ψ := by
  apply Classical.choice
  obtain ⟨H, i, hi, hic⟩ := endomorphismFixedSubgroup_isClosedRepresentable ψ
  let p := hi.factorHom ψ ((range_le_endomorphismFixedSubgroup_iff ψ ψ).mpr hidem)
  have hpi : p ≫ i = ψ := hi.factorHom_comp ψ _
  have hfix : i ≫ ψ = i :=
    (range_le_endomorphismFixedSubgroup_iff ψ i).mp hi.2.le
  let : Mono i.hom.hom := hi.1
  let : Mono i := (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono i.hom.hom))
  have hret : i ≫ p = 𝟙 H := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc, hpi, Category.id_comp] using hfix
  have hrange : SubgroupFunctor.range i = SubgroupFunctor.range ψ := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine SubgroupFunctor.mem_range.mpr ⟨y ≫ i.hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hfix]
      rfl
    · rintro ⟨y, rfl⟩
      refine SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hpi]
      rfl
  exact ⟨⟨H, i, p, hic, hpi, hret, hi.2, hrange⟩⟩

namespace IdempotentRetract

variable {ψ : G ⟶ G} (P : IdempotentRetract ψ)

@[reassoc (attr := simp)]
theorem inclusion_comp : P.inclusion ≫ ψ = P.inclusion := by
  calc
    P.inclusion ≫ ψ = P.inclusion ≫ (P.projection ≫ P.inclusion) :=
      congrArg (fun f => P.inclusion ≫ f) P.factorization.symm
    _ = (P.inclusion ≫ P.projection) ≫ P.inclusion := (Category.assoc _ _ _).symm
    _ = P.inclusion := by rw [P.retraction, Category.id_comp]

/-- Affineness of the source is inherited by the closed retract. -/
theorem affine [IsAffineHom G.X.hom] : IsAffineHom P.group.X.hom := by
  let : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
  rw [← P.inclusion.hom.hom.w]
  infer_instance

/-- The actual retract image of a smooth affine group is smooth over any base. -/
theorem smooth [IsAffineHom G.X.hom] [Smooth G.X.hom] : Smooth P.group.X.hom := by
  let : IsAffineHom P.group.X.hom := P.affine
  exact AffineRetractGeometry.smooth_of_retract_anyBase
    P.inclusion.hom.hom P.projection.hom.hom
    (congrArg (fun f => f.hom.hom) P.retraction)

/-- Connectedness passes to the retract without any field hypothesis. -/
theorem connected [ConnectedSpace G.X.left] : ConnectedSpace P.group.X.left :=
  AffineRetractGeometry.connectedSpace_of_retract
    P.inclusion.hom.hom P.projection.hom.hom
    (congrArg (fun f => f.hom.hom) P.retraction)

/-- Geometrically connected fibres pass to the actual retract image. -/
theorem geometricallyConnected [GeometricallyConnected G.X.hom] :
    GeometricallyConnected P.group.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ b
  let F := Over.pullback b
  have : ConnectedSpace (F.obj G.X).left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom)) K b
  exact AffineRetractGeometry.connectedSpace_of_retract
    (F.map P.inclusion.hom.hom) (F.map P.projection.hom.hom) (by
      rw [← F.map_comp, ← Grp.comp_hom_hom, P.retraction, Grp.id_hom_hom, F.map_id])

end IdempotentRetract

end Langlands.GroupScheme
