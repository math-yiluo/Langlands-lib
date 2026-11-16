import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.GroupScheme.KernelSquareTransport

/-! # Full and neutral kernels of actual relative-component maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

private theorem specialFibreMap_mono
    (D : RelativeComponentModelData R K G) : Mono D.specialFibreMap.hom.hom := by
  let : GeometricallyConnected D.neutral.group.X.hom := D.neutral_geometricallyConnected
  have hi := D.isRelativeComponent.baseChange (IntegralModel.residueBaseMap R)
  have : IsOpenImmersion D.specialFibreMap.hom.hom.left := hi.isOpenImmersion
  exact Over.mono_of_mono_left _

/-- With geometrically connected full kernel, the neutral kernel has exactly
its full all-test image in the source full special fibre. -/
theorem range_neutralKernel_full_eq
    [GeometricallyConnected (kernel φ.fullSpecialFibreMap).X.hom] :
    SubgroupFunctor.range (kernelι φ.neutralSpecialFibreMap ≫ source.specialFibreMap) =
      SubgroupFunctor.range (kernelι φ.fullSpecialFibreMap) := by
  let : GeometricallyConnected source.neutral.group.X.hom :=
    source.neutral_geometricallyConnected
  have hi := source.isRelativeComponent.baseChange (IntegralModel.residueBaseMap R)
  let k := RelativeIdentityComponent.factor (kernelι φ.fullSpecialFibreMap) hi
  have hk : k ≫ source.specialFibreMap = kernelι φ.fullSpecialFibreMap :=
    RelativeIdentityComponent.factor_comp _ hi
  have hk' : k.hom.hom ≫ source.specialFibreMap.hom.hom =
      (kernelι φ.fullSpecialFibreMap).hom.hom :=
    congrArg (fun f => (Grp.forget (Over (Spec (CommRingCat.of
      (IsLocalRing.ResidueField R))))).map f) hk
  have hcomm : φ.neutralSpecialFibreMap.hom.hom ≫ target.specialFibreMap.hom.hom =
      source.specialFibreMap.hom.hom ≫ φ.fullSpecialFibreMap.hom.hom :=
    congrArg (fun f => (Grp.forget (Over (Spec (CommRingCat.of
      (IsLocalRing.ResidueField R))))).map f) φ.specialFibre_component_comm
  have : Mono target.specialFibreMap.hom.hom := specialFibreMap_mono target
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    apply (mem_range_kernelι_iff φ.fullSpecialFibreMap _).mpr
    change (z ≫ (kernelι φ.neutralSpecialFibreMap).hom.hom ≫
      source.specialFibreMap.hom.hom) ≫ φ.fullSpecialFibreMap.hom.hom = 1
    rw [Category.assoc, Category.assoc, ← hcomm, ← Category.assoc,
      ← Category.assoc]
    have hz : (z ≫ (kernelι φ.neutralSpecialFibreMap).hom.hom) ≫
        φ.neutralSpecialFibreMap.hom.hom = 1 :=
      (kernelPointsEquiv φ.neutralSpecialFibreMap U z).property
    rw [hz, MonObj.one_comp]
  · rintro ⟨z, rfl⟩
    let y := z ≫ k.hom.hom
    have hy : y ≫ φ.neutralSpecialFibreMap.hom.hom = 1 := by
      apply (cancel_mono target.specialFibreMap.hom.hom).mp
      rw [MonObj.one_comp, Category.assoc, hcomm]
      change (z ≫ k.hom.hom) ≫ (source.specialFibreMap.hom.hom ≫
        φ.fullSpecialFibreMap.hom.hom) = 1
      rw [Category.assoc, ← Category.assoc k.hom.hom, hk', ← Category.assoc]
      exact (kernelPointsEquiv φ.fullSpecialFibreMap U z).property
    let w := (kernelPointsEquiv φ.neutralSpecialFibreMap U).symm ⟨y, hy⟩
    have hw : w ≫ (kernelι φ.neutralSpecialFibreMap).hom.hom = y :=
      congrArg Subtype.val
        ((kernelPointsEquiv φ.neutralSpecialFibreMap U).apply_symm_apply ⟨y, hy⟩)
    refine ⟨w, ?_⟩
    change w ≫ ((kernelι φ.neutralSpecialFibreMap).hom.hom ≫
      source.specialFibreMap.hom.hom) = z ≫ (kernelι φ.fullSpecialFibreMap).hom.hom
    rw [← Category.assoc, hw]
    change (z ≫ k.hom.hom) ≫ source.specialFibreMap.hom.hom = _
    rw [Category.assoc, hk']

/-- The actual full and neutral scheme-theoretic kernels are canonically
isomorphic when the full kernel is geometrically connected. -/
def specialFibreKernelIsoFull
    [GeometricallyConnected (kernel φ.fullSpecialFibreMap).X.hom] :
    kernel φ.neutralSpecialFibreMap ≅ kernel φ.fullSpecialFibreMap := by
  have : Mono source.specialFibreMap.hom.hom := specialFibreMap_mono source
  have : Mono (kernelι φ.neutralSpecialFibreMap ≫ source.specialFibreMap).hom.hom := by
    change Mono ((kernelι φ.neutralSpecialFibreMap).hom.hom ≫
      source.specialFibreMap.hom.hom)
    infer_instance
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := SubgroupFunctor.range (kernelι φ.fullSpecialFibreMap))
    ⟨inferInstance, φ.range_neutralKernel_full_eq⟩ ⟨inferInstance, rfl⟩

/-- Smooth connected unipotent full kernels give the same geometry for the
actual neutral map, with no additional neutral-image formula. -/
theorem hasSmoothConnectedUnipotentKernel_of_full
    (hfull : Smooth (kernel φ.fullSpecialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.fullSpecialFibreMap).X.left ∧
        IsUnipotent (kernel φ.fullSpecialFibreMap)) :
    φ.HasSmoothConnectedUnipotentKernel := by
  have : Smooth (kernel φ.fullSpecialFibreMap).X.hom := hfull.1
  have : ConnectedSpace (kernel φ.fullSpecialFibreMap).X.left := hfull.2.1
  have : IsAffineHom source.full.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd source.full.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : IsAffineHom target.full.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd target.full.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  have : IsAffineHom (kernel φ.fullSpecialFibreMap).X.hom := by
    rw [← Over.w (kernelι φ.fullSpecialFibreMap).hom.hom]
    infer_instance
  have : GeometricallyConnected (kernel φ.fullSpecialFibreMap).X.hom :=
    Langlands.GroupScheme.geometricallyConnected_of_connected
      (kernel φ.fullSpecialFibreMap)
  exact smooth_connected_unipotent_of_groupIso φ.specialFibreKernelIsoFull hfull

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme

/-- The actual neutral kernel is the full kernel whenever the latter is
geometrically connected; smooth connected unipotent geometry therefore
passes from the full comparison to the neutral comparison. -/
def RelativeComponentFullKernelStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (source target : RelativeComponentModelData R K G)
    (φ : RelativeComponentModelHom source target),
    (GeometricallyConnected (kernel φ.fullSpecialFibreMap).X.hom →
      Nonempty (kernel φ.neutralSpecialFibreMap ≅ kernel φ.fullSpecialFibreMap)) ∧
    ((Smooth (kernel φ.fullSpecialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.fullSpecialFibreMap).X.left ∧
      IsUnipotent (kernel φ.fullSpecialFibreMap)) →
      φ.HasSmoothConnectedUnipotentKernel)

/-- Full-to-neutral transfer for every supplied actual compatible comparison. -/
theorem relativeComponentFullKernel : RelativeComponentFullKernelStatement.{u} := by
  intro R K _ _ _ _ _ _ G source target φ
  constructor
  · intro h
    let : GeometricallyConnected (kernel φ.fullSpecialFibreMap).X.hom := h
    exact ⟨φ.specialFibreKernelIsoFull⟩
  · exact φ.hasSmoothConnectedUnipotentKernel_of_full

end Langlands.BruhatTits.IntegralModels
