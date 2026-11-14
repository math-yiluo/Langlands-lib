import Langlands.BruhatTits.IntegralModels.IntegralRootModelMapIso
import Langlands.GroupScheme.KernelSquareTransport

/-! # Actual incident root images in a reductive quotient at equal depths -/

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

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData source S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData target)

/-- The original actual source-root map into the target reductive quotient. -/
def rootTargetReductiveQuotientMap (a : characterLattice S) (ha : a ≠ 0) :
    ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre ⟶ Q.quotient :=
  ((T.toIntegralSplitTorusData hT).rootModelMap a ha).specialFibreMap ≫
    φ.neutralSpecialFibreMap ≫ Q.projection

/-- The actual composite factors through the canonical residue root map. -/
theorem rootTargetReductiveQuotientMap_eq (a : characterLattice S) (ha : a ≠ 0) :
    φ.rootTargetReductiveQuotientMap T hT Q a ha =
      φ.residueRootMap T hT a ha ≫
        ((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootReductiveQuotientMap
          Q a ha :=
  (φ.residueRootMap_quotient_comp T hT Q a ha).symm

private instance rootSpecialFibre_affine (a : characterLattice S) (ha : a ≠ 0) :
    IsAffineHom ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    ((T.toIntegralSplitTorusData hT).rootModel a ha).group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance rootSpecialFibre_smooth (a : characterLattice S) (ha : a ≠ 0) :
    Smooth ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre.X.hom := by
  let A := T.toIntegralSplitTorusData hT
  let : Smooth source.neutral.group.X.hom := source.neutral_smooth
  let : Smooth (A.rootModel a ha).group.X.hom :=
    IntegralModel.SplitRoot.model_isSmooth source.neutral A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero ha)
  change Smooth (CategoryTheory.Limits.pullback.snd
    (A.rootModel a ha).group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance rootSpecialFibre_connected (a : characterLattice S) (ha : a ≠ 0) :
    ConnectedSpace ((T.toIntegralSplitTorusData hT).rootModel a ha).specialFibre.X.left := by
  let A := T.toIntegralSplitTorusData hT
  let : Smooth source.neutral.group.X.hom := source.neutral_smooth
  exact (A.rootModel a ha).hasConnectedSpecialFibre_of_geometricallyConnected
    ((A.rootModel a ha).hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected
      (IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
        source.neutral A.isSplit A.inclusion
        (A.integralCharacter a) (A.integralCharacter_ne_zero ha)))

/-- An invertible actual residue root map transfers smoothness of the full
original root-to-quotient kernel from the target root model. -/
theorem rootTargetReductiveQuotientMap_smooth_kernel_of_isIso
    (hQ : Q.IsReductiveQuotient) (a : characterLattice S) (ha : a ≠ 0)
    [IsIso (φ.residueRootMap T hT a ha)] :
    Smooth (kernel (φ.rootTargetReductiveQuotientMap T hT Q a ha)).X.hom := by
  let B := (φ.mapIntegralTorus T).toIntegralSplitTorusData hT
  let q := B.rootReductiveQuotientMap Q a ha
  let e := kernelSquareIso (φ.rootTargetReductiveQuotientMap T hT Q a ha)
    q (asIso (φ.residueRootMap T hT a ha)) (Iso.refl _) (by
      change φ.residueRootMap T hT a ha ≫ q =
        φ.rootTargetReductiveQuotientMap T hT Q a ha ≫ 𝟙 _
      rw [Category.comp_id]
      exact (φ.rootTargetReductiveQuotientMap_eq T hT Q a ha).symm)
  let eo := (Grp.forget (Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).mapIso e
  have : IsIso eo.hom.left :=
    (Over.forget (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))).map_isIso eo.hom
  let : Smooth ((Grp.forget (Over
    (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).obj (kernel q)).hom :=
    B.rootReductiveQuotientMap_smooth_kernel Q hQ a ha
  change Smooth ((Grp.forget (Over
    (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).obj
      (kernel (φ.rootTargetReductiveQuotientMap T hT Q a ha))).hom
  rw [← eo.hom.w]
  infer_instance

/-- The original incident root differential has the full target cyclic
weight span when the actual residue root map is invertible. -/
theorem rootTargetReductiveQuotientMap_lie_range_of_isIso
    (hQ : Q.IsReductiveQuotient) (a : characterLattice S) (ha : a ≠ 0)
    [IsIso (φ.residueRootMap T hT a ha)] :
    LinearMap.range (Lie.targetMapLinear
      (φ.rootTargetReductiveQuotientMap T hT Q a ha) (IsLocalRing.ResidueField R)) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  have : IsIso (φ.residueRootMap T hT a ha).hom.hom :=
    (Grp.forget (Over (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))).map_isIso
      (φ.residueRootMap T hT a ha)
  have : IsIso (φ.residueRootMap T hT a ha).hom.hom.left :=
    (Over.forget (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))).map_isIso
      (φ.residueRootMap T hT a ha).hom.hom
  have hsurj := Lie.targetMapLinear_surjective_of_smooth
    (φ.residueRootMap T hT a ha) (IsLocalRing.ResidueField R) inferInstance
  rw [φ.rootTargetReductiveQuotientMap_eq T hT Q a ha,
    Lie.targetMapLinear_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  convert
    ((φ.mapIntegralTorus T).toIntegralSplitTorusData hT).rootReductiveQuotientMap_lie_range
      Q hQ a ha using 1
  simp only [IntegralTorusData.toIntegralSplitTorusData_specialFibreInclusion,
    IntegralTorusData.toIntegralSplitTorusData_characterSpecialization,
    φ.mapIntegralTorus_specialFibreInclusion T,
    φ.mapIntegralTorus_characterSpecialization T hT,
    quotientTorusInclusion, targetTorusInclusion, Category.assoc]
  rfl

private instance rootTargetImage_lieCommGroup (a : characterLattice S) (ha : a ≠ 0) :
    CommGroup (lieKernel
      (SchematicImage.image (φ.rootTargetReductiveQuotientMap T hT Q a ha))
      (IsLocalRing.ResidueField R)) :=
  lieKernelCommGroup _

private instance rootTargetImage_lieModule (a : characterLattice S) (ha : a ≠ 0) :
    Module (IsLocalRing.ResidueField R)
      (Additive (lieKernel
        (SchematicImage.image (φ.rootTargetReductiveQuotientMap T hT Q a ha))
        (IsLocalRing.ResidueField R))) :=
  lieKernelModule _

/-- The actual schematic root image has the same full cyclic Lie range;
the proof uses smoothness of the full original composite kernel. -/
theorem rootTargetReductiveQuotientImage_lie_range_of_isIso
    (hQ : Q.IsReductiveQuotient) (a : characterLattice S) (ha : a ≠ 0)
    [IsIso (φ.residueRootMap T hT a ha)] :
    LinearMap.range (Lie.targetMapLinear
      (SchematicImage.inclusion (φ.rootTargetReductiveQuotientMap T hT Q a ha))
      (IsLocalRing.ResidueField R)) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  rw [Lie.range_schematicImage_inclusion_of_smooth_kernel
    (φ.rootTargetReductiveQuotientMap T hT Q a ha)
    (φ.rootTargetReductiveQuotientMap_smooth_kernel_of_isIso T hT Q hQ a ha)]
  exact φ.rootTargetReductiveQuotientMap_lie_range_of_isIso T hT Q hQ a ha

end General

section EqualDepth

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
    (Ω Ω' : Set C.Apartment)
    (hsource : source.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))
    (htarget : target.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty)
    (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hb' : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))

include hQ hsource htarget hne hne' hb hb'

/-- Equal actual zero-fixer depths imply smoothness of the full original
source-root-to-target-quotient kernel. -/
theorem rootTargetReductiveQuotientMap_smooth_kernel_of_rootFixerDepth_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    Smooth (kernel (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)).X.hom := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_rootFixerDepth_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth
  exact φ.rootTargetReductiveQuotientMap_smooth_kernel_of_isIso T hT Q hQ a a.2.1

/-- At equal actual zero-fixer depths, the original differential image
is the full target cyclic root-weight span. -/
theorem rootTargetReductiveQuotientMap_lie_range_of_rootFixerDepth_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    LinearMap.range (Lie.targetMapLinear
      (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1)
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_rootFixerDepth_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth
  exact φ.rootTargetReductiveQuotientMap_lie_range_of_isIso T hT Q hQ a a.2.1

/-- At equal depths, the actual schematic root image has the full target
cyclic Lie range. -/
theorem rootTargetReductiveQuotientImage_lie_range_of_rootFixerDepth_eq
    (x : C.Apartment) (a : relativeRoots C.i)
    (hdepth : C.apartment.rootFixerDepth a x Ω' =
      C.apartment.rootFixerDepth a x Ω) :
    LinearMap.range (Lie.targetMapLinear
      (SchematicImage.inclusion (φ.rootTargetReductiveQuotientMap T hT Q a a.2.1))
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) =
        RelativeRoot.semigroupWeightSpan
          (AutomorphicAction.conjugation (φ.quotientTorusInclusion Q T))
          (RelativeRoot.cyclicTail (T.characterSpecialization hT a) 1) := by
  let : IsIso (φ.residueRootMap T hT a a.2.1) :=
    φ.residueRootMap_isIso_of_rootFixerDepth_eq C E T hT Ω Ω'
      hsource htarget hne hne' hb hb' x a hdepth
  exact φ.rootTargetReductiveQuotientImage_lie_range_of_isIso T hT Q hQ a a.2.1

end EqualDepth

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelHom
