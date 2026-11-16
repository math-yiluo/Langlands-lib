import Langlands.GroupScheme.Reductive.SmoothTargetMonomorphismImmersion
import Langlands.GroupScheme.GenericSubgroupClosureFactorization
import Langlands.GroupScheme.DvrAffineClosureReduction
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # The smooth generic closure of a reductive monomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ReductiveGenericClosure

/-- A quasi-compact schematically dominant immersion is open. -/
theorem isOpenImmersion_of_schematicDominance {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    IsOpenImmersion f := by
  have hp : IsPullback (𝟙 X) f.liftCoborder f f.coborderRange.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have : IsSchemeTheoreticallyDominant f.liftCoborder :=
    IsSchemeTheoreticallyDominant.of_isPullback hp
  have : IsIso f.liftCoborder :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr f.liftCoborder.ker_eq_bot
  rw [← f.liftCoborder_ι]
  infer_instance

section Construction

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Flat M.X.hom] [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left]

/-- The actual generic map of the monomorphism. -/
abbrev genericMap :=
  (baseChange (Spec.algebraMap R K)).map f

instance genericMap_isClosedImmersion :
    IsClosedImmersion (genericMap (K := K) f).hom.hom.left :=
  DvrAffineClosureReduction.genericMap_isClosedImmersion f

/-- The schematic closure of the generic image, with its induced group structure. -/
abbrev closure : GroupScheme (Spec (CommRingCat.of R)) :=
  GenericSubgroupClosure.closureGroup G (genericMap (K := K) f)

/-- The canonical factor through the schematic closure of the generic image. -/
def factor : M ⟶ closure (K := K) f :=
  GenericSubgroupClosure.factor G (genericMap (K := K) f) f (𝟙 _) (by simp)

/-- The actual closed inclusion of this closure in the original target. -/
abbrev inclusion : closure (K := K) f ⟶ G :=
  GenericSubgroupClosure.closureInclusion G (genericMap (K := K) f)

@[reassoc (attr := simp)]
theorem factor_inclusion : factor (K := K) f ≫ inclusion (K := K) f = f :=
  GenericSubgroupClosure.factor_fac _ _ _ _ _

instance factor_mono :
    Mono (factor (K := K) f).hom.hom.left :=
  mono_of_mono_fac (congrArg (fun a => a.hom.hom.left) (factor_inclusion (K := K) f))

theorem genericProjection_factor :
    GenericSubgroupClosure.genericProjection (K := K) M ≫
        (factor (K := K) f).hom.hom =
      GenericSubgroupClosure.projectionOver G (genericMap (K := K) f) := by
  apply (cancel_mono (GenericSubgroupClosure.inclusionOver G
    (genericMap (K := K) f))).mp
  rw [Category.assoc]
  change GenericSubgroupClosure.genericProjection M ≫
      ((factor (K := K) f ≫ inclusion (K := K) f).hom.hom) = _
  rw [factor_inclusion, GenericSubgroupClosure.projectionOver_fac]
  simpa only [GenericSubgroupClosure.genericProjection,
    GenericSubgroupClosure.genericOver, Category.id_comp] using
    (baseChangePointsEquiv_comp (Spec.algebraMap R K) f
      ((baseChange (Spec.algebraMap R K)).obj M).X (𝟙 _)).symm

instance factor_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (factor (K := K) f).hom.hom.left := by
  refine ⟨le_antisymm ?_ bot_le⟩
  rw [← (GenericSubgroupClosure.projectionOver G
    (genericMap (K := K) f)).left.ker_eq_bot,
    ← genericProjection_factor, Over.comp_left]
  exact Scheme.Hom.le_ker_comp _ _

instance factor_isAffineHom :
    IsAffineHom (factor (K := K) f).hom.hom.left := by
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : IsAffine (closure (K := K) f).X.left :=
    isAffine_of_isAffineHom (closure (K := K) f).X.hom
  infer_instance

theorem factor_isOpenImmersion (hM : IsReductive M) :
    IsOpenImmersion (factor (K := K) f).hom.hom.left := by
  have : IsImmersion f.hom.hom.left := ReductiveImmersion.isImmersion_of_mono hM f
  have hf :
      (factor (K := K) f).hom.hom.left ≫ (inclusion (K := K) f).hom.hom.left =
        f.hom.hom.left :=
    congrArg (fun a => a.hom.hom.left) (factor_inclusion (K := K) f)
  have : IsImmersion ((factor (K := K) f).hom.hom.left ≫
      (inclusion (K := K) f).hom.hom.left) := hf.symm ▸ inferInstance
  have : IsImmersion (factor (K := K) f).hom.hom.left :=
    IsImmersion.of_comp (factor (K := K) f).hom.hom.left (inclusion (K := K) f).hom.hom.left
  have : QuasiCompact (factor (K := K) f).hom.hom.left := inferInstance
  exact isOpenImmersion_of_schematicDominance _

/-- The open subgroup of the closure presented by the reductive source. -/
def imageOpen (hM : IsReductive M) : (closure (K := K) f).X.left.Opens :=
  letI := factor_isOpenImmersion (K := K) f hM
  (factor (K := K) f).hom.hom.left.opensRange

/-- The source is canonically isomorphic to its actual open image in the closure. -/
def openIso (hM : IsReductive M) :
    M.X.left ≅ (imageOpen (K := K) f hM).toScheme :=
  letI := factor_isOpenImmersion (K := K) f hM
  IsOpenImmersion.isoOfRangeEq (factor (K := K) f).hom.hom.left
    (imageOpen (K := K) f hM).ι (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc (attr := simp)]
theorem openIso_hom_ι (hM : IsReductive M) :
    (openIso (K := K) f hM).hom ≫ (imageOpen (K := K) f hM).ι =
      (factor (K := K) f).hom.hom.left := by
  let := factor_isOpenImmersion (K := K) f hM
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem closure_smooth (hM : IsReductive M) :
    Smooth (closure (K := K) f).X.hom := by
  have := hM.smooth
  have : IsOpenImmersion (factor (K := K) f).hom.hom.left :=
    factor_isOpenImmersion f hM
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField s
  let Cb := (baseChange b).obj (closure (K := K) f)
  let Mb := (baseChange b).obj M
  let a := (baseChange b).map (factor (K := K) f)
  have : LocallyOfFiniteType Cb.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (closure (K := K) f).X.hom b))
  have : Smooth Mb.X.hom :=
    inferInstanceAs (Smooth (pullback.snd M.X.hom b))
  have : IsOpenImmersion a.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b
      (factor (K := K) f).hom.hom inferInstance
  exact smooth_of_smooth_open_subgroup Cb Mb a

section GeometricIdentityComponent

variable (hM : IsReductive M)

local instance (s : Spec (CommRingCat.of R)) :
    IsAffineHom (geometricFiber (closure (K := K) f) s).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd (closure (K := K) f).X.hom
    (geometricPoint _ s)))

/-- Each geometric source fibre is the actual identity component of the closure fibre. -/
def geometricFiberIdentityIso (s : Spec (CommRingCat.of R)) :
    letI : Smooth (geometricFiber (closure (K := K) f) s).X.hom :=
      MorphismProperty.pullback_snd _ _ (closure_smooth f hM)
    geometricFiber M s ≅ identityComponent (geometricFiber (closure (K := K) f) s) := by
  letI : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
  letI : Smooth (geometricFiber (closure (K := K) f) s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd (closure (K := K) f).X.hom
      (geometricPoint _ s)))
  let b := geometricPoint (Spec (CommRingCat.of R)) s
  let a := (baseChange b).map (factor (K := K) f)
  have : Smooth (geometricFiber M s).X.hom := (hM.geometricFiber s).smooth
  have : IsAffineHom (geometricFiber M s).X.hom := (hM.geometricFiber s).isAffineHom
  have : ConnectedSpace (geometricFiber M s).X.left := (hM.geometricFiber s).connectedSpace
  have : Mono (factor (K := K) f).hom.hom := Over.mono_of_mono_left _
  have : Mono a.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map (factor (K := K) f).hom.hom))
  have : IsClosedImmersion a.hom.hom.left := HomImage.isClosedSubgroup_of_mono a
  have : IsOpenImmersion (factor (K := K) f).hom.hom.left :=
    factor_isOpenImmersion f hM
  have : IsOpenImmersion a.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b
      (factor (K := K) f).hom.hom inferInstance
  exact IdentityComponent.isoOfIsOpenImmersion _ a

/-- All geometric identity components of the smooth generic closure are reductive. -/
theorem identityComponentReductiveLocus_eq_univ :
    letI : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
    identityComponentReductiveLocus (closure (K := K) f) = Set.univ := by
  let : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
  apply Set.eq_univ_of_forall
  intro s
  exact (hM.geometricFiber s).isConnectedReductive_of_isAlgClosed.of_iso
    (geometricFiberIdentityIso f hM s).symm

end GeometricIdentityComponent

end Construction

end Langlands.GroupScheme.ReductiveGenericClosure
