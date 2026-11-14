import Langlands.GroupScheme.IntegralModel.KernelCentralizerRoots

/-! # Integral root points in a full-kernel centralizer component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.KernelCentralizerData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G}
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ M.group} {a : characterLattice T}
    (D : KernelCentralizerData M i a) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T)

local notation "χC" => (CommGroupScheme.groupHom ν ≫ D.torus hT)
local notation "χF" => (χC ≫ D.componentHom)
local notation "UF" => (Dynamic.Affine.unipotentScheme χF)
local notation "jF" => (Dynamic.Affine.unipotentHom χF)

local instance : IsAffine D.fullGroup.X.left := isAffine_of_isAffineHom D.fullGroup.X.hom

/-- The full centralizer's dynamic unipotent has connected fibres, so its
actual integral inclusion factors through the relative identity component. -/
def fullUnipotentToComponent : UF ⟶ D.componentGroup := by
  have : GeometricallyConnected (UF).X.hom :=
    ((dynamicBaseSmoothConnected _ D.fullGroup χF _ _).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom χF)).2
  exact Classical.choose (D.isRelativeComponent.exists_hom_lift jF)

@[reassoc]
theorem fullUnipotentToComponent_comp :
    D.fullUnipotentToComponent hT ν ≫ D.componentHom = jF := by
  have : GeometricallyConnected (UF).X.hom :=
    ((dynamicBaseSmoothConnected _ D.fullGroup χF _ _).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom χF)).2
  exact Classical.choose_spec (D.isRelativeComponent.exists_hom_lift jF)

variable [IsDiscreteValuationRing R]

local instance : IsAffineHom D.componentGroup.X.hom := D.model.affine
local instance : IsAffine D.componentGroup.X.left :=
  isAffine_of_isAffineHom D.componentGroup.X.hom

/-- Every ambient integral section whose actual generic restriction belongs
to the positive root functor has integral canonical dynamic coordinates in
the full-kernel centralizer's relative identity component. -/
theorem exists_integralRootUnipotentLift (hpos : 0 < latticePairing T a ν)
    (x : M.integralSections)
    (hx : baseChangeSectionHom (Spec.algebraMap R K) M.group x ∈
      (RelativeRoot.subgroup ((baseChange (Spec.algebraMap R K)).map i)
        (characterLattice.baseChange (Spec.algebraMap R K) T a)).carrier
          (Over.mk (𝟙 _))) :
    ∃ y : rationalPoints (Dynamic.Affine.unipotentScheme χC),
      rationalPoints.map
        (Dynamic.Affine.unipotentHom χC ≫ D.componentHom ≫ D.fullHom) y = x := by
  let b := Spec.algebraMap R K
  let χCK := Dynamic.baseChangeCocharacter b χC
  let χFK := Dynamic.baseChangeCocharacter b χF
  let f := D.componentHom ≫ D.fullHom
  have hx' : baseChangeSectionHom b M.group x ∈
      ((Dynamic.unipotent χCK).map ((baseChange b).map f)).carrier
        (Over.mk (𝟙 _)) := by
    rw [D.dynamicUnipotent_fibre_map hT b ν hpos]
    exact hx
  obtain ⟨yC, hyC, hyCx⟩ := SubgroupFunctor.mem_map.mp hx'
  have hyF : yC ≫ ((baseChange b).map D.componentHom).hom.hom ∈
      (Dynamic.unipotent χFK).carrier (Over.mk (𝟙 _)) := by
    have h := Dynamic.unipotent_le_comap χCK
      ((baseChange b).map D.componentHom) _ hyC
    simpa only [SubgroupFunctor.mem_comap, χFK, χCK, Dynamic.baseChangeCocharacter, Functor.map_comp,
      Category.assoc] using h
  have hrepF := (Dynamic.Affine.isRepresentedBy_unipotentHom χF).baseChange b
  rw [← Dynamic.unipotent_baseChange] at hrepF
  have hyFrange : yC ≫ ((baseChange b).map D.componentHom).hom.hom ∈
      (SubgroupFunctor.range ((baseChange b).map jF)).carrier (Over.mk (𝟙 _)) := by
    rw [hrepF.2]
    exact hyF
  obtain ⟨yF, hyF⟩ := SubgroupFunctor.mem_range.mp hyFrange
  have hclosed : IsClosedSubgroup (jF ≫ D.fullHom) :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χF).comp D.fullClosed
  have hxyF : M.integralPointMap x =
      rationalPoints.map (M.genericHom (jF ≫ D.fullHom)) yF := by
    change baseChangeSectionHom b M.group x ≫ M.genericIso.hom.hom.hom =
      yF ≫ ((baseChange b).map (jF ≫ D.fullHom) ≫ M.genericIso.hom).hom.hom
    have heq : yF ≫ ((baseChange b).map (jF ≫ D.fullHom)).hom.hom =
        baseChangeSectionHom b M.group x := by
      rw [Functor.map_comp, Grp.comp_hom_hom, ← Category.assoc, hyF, Category.assoc]
      simpa only [f, Functor.map_comp, Grp.comp_hom_hom] using hyCx
    rw [Grp.comp_hom_hom, ← Category.assoc, heq]
  obtain ⟨zF, hzFx, hzF⟩ :=
    M.exists_eq_of_integralPointMap_eq (jF ≫ D.fullHom) hclosed x yF hxyF
  let zC : rationalPoints D.componentGroup :=
    rationalPoints.map (D.fullUnipotentToComponent hT ν) zF
  have hzCx : rationalPoints.map f zC = x := by
    change zF ≫ (D.fullUnipotentToComponent hT ν ≫
      (D.componentHom ≫ D.fullHom)).hom.hom = x
    rw [← Category.assoc, D.fullUnipotentToComponent_comp]
    exact hzFx
  have hzCK : baseChangeSectionHom b D.componentGroup zC = yC := by
    have hmono : Mono ((baseChange b).map f).hom.hom := by
      have : IsOpenImmersion D.componentHom.hom.hom.left :=
        D.isRelativeComponent.isOpenImmersion
      have : IsClosedImmersion ((baseChange b).map D.fullHom).hom.hom.left :=
        D.fullClosed.baseChange b
      have : Mono ((baseChange b).map D.componentHom).hom.hom := inferInstance
      have : Mono ((baseChange b).map D.fullHom).hom.hom := Over.mono_of_mono_left _
      simpa only [f, Functor.map_comp, Grp.comp_hom_hom] using
        (inferInstance : Mono (((baseChange b).map D.componentHom).hom.hom ≫
          ((baseChange b).map D.fullHom).hom.hom))
    apply (cancel_mono ((baseChange b).map f).hom.hom).mp
    rw [← baseChangeSectionHom_naturality]
    change baseChangeSectionHom b M.group (rationalPoints.map f zC) = _
    rw [hzCx]
    exact hyCx.symm
  let N : IntegralModel R K ((baseChange b).obj D.componentGroup) :=
    { group := D.componentGroup
      affine := inferInstance
      flat := inferInstance
      finiteType := inferInstance
      genericIso := Iso.refl _ }
  have hrepC := (Dynamic.Affine.isRepresentedBy_unipotentHom χC).baseChange b
  rw [← Dynamic.unipotent_baseChange] at hrepC
  have hyCrange : yC ∈
      (SubgroupFunctor.range ((baseChange b).map
        (Dynamic.Affine.unipotentHom χC))).carrier (Over.mk (𝟙 _)) := by
    rw [hrepC.2]
    exact hyC
  obtain ⟨yU, hyU⟩ := SubgroupFunctor.mem_range.mp hyCrange
  have hxyU : N.integralPointMap zC =
      rationalPoints.map (N.genericHom (Dynamic.Affine.unipotentHom χC)) yU := by
    change baseChangeSectionHom b D.componentGroup zC =
      yU ≫ ((baseChange b).map (Dynamic.Affine.unipotentHom χC)).hom.hom
    rw [hzCK]
    exact hyU.symm
  obtain ⟨zU, hzU, -⟩ := N.exists_eq_of_integralPointMap_eq
    (Dynamic.Affine.unipotentHom χC)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χC) zC yU hxyU
  refine ⟨zU, ?_⟩
  change (zU ≫ (Dynamic.Affine.unipotentHom χC).hom.hom) ≫ f.hom.hom = x
  rw [show zU ≫ (Dynamic.Affine.unipotentHom χC).hom.hom = zC from hzU]
  exact hzCx

/-- Choose an actual integral dynamic lift with its exact ambient equation. -/
def integralRootUnipotentLift (hpos : 0 < latticePairing T a ν)
    (x : M.integralSections)
    (hx : baseChangeSectionHom (Spec.algebraMap R K) M.group x ∈
      (RelativeRoot.subgroup ((baseChange (Spec.algebraMap R K)).map i)
        (characterLattice.baseChange (Spec.algebraMap R K) T a)).carrier
          (Over.mk (𝟙 _))) :
    {y : rationalPoints (Dynamic.Affine.unipotentScheme χC) //
      rationalPoints.map
        (Dynamic.Affine.unipotentHom χC ≫ D.componentHom ≫ D.fullHom) y = x} :=
  ⟨Classical.choose (D.exists_integralRootUnipotentLift hT ν hpos x hx),
    Classical.choose_spec (D.exists_integralRootUnipotentLift hT ν hpos x hx)⟩

end Langlands.GroupScheme.IntegralModel.KernelCentralizerData
