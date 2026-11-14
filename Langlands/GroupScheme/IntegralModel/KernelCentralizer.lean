import Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Rational.KernelCentralizerBaseChange
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveProof
import Langlands.GroupScheme.IdentityComponent.Transport

/-! # Integral models of full character-kernel centralizer components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeRoot

/-- The centralizer of the full character kernel in a smooth affine group
has a smooth closed representative over any integral domain. -/
theorem kernelCentralizer_hasSmoothClosedRepresentative_overRing
    {R : Type u} [CommRing R] [IsDomain R]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (hG : Smooth G.X.hom) :
    (kernelCentralizer i a).HasSmoothClosedRepresentative := by
  let e := Diagonalizable.kernelDiagonalizableIso T hT a
  have h := diagonalizableCentralizer_hasSmoothClosedRepresentative_overRing
    (e.inv ≫ characterKernelι a ≫ i) hG
  have hr : SubgroupFunctor.range (e.inv ≫ characterKernelι a ≫ i) =
      SubgroupFunctor.range (characterKernelι a ≫ i) :=
    SubgroupFunctor.range_precomp_iso e.symm (characterKernelι a ≫ i)
  rw [torusCentralizer_eq_centralizer_range, hr] at h
  rw [kernelCentralizer_eq_torusCentralizer,
    torusCentralizer_eq_centralizer_range (T := characterKernelComm a)]
  exact h

end RelativeRoot

namespace IsRelativeIdentityComponent

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyConnected H.X.hom]
    {i : H ⟶ G}

local instance : ConnectedSpace H.X.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom

/-- Over a field, a geometrically connected relative identity component
is canonically the ordinary identity component. -/
def identityComponentIso (hi : IsRelativeIdentityComponent G i) :
    H ≅ identityComponent G := by
  have : Mono i.hom.hom := hi.mono_hom
  let j := Classical.choose (hi.exists_hom_lift (identityComponentι G))
  have hj := Classical.choose_spec (hi.exists_hom_lift (identityComponentι G))
  refine
    { hom := IdentityComponent.factor G i
      inv := j
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Grp.hom_ext
    apply (cancel_mono i.hom.hom).mp
    change ((IdentityComponent.factor G i ≫ j) ≫ i).hom.hom =
      ((𝟙 H) ≫ i).hom.hom
    rw [Category.assoc, hj, IdentityComponent.factor_identityComponentι,
      Category.id_comp]
  · exact IdentityComponent.hom_ext_of_isOpenImmersion (identityComponentι G) (by
      rw [Category.assoc, IdentityComponent.factor_identityComponentι, hj,
        Category.id_comp])

@[reassoc]
theorem identityComponentIso_hom_comp (hi : IsRelativeIdentityComponent G i) :
    hi.identityComponentIso.hom ≫ identityComponentι G = i := by
  change IdentityComponent.factor G i ≫ identityComponentι G = i
  exact IdentityComponent.factor_identityComponentι G i

end IsRelativeIdentityComponent

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]

local instance : Smooth M.genericFibre.X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd M.group.X.hom
    (Spec.algebraMap R K)))

local instance : IsAffineHom M.genericFibre.X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd M.group.X.hom
    (Spec.algebraMap R K)))

variable {H : GroupScheme (Spec (CommRingCat.of R))} {i : H ⟶ M.group}
    [GeometricallyConnected H.X.hom]

local instance : GeometricallyConnected ((baseChange (Spec.algebraMap R K)).obj H).X.hom :=
  inferInstanceAs (GeometricallyConnected
    (CategoryTheory.Limits.pullback.snd H.X.hom (Spec.algebraMap R K)))

/-- The generic fibre of a relative identity component is the ordinary
identity component of the actual generic fibre of the original model. -/
def componentGenericIso (hi : IsRelativeIdentityComponent M.group i) :
    (baseChange (Spec.algebraMap R K)).obj H ≅ identityComponent M.genericFibre := by
  exact (RelativeIdentityComponent.smoothBaseChange _
    M.group (inferInstance : Smooth M.group.X.hom) H i hi _
      (Spec.algebraMap R K)).identityComponentIso

@[reassoc]
theorem componentGenericIso_hom_comp (hi : IsRelativeIdentityComponent M.group i) :
    (M.componentGenericIso hi).hom ≫ identityComponentι M.genericFibre =
      (baseChange (Spec.algebraMap R K)).map i := by
  exact (RelativeIdentityComponent.smoothBaseChange _
    M.group (inferInstance : Smooth M.group.X.hom) H i hi _
      (Spec.algebraMap R K)).identityComponentIso_hom_comp

variable [IsDiscreteValuationRing R] [Smooth H.X.hom]

/-- A smooth relative identity component over a DVR gives an integral model
of the identity component of the original generic fibre, even when that fibre
is disconnected. -/
def componentModel (hi : IsRelativeIdentityComponent M.group i) :
    IntegralModel R K (identityComponent M.genericFibre) where
  group := H
  affine := RelativeIdentityComponent.smoothDvrAffineness R M.group
    (inferInstance : Smooth M.group.X.hom) M.affine H i hi
  flat := inferInstance
  finiteType := inferInstance
  genericIso := M.componentGenericIso hi

/-- The integral component inclusion extends the specified generic inclusion
of the ordinary identity component followed by the original model isomorphism. -/
def componentInclusion (hi : IsRelativeIdentityComponent M.group i) :
    (M.componentModel hi).Hom M (identityComponentι M.genericFibre ≫ M.genericIso.hom) where
  hom := i
  generic_comm := by
    change _ ≫ M.genericIso.hom =
      (M.componentGenericIso hi).hom ≫ (identityComponentι M.genericFibre ≫ M.genericIso.hom)
    rw [← Category.assoc, componentGenericIso_hom_comp]

end IntegralModel

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The actual full character-kernel centralizer and its smooth relative
identity component inside an integral model. The full centralizer is allowed
to be disconnected. -/
structure KernelCentralizerData (M : IntegralModel R K G)
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (i : T.toGrp ⟶ M.group) (a : characterLattice T) where
  fullGroup : GroupScheme (Spec (CommRingCat.of R))
  fullHom : fullGroup ⟶ M.group
  fullClosed : IsClosedSubgroup fullHom
  fullRepresents : (RelativeRoot.kernelCentralizer i a).IsRepresentedBy fullHom
  [fullSmooth : Smooth fullGroup.X.hom]
  [fullAffine : IsAffineHom fullGroup.X.hom]
  componentGroup : GroupScheme (Spec (CommRingCat.of R))
  componentHom : componentGroup ⟶ fullGroup
  isRelativeComponent : IsRelativeIdentityComponent fullGroup componentHom
  [componentSmooth : Smooth componentGroup.X.hom]
  [componentGeometricallyConnected : GeometricallyConnected componentGroup.X.hom]

attribute [instance] KernelCentralizerData.fullSmooth KernelCentralizerData.fullAffine
  KernelCentralizerData.componentSmooth KernelCentralizerData.componentGeometricallyConnected

namespace KernelCentralizerData

variable (M : IntegralModel R K G)
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (i : T.toGrp ⟶ M.group) (a : characterLattice T)

/-- A split integral torus map in a smooth model supplies the full centralizer
and its actual relative identity component. The character need not be
primitive or nonzero, and its kernel need not be smooth. -/
theorem nonempty_of_split [Smooth M.group.X.hom] (hT : IsSplitTorus T.toGrp) :
    Nonempty (KernelCentralizerData M i a) := by
  have : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  obtain ⟨C, j, hj, hC, hrep⟩ :=
    RelativeRoot.kernelCentralizer_hasSmoothClosedRepresentative_overRing i hT a
      (inferInstance : Smooth M.group.X.hom)
  have : IsClosedImmersion j.hom.hom.left := hj
  have hAff : IsAffineHom C.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  obtain ⟨H, k, hk, hH, hgc⟩ := RelativeIdentityComponent.smoothExistence _ C hC
  exact ⟨{
    fullGroup := C
    fullHom := j
    fullClosed := hj
    fullRepresents := hrep
    fullSmooth := hC
    fullAffine := hAff
    componentGroup := H
    componentHom := k
    isRelativeComponent := hk
    componentSmooth := hH
    componentGeometricallyConnected := hgc }⟩

/-- A chosen actual centralizer-component construction from a split integral
torus map. -/
def ofSplit [Smooth M.group.X.hom] (hT : IsSplitTorus T.toGrp) :
    KernelCentralizerData M i a :=
  Classical.choice (nonempty_of_split M i a hT)

variable {M i a} (D : KernelCentralizerData M i a)

/-- The full centralizer as a model of its actual generic fibre. -/
def fullModel :
    IntegralModel R K ((baseChange (Spec.algebraMap R K)).obj D.fullGroup) where
  group := D.fullGroup
  affine := inferInstance
  flat := inferInstance
  finiteType := inferInstance
  genericIso := Iso.refl _

/-- The generic full centralizer is the full kernel centralizer of the
base-changed character, on every test scheme. -/
theorem fullGenericRepresents :
    (RelativeRoot.kernelCentralizer
      ((baseChange (Spec.algebraMap R K)).map i)
      (characterLattice.baseChange (Spec.algebraMap R K) T a)).IsRepresentedBy
        ((baseChange (Spec.algebraMap R K)).map D.fullHom) :=
  RelativeRoot.kernelCentralizer_isRepresentedBy_baseChange
    (Spec.algebraMap R K) i a D.fullRepresents

/-- The full centralizer inclusion extends its actual generic ambient map. -/
def fullInclusion :
    D.fullModel.Hom M
      ((baseChange (Spec.algebraMap R K)).map D.fullHom ≫ M.genericIso.hom) where
  hom := D.fullHom
  generic_comm := by
    change _ = (𝟙 _) ≫ _
    rw [Category.id_comp]

theorem fullInclusion_isClosed : IsClosedSubgroup D.fullInclusion.hom :=
  D.fullClosed

local instance : Smooth D.fullModel.group.X.hom := D.fullSmooth

local instance : Smooth D.fullModel.genericFibre.X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom
    (Spec.algebraMap R K)))

local instance : IsAffineHom D.fullModel.genericFibre.X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd D.fullGroup.X.hom
    (Spec.algebraMap R K)))

variable [IsDiscreteValuationRing R]

/-- The affine smooth integral model of the identity component of the
actual generic full centralizer. -/
def model : IntegralModel R K (identityComponent D.fullModel.genericFibre) :=
  D.fullModel.componentModel D.isRelativeComponent

theorem model_isSmooth : Smooth D.model.group.X.hom :=
  D.componentSmooth

theorem model_geometricallyConnected : GeometricallyConnected D.model.group.X.hom :=
  D.componentGeometricallyConnected

/-- The component model maps to the original ambient model, with the
specified generic map given by both actual inclusions. -/
def inclusion :
    D.model.Hom M
      (identityComponentι D.fullModel.genericFibre ≫
        (baseChange (Spec.algebraMap R K)).map D.fullHom ≫ M.genericIso.hom) where
  hom := D.componentHom ≫ D.fullHom
  generic_comm := by
    change (baseChange (Spec.algebraMap R K)).map
        (D.componentHom ≫ D.fullHom) ≫ M.genericIso.hom =
      (D.fullModel.componentGenericIso D.isRelativeComponent).hom ≫ _
    rw [Functor.map_comp, Category.assoc, ← Category.assoc,
      ← Category.assoc,
      componentGenericIso_hom_comp]
    rfl

omit [IsDiscreteValuationRing R] in
/-- Reductivity of the component model's generic group follows from the
published full-kernel centralizer theorem. The nonzero hypothesis concerns
the actual generic character. -/
theorem generic_isConnectedReductive (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp)
    (ha : characterLattice.baseChange (Spec.algebraMap R K) T a ≠ 0) :
    IsConnectedReductive (identityComponent D.fullModel.genericFibre) := by
  have hj := D.fullClosed.baseChange (Spec.algebraMap R K)
  exact RelativeRoot.kernelCentralizerComponentReductive K M.genericFibre
    (hG.of_iso M.genericIso) ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T)
    (IsSplitTorus.baseChange (Spec.algebraMap R K) hT)
    ((baseChange (Spec.algebraMap R K)).map i)
    (characterLattice.baseChange (Spec.algebraMap R K) T a) ha
    D.fullModel.genericFibre ((baseChange (Spec.algebraMap R K)).map D.fullHom)
    D.fullGenericRepresents hj inferInstance

end KernelCentralizerData
end IntegralModel
end Langlands.GroupScheme
