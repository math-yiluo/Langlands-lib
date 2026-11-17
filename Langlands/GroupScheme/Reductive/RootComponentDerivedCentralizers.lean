import Langlands.GroupScheme.Reductive.RootComponentTorusProduct
import Langlands.GroupScheme.Reductive.SimplyConnectedCentralizerDerived

/-! # Relative derived complementary centralizers from component coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Actual reductive centralizer and relative derived subgroup for a split
torus map over an affine base, without a simple-connectedness hypothesis. -/
structure RelativeCentralizerDerivedModel {R : CommRingCat.{u}}
    {G : GroupScheme (Spec R)} {T : CommGroupScheme (Spec R)} (a : T.toGrp ⟶ G) where
  centralizer : GroupScheme (Spec R)
  inclusion : centralizer ⟶ G
  closed : IsClosedSubgroup inclusion
  represents : (torusCentralizer a).IsRepresentedBy inclusion
  reductive : IsReductive centralizer
  derivedGroup : GroupScheme (Spec R)
  derivedInclusion : derivedGroup ⟶ centralizer
  admissible : RelativeDerived.IsAdmissible derivedInclusion

namespace RelativeCentralizerDerivedModel

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {T : CommGroupScheme (Spec R)} {a : T.toGrp ⟶ G}
    (C : RelativeCentralizerDerivedModel a)

/-- The derived subgroup's actual ambient inclusion. -/
def ambientInclusion : C.derivedGroup ⟶ G := C.derivedInclusion ≫ C.inclusion

/-- The relative derived centralizer is closed in the ambient group. -/
theorem ambientInclusion_closed : IsClosedSubgroup C.ambientInclusion :=
  C.admissible.1.comp C.closed

/-- The relative derived centralizer is reductive over the original base. -/
theorem isReductive : IsReductive C.derivedGroup := C.admissible.2.2.1

/-- The relative derived inclusion is the full actual derived subgroup on
every specified field-valued fibre. -/
theorem isDerivedSubgroup_fieldFiber {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec R) :
    IsDerivedSubgroup ((baseChange b).map C.derivedInclusion) := by
  obtain ⟨Q, q, hQ, hq⟩ := C.admissible.2.2.2.2
  exact isDerivedSubgroup_fieldFiber_of_semisimple_torusQuotient C.derivedInclusion
    C.admissible.1 C.isReductive C.admissible.2.2.2.1 q hQ hq b

/-- Closed split-subtorus centralizers retain simply connected derived
geometric fibres when the ambient geometric fibres are simply connected. -/
theorem isFibrewiseSimplyConnected (hT : IsSplitTorus T.toGrp)
    (ha : IsClosedSubgroup a) (hsc : IsFibrewiseSimplyConnected G) :
    IsFibrewiseSimplyConnected C.derivedGroup :=
  isFibrewiseSimplyConnected_relativeDerived_splitCentralizer a hT C.inclusion
    C.represents hsc ha C.derivedInclusion C.admissible

end RelativeCentralizerDerivedModel

/-- Construct relative centralizer-derived data for any split torus map in a
reductive group over an affine base. -/
def relativeCentralizerDerivedModel {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) (hG : IsReductive G)
    (T : CommGroupScheme (Spec R)) (a : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) : RelativeCentralizerDerivedModel a := by
  classical
  apply Classical.choice
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, j, hjc, hCs, hj⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing a hT hG.smooth
  have hC : IsReductive C :=
    isReductive_splitTorusCentralizer_overRing a hT j hj hG hjc hCs
  obtain ⟨D, d, hd⟩ :=
    relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect
      relativeSemisimpleFppfPerfect (Spec R) C hC
  exact ⟨⟨C, j, hjc, hj, hC, D, d, hd⟩⟩

namespace RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

local instance : DecidableEq M.coordinates := Classical.decEq _
local instance (c : Component M.basis) : DecidableEq (D.Complement c) := Classical.decEq _

local instance (c : Component M.basis) : Fintype (D.Complement c) :=
  Fintype.ofFinite (D.Complement c)

/-- The actual complementary split torus over any scheme. -/
abbrev complementTorus (S : Scheme.{u}) (c : Component M.basis) : CommGroupScheme S :=
  splitTorus.commGroupScheme S (D.Complement c)

/-- Complementary character restriction defines an actual torus inclusion. -/
def complementTorusInclusion (S : Scheme.{u}) (c : Component M.basis) :
    D.complementTorus S c ⟶ splitTorus.commGroupScheme S M.coordinates :=
  splitTorus.exponentHom S (D.Complement c) M.coordinates (D.restriction c)

/-- Character extension by zero defines a retraction of that torus inclusion. -/
def complementTorusRetraction (S : Scheme.{u}) (c : Component M.basis) :
    splitTorus.commGroupScheme S M.coordinates ⟶ D.complementTorus S c :=
  splitTorus.exponentHom S M.coordinates (D.Complement c) (D.extension c)

/-- The explicit integral right inverse is an actual retraction. -/
theorem complementTorusInclusion_retraction (S : Scheme.{u}) (c : Component M.basis) :
    D.complementTorusInclusion S c ≫ D.complementTorusRetraction S c = 𝟙 _ := by
  rw [complementTorusInclusion, complementTorusRetraction, splitTorus.exponentHom_comp,
    D.restriction_comp_extension, splitTorus.exponentHom_id]

/-- The group-homomorphism form of the complementary torus inclusion. -/
def complementGroupInclusion (S : Scheme.{u}) (c : Component M.basis) :
    (D.complementTorus S c).toGrp ⟶ splitTorus S M.coordinates :=
  CommGroupScheme.groupHom (D.complementTorusInclusion S c)

/-- Every complementary torus is closed in the full coordinate torus. -/
theorem complementGroupInclusion_closed (S : Scheme.{u}) (c : Component M.basis) :
    IsClosedSubgroup (D.complementGroupInclusion S c) := by
  let sigma := D.complementGroupInclusion S c
  let q := CommGroupScheme.groupHom (D.complementTorusRetraction S c)
  have he : sigma ≫ q = 𝟙 _ :=
    congrArg CommGroupScheme.groupHom (D.complementTorusInclusion_retraction S c)
  let : IsAffineHom (splitTorus S M.coordinates).X.hom := isAffineHom_splitTorus S M.coordinates
  have : IsSeparated q.hom.hom.left := by
    have : IsSeparated (q.hom.hom.left ≫ (D.complementTorus S c).toGrp.X.hom) := by
      rw [Over.w]
      infer_instance
    exact IsSeparated.of_comp _ (D.complementTorus S c).toGrp.X.hom
  have : IsClosedImmersion (sigma.hom.hom.left ≫ q.hom.hom.left) := by
    have h : sigma.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, he]
      rfl
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ q.hom.hom.left

/-- The complementary torus inclusion in the original group over its base. -/
def complementAmbient (c : Component M.basis) :
    (D.complementTorus M.base c).toGrp ⟶ M.group :=
  D.complementGroupInclusion M.base c ≫ M.inclusion

/-- The complementary torus is closed in the original group. -/
theorem complementAmbient_closed (c : Component M.basis) :
    IsClosedSubgroup (D.complementAmbient c) :=
  (D.complementGroupInclusion_closed M.base c).comp M.closed

/-- The actual relative centralizer and its derived subgroup for a component. -/
def relativeComponentModel (c : Component M.basis) :
    RelativeCentralizerDerivedModel (D.complementAmbient c) :=
  relativeCentralizerDerivedModel M.group M.reductive (D.complementTorus M.base c)
    (D.complementAmbient c) (isSplitTorus_splitTorus (D.Complement c))

/-- The actual candidate relative group for one component. -/
abbrev componentDerivedGroup (c : Component M.basis) : GroupScheme M.base :=
  (D.relativeComponentModel c).derivedGroup

/-- Its actual closed ambient inclusion. -/
def componentDerivedInclusion (c : Component M.basis) : D.componentDerivedGroup c ⟶ M.group :=
  (D.relativeComponentModel c).ambientInclusion

/-- The candidate component group is reductive over the original affine base. -/
theorem componentDerivedGroup_reductive (c : Component M.basis) :
    IsReductive (D.componentDerivedGroup c) := (D.relativeComponentModel c).isReductive

/-- The candidate component group's inclusion is closed. -/
theorem componentDerivedInclusion_closed (c : Component M.basis) :
    IsClosedSubgroup (D.componentDerivedInclusion c) :=
  (D.relativeComponentModel c).ambientInclusion_closed

/-- Simply connected ambient geometric fibres give simply connected
geometric fibres of all the candidate component groups. -/
theorem componentDerivedGroup_simplyConnected (hsc : IsFibrewiseSimplyConnected M.group)
    (c : Component M.basis) : IsFibrewiseSimplyConnected (D.componentDerivedGroup c) :=
  (D.relativeComponentModel c).isFibrewiseSimplyConnected
    (isSplitTorus_splitTorus (D.Complement c)) (D.complementAmbient_closed c) hsc

/-- The full coordinate torus factors through the complementary centralizer. -/
def relativeComponentTorus (c : Component M.basis) :
    splitTorus M.base M.coordinates ⟶ (D.relativeComponentModel c).centralizer :=
  (D.relativeComponentModel c).represents.factorHom M.inclusion
    (range_le_torusCentralizer_of_factor
      (A := D.complementTorus M.base c)
      (B := splitTorus.commGroupScheme M.base M.coordinates)
      (D.complementAmbient c) M.inclusion (D.complementGroupInclusion M.base c) rfl)

/-- The factored full torus has the original inclusion as its composite. -/
theorem relativeComponentTorus_comp (c : Component M.basis) :
    D.relativeComponentTorus c ≫ (D.relativeComponentModel c).inclusion = M.inclusion :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The full coordinate torus remains closed in the complementary centralizer. -/
theorem relativeComponentTorus_closed (c : Component M.basis) :
    IsClosedSubgroup (D.relativeComponentTorus c) :=
  IsClosedSubgroup.of_comp (D.relativeComponentModel c).closed
    (by rw [D.relativeComponentTorus_comp]; exact M.closed)

/-- The full coordinate torus is fibrewise maximal in that centralizer. -/
theorem relativeComponentTorus_maximal (c : Component M.basis) :
    IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme M.base M.coordinates) (D.relativeComponentTorus c) := by
  intro s
  apply IsMaximalTorus.of_comp ((D.relativeComponentModel c).closed.baseChange _)
  rw [← Functor.map_comp, D.relativeComponentTorus_comp]
  exact M.maximal s

/-- Complementary coordinate inclusions commute with arbitrary base change,
with the actual normalized split-torus identifications. -/
theorem complementGroupInclusion_baseChange {S S' : Scheme.{u}} (q : S' ⟶ S)
    (c : Component M.basis) :
    (splitTorus.baseChangeIso q (D.Complement c)).hom ≫ D.complementGroupInclusion S' c =
      (baseChange q).map (D.complementGroupInclusion S c) ≫
        (splitTorus.baseChangeIso q M.coordinates).hom :=
  congrArg CommGroupScheme.groupHom
    (splitTorus.exponentHom_baseChange S (D.Complement c) M.coordinates q (D.restriction c))

end RootComponentCoordinates

end Langlands.GroupScheme
