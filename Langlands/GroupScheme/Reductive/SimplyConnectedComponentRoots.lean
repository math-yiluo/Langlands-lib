import Langlands.GroupScheme.Reductive.SimplyConnectedComponentCentralizers
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel

/-! # Actual field roots of complementary-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedCorootSubtori

variable {I J : Type u} [Fintype I]
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
  (hspan : P.corootSpan ℤ = ⊤) (s : Set b.support)

/-- Selected simple-coroot inclusions commute with arbitrary base change,
using the actual canonical source and target split-torus isomorphisms. -/
theorem inclusion_baseChange {S S' : Scheme.{u}} (q : S' ⟶ S) :
    (splitTorus.baseChangeIso q s).hom ≫
        CommGroupScheme.groupHom (inclusion P b hspan s S') =
      (baseChange q).map (CommGroupScheme.groupHom (inclusion P b hspan s S)) ≫
        (splitTorus.baseChangeIso q I).hom := by
  classical
  let : Fintype s := Fintype.ofFinite s
  exact congrArg CommGroupScheme.groupHom
    (splitTorus.exponentHom_baseChange S s I q (restriction P b hspan s))

end SimplyConnectedCorootSubtori

namespace AffineSimplyConnectedPinnedModel

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable (M : AffineSimplyConnectedPinnedModel.{u})

local instance : CommRing M.ring := M.toAffinePinnedModel.commRing
local instance : Fintype M.coordinates := M.toAffinePinnedModel.fintypeCoordinates
local instance : Fintype M.rootIndex := M.toAffinePinnedModel.fintypeRoots
private local instance : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced
local instance (c : M.Component) : Fintype (M.Complement c) :=
  Fintype.ofFinite (M.Complement c)
local instance : IsAffineHom M.group.X.hom := M.reductive.isAffineHom
local instance : Smooth M.group.X.hom := M.reductive.smooth
local instance (c : M.Component) : IsAffineHom (M.componentCentralizer c).centralizer.X.hom :=
  (M.componentCentralizer c).reductive.isAffineHom
local instance (c : M.Component) : Smooth (M.componentCentralizer c).centralizer.X.hom :=
  (M.componentCentralizer c).reductive.smooth

variable (c : M.Component) (k : Type u) [Field k] [Algebra M.ring k]

/-- The actual full coordinate maximal torus of the specified field fibre
of the complementary centralizer. -/
def fieldCentralizerTorus :
    splitTorus (Spec (CommRingCat.of k)) M.coordinates ⟶
      (baseChange (algebraBaseMap M.ring k)).obj (M.componentCentralizer c).centralizer :=
  splitTorus.baseChangeHom (K := k) (M.componentCentralizer c).centralizer M.coordinates
    (M.centralizerTorusInclusion c)

/-- Its composite is the original actual coordinate torus on that field fibre. -/
theorem fieldCentralizerTorus_comp :
    M.fieldCentralizerTorus c k ≫
        (baseChange (algebraBaseMap M.ring k)).map (M.componentCentralizer c).inclusion =
      splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion := by
  change ((splitTorus.baseChangeIso _ _).inv ≫ _) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp, M.centralizerTorusInclusion_comp]
  rfl

/-- The field fibre represents the centralizer of the actual normalized
complementary torus on that field. -/
theorem fieldCentralizer_represents :
    (torusCentralizer
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (M.Complement c))
      (splitTorus.baseChangeHom (K := k) M.group (M.Complement c)
        (M.complementAmbient c))).IsRepresentedBy
      ((baseChange (algebraBaseMap M.ring k)).map (M.componentCentralizer c).inclusion) := by
  have h := (M.componentCentralizer c).represents.baseChange (algebraBaseMap M.ring k)
  rw [← torusCentralizer_baseChange] at h
  rw [torusCentralizer_eq_centralizer_range] at h
  have hr := SubgroupFunctor.range_iso_comp
    (splitTorus.baseChangeIso (algebraBaseMap M.ring k) (M.Complement c)).symm
    ((baseChange (algebraBaseMap M.ring k)).map (M.complementAmbient c))
  simp only [Iso.symm_hom] at hr
  rw [splitTorus.baseChangeHom, torusCentralizer_eq_centralizer_range, hr]
  exact h

/-- The actual normalized complementary torus is the integral coroot-subtorus
map followed by the actual normalized full torus on the field fibre. -/
theorem fieldComplement_factor :
    CommGroupScheme.groupHom
        (SimplyConnectedCorootSubtori.inclusion M.rootDatum M.basis M.corootSpan_eq_top
          {i | component M.basis i ≠ c} (Spec (CommRingCat.of k))) ≫
      splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion =
        splitTorus.baseChangeHom (K := k) M.group (M.Complement c) (M.complementAmbient c) := by
  let q := algebraBaseMap M.ring k
  let e := splitTorus.baseChangeIso q (M.Complement c)
  let f := splitTorus.baseChangeIso q M.coordinates
  have he := SimplyConnectedCorootSubtori.inclusion_baseChange M.rootDatum M.basis
    M.corootSpan_eq_top {i | component M.basis i ≠ c} q
  change e.hom ≫ _ = _ ≫ f.hom at he
  have hf := congrArg (fun z => e.inv ≫ z ≫ f.inv) he
  have hf' : CommGroupScheme.groupHom
        (SimplyConnectedCorootSubtori.inclusion M.rootDatum M.basis M.corootSpan_eq_top
          {i | component M.basis i ≠ c} (Spec (CommRingCat.of k))) ≫ f.inv =
      e.inv ≫ (baseChange q).map (M.complementInclusion c) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id,
      complementInclusion] using hf
  change _ ≫ (f.inv ≫ (baseChange q).map M.inclusion) =
    e.inv ≫ (baseChange q).map (M.complementAmbient c)
  rw [← Category.assoc, hf', Category.assoc, ← Functor.map_comp]
  rfl

/-- The roots of the actual complementary centralizer are the ambient roots
whose characters restrict trivially to the complementary torus. -/
theorem fieldCentralizer_roots :
    relativeRoots (M.fieldCentralizerTorus c k) =
      {α | α ∈ relativeRoots
          (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion) ∧
        SimplyConnectedCorootSubtori.inclusion M.rootDatum M.basis M.corootSpan_eq_top
            {i | component M.basis i ≠ c} (Spec (CommRingCat.of k)) ≫ α = 0} := by
  let : IsAffineHom
      ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
    (M.reductive.isConnectedReductive_algebraMap k).isAffineHom
  let : Smooth
      ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
    (M.reductive.isConnectedReductive_algebraMap k).smooth
  let : IsAffineHom
      ((baseChange (algebraBaseMap M.ring k)).obj
        (M.componentCentralizer c).centralizer).X.hom :=
    ((M.componentCentralizer c).reductive.isConnectedReductive_algebraMap k).isAffineHom
  let : Smooth
      ((baseChange (algebraBaseMap M.ring k)).obj
        (M.componentCentralizer c).centralizer).X.hom :=
    ((M.componentCentralizer c).reductive.isConnectedReductive_algebraMap k).smooth
  exact relativeRoots_splitTorusCentralizer_factor
    (G := (baseChange (algebraBaseMap M.ring k)).obj M.group)
    (M := (baseChange (algebraBaseMap M.ring k)).obj (M.componentCentralizer c).centralizer)
    (A := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (M.Complement c))
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (splitTorus.baseChangeHom (K := k) M.group (M.Complement c) (M.complementAmbient c))
    (isSplitTorus_splitTorus (M.Complement c))
    (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion)
    (M.fieldCentralizerTorus c k)
    ((baseChange (algebraBaseMap M.ring k)).map (M.componentCentralizer c).inclusion)
    (M.fieldCentralizer_represents c k) (M.fieldCentralizerTorus_comp c k)
    (SimplyConnectedCorootSubtori.inclusion M.rootDatum M.basis M.corootSpan_eq_top
      {i | component M.basis i ≠ c} (Spec (CommRingCat.of k)))
    (M.fieldComplement_factor c k)

/-- An original root occurs in the actual centralizer fibre exactly when its
Cartan component is the selected component. -/
theorem mem_fieldCentralizer_roots_iff (r : M.rootIndex) :
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
        (M.rootDatum.root r) ∈ relativeRoots (M.fieldCentralizerTorus c k) ↔
      rootComponent M.basis M.corootSpan_eq_top r = c := by
  classical
  let : M.rootDatum.IsReduced := M.fibrewiseRootDatum.isReduced
  let : Fintype (M.Complement c) := Fintype.ofFinite (M.Complement c)
  have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
      (M.rootDatum.root r) ∈ relativeRoots
        (splitTorus.baseChangeHom (K := k) M.group M.coordinates M.inclusion) := by
    rw [relativeRoots_eq_roots, ← (M.fibrewiseRootDatum.field k).2.1]
    exact ⟨r, CoordinateRootDatum.fieldRealization_root k M.rootDatum r⟩
  rw [M.fieldCentralizer_roots c k]
  change (_ ∧ _) ↔ _
  rw [and_iff_right hroot, SimplyConnectedCorootSubtori.inclusion_comp_character,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  have hz : (fun i : M.Complement c =>
      M.rootDatum.toLinearMap (M.rootDatum.root r) (M.rootDatum.coroot i)) =
    SimplyConnectedCorootSubtori.restriction M.rootDatum M.basis M.corootSpan_eq_top
      {i | component M.basis i ≠ c} (M.rootDatum.root r) := by
    ext i
    exact (SimplyConnectedCorootSubtori.simpleCorootCoordinates_apply M.rootDatum M.basis
      M.corootSpan_eq_top (M.rootDatum.root r) i).symm
  rw [AddEquiv.map_eq_zero_iff]
  change (fun i : M.Complement c =>
    M.rootDatum.toLinearMap (M.rootDatum.root r) (M.rootDatum.coroot i)) = 0 ↔ _
  rw [hz]
  exact SimplyConnectedCorootSubtori.restriction_root_complement_eq_zero_iff
    M.rootDatum M.basis M.corootSpan_eq_top c r

end AffineSimplyConnectedPinnedModel

end Langlands.GroupScheme
