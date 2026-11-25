import Langlands.GroupScheme.Reductive.RootComponentDerivedCentralizers
import Langlands.GroupScheme.Reductive.RootComponentAlmostSimple
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerProof
import Langlands.GroupScheme.SubgroupFunctor.FppfProductSolvable
import Langlands.GroupScheme.SubgroupFunctor.FppfProductTrivial
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProduct
import Langlands.GroupScheme.Derived.SplitTorusTransport
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorGaloisAction

/-! # Actual field comparison of component derived centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A closed normal semisimple subgroup containing every root group of a
connected reductive group is exactly its full derived subgroup. -/
theorem isDerivedSubgroup_of_semisimple_of_contains_rootGroups
    {k : Type u} [Field k] [IsAlgClosed k]
    {C H : GroupScheme (Spec (CommRingCat.of k))}
    (hC : IsConnectedReductive C) (hH : IsSemisimple H)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (t : T.toGrp ⟶ C) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (n : H ⟶ C) (hnc : IsClosedSubgroup n) (hn : (SubgroupFunctor.range n).IsNormal)
    (hroots : letI := hC.isAffineHom
      ∀ a ∈ relativeRoots t, RelativeRoot.subgroup t a ≤ SubgroupFunctor.range n) :
    IsDerivedSubgroup n := by
  let : Smooth C.X.hom := hC.smooth
  let : IsAffineHom C.X.hom := hC.isAffineHom
  let : ConnectedSpace C.X.left := hC.connectedSpace
  let : Smooth H.X.hom := hH.isConnectedReductive.smooth
  let : ConnectedSpace H.X.left := hH.isConnectedReductive.connectedSpace
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  let : IsClosedImmersion n.hom.hom.left := hnc
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  obtain ⟨P, p, hp, _, _⟩ :=
    SmoothConnectedNormalFactorProduct.exists_isFppfProduct t n ht.2.1 hnc hn
  have hfull : SubgroupFunctor.range p = ⊤ :=
    range_eq_top_of_selfCentralizing_torus_and_rootSubgroups t hT
      (algClosedMaximalTorusCentralizer k C hC T t ht) p hp.isClosedSubgroup
      hp.left_le (fun a ha => (hroots a ha).trans hp.right_le)
  apply isDerivedSubgroup_of_perfect_of_containsCommutators n hnc (semisimplePerfect k H hH)
  intro U x y
  have hloc (z : U ⟶ C.X) : SubgroupFunctor.FppfLocallyInProduct
      (SubgroupFunctor.range n) (SubgroupFunctor.range t) z :=
    ((hp.mem_range_iff U z).mp (by rw [hfull]; trivial)).swap_of_isNormal_right hn
  have hcomm := SubgroupFunctor.FppfLocallyInProduct.commutator hn (C := ⊥)
    (hloc x) (hloc y) (by
      intro V b b' hb hb'
      obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hb
      obtain ⟨z', rfl⟩ := SubgroupFunctor.mem_range.mp hb'
      change ⁅z ≫ t.hom.hom, z' ≫ t.hom.hom⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr
        ((Commute.all z z').map (SubgroupFunctor.postcompHom t V)))
  exact (SubgroupFunctor.FppfLocallyInProduct.range_bot_iff n).mp hcomm

namespace RootComponentCoordinates

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

variable {M : AffinePinnedModel.{u}} (D : RootComponentCoordinates M)

local instance : Smooth M.group.X.hom := M.reductive.smooth
local instance (c : Component M.basis) : Fintype (D.Complement c) := Fintype.ofFinite _
local instance (c : Component M.basis) : IsAffineHom (D.relativeComponentModel c).centralizer.X.hom :=
  (D.relativeComponentModel c).reductive.isAffineHom
local instance (c : Component M.basis) : Smooth (D.relativeComponentModel c).centralizer.X.hom :=
  (D.relativeComponentModel c).reductive.smooth

variable (c : Component M.basis) (k : Type u) [Field k] [Algebra M.ring k]

/-- The actual normalized full torus of the complementary centralizer fibre. -/
def fieldComponentTorus : splitTorus (Spec (CommRingCat.of k)) M.coordinates ⟶
    (baseChange (algebraBaseMap M.ring k)).obj (D.relativeComponentModel c).centralizer :=
  splitTorus.baseChangeHom (K := k) (D.relativeComponentModel c).centralizer M.coordinates
    (D.relativeComponentTorus c)

/-- The normalized full torus has the original actual ambient inclusion. -/
theorem fieldComponentTorus_comp : D.fieldComponentTorus c k ≫
    (baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion =
      D.fieldTorusInclusion k := by
  change ((splitTorus.baseChangeIso _ _).inv ≫ _) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp, D.relativeComponentTorus_comp]
  rfl

/-- The actual normalized complementary torus is represented by the pulled
back relative centralizer, using the canonical split-torus identifications. -/
theorem fieldComponentCentralizer_represents :
    (torusCentralizer
      (T := D.complementTorus (Spec (CommRingCat.of k)) c)
      (splitTorus.baseChangeHom (K := k) M.group (D.Complement c)
        (D.complementAmbient c))).IsRepresentedBy
      ((baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion) := by
  have h := (D.relativeComponentModel c).represents.baseChange (algebraBaseMap M.ring k)
  rw [← torusCentralizer_baseChange] at h
  rw [torusCentralizer_eq_centralizer_range] at h
  have hr := SubgroupFunctor.range_iso_comp
    (splitTorus.baseChangeIso (algebraBaseMap M.ring k) (D.Complement c)).symm
    ((baseChange (algebraBaseMap M.ring k)).map (D.complementAmbient c))
  simp only [Iso.symm_hom] at hr
  rw [splitTorus.baseChangeHom, torusCentralizer_eq_centralizer_range, hr]
  exact h

/-- The actual complementary subtorus factors through the normalized full
torus by the original integral restriction map. -/
theorem fieldComponentComplement_factor :
    D.complementGroupInclusion (Spec (CommRingCat.of k)) c ≫ D.fieldTorusInclusion k =
      splitTorus.baseChangeHom (K := k) M.group (D.Complement c) (D.complementAmbient c) := by
  let q := algebraBaseMap M.ring k
  let e := splitTorus.baseChangeIso q (D.Complement c)
  let f := splitTorus.baseChangeIso q M.coordinates
  have he := D.complementGroupInclusion_baseChange q c
  change e.hom ≫ _ = _ ≫ f.hom at he
  have hf := congrArg (fun z => e.inv ≫ z ≫ f.inv) he
  have hf' : D.complementGroupInclusion (Spec (CommRingCat.of k)) c ≫ f.inv =
      e.inv ≫ (baseChange q).map (D.complementGroupInclusion M.base c) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hf
  change _ ≫ (f.inv ≫ (baseChange q).map M.inclusion) =
    e.inv ≫ (baseChange q).map (D.complementAmbient c)
  rw [← Category.assoc, hf', Category.assoc, ← Functor.map_comp]
  rfl

/-- Pullback of any constant exponent character is the supplied integral
complementary restriction. -/
theorem complementTorusInclusion_comp_character (S : Scheme.{u}) (x : M.coordinates → ℤ) :
    D.complementTorusInclusion S c ≫ splitTorus.exponentCharacter S M.coordinates x =
      splitTorus.exponentCharacter S (D.Complement c) (D.restriction c x) := by
  classical
  exact splitTorus.exponentHom_comp_exponentCharacter S (D.Complement c) M.coordinates
    (D.restriction c) x

local instance : IsAffineHom ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
  (M.reductive.isConnectedReductive_algebraMap k).isAffineHom
local instance : Smooth ((baseChange (algebraBaseMap M.ring k)).obj M.group).X.hom :=
  (M.reductive.isConnectedReductive_algebraMap k).smooth
local instance : IsAffineHom
    ((baseChange (algebraBaseMap M.ring k)).obj (D.relativeComponentModel c).centralizer).X.hom :=
  ((D.relativeComponentModel c).reductive.isConnectedReductive_algebraMap k).isAffineHom
local instance : Smooth
    ((baseChange (algebraBaseMap M.ring k)).obj (D.relativeComponentModel c).centralizer).X.hom :=
  ((D.relativeComponentModel c).reductive.isConnectedReductive_algebraMap k).smooth

/-- The centralizer's roots are exactly the ambient roots trivial on the
complementary split torus. -/
theorem fieldComponentCentralizer_roots_restrict :
    relativeRoots (D.fieldComponentTorus c k) =
      {a | a ∈ relativeRoots (D.fieldTorusInclusion k) ∧
        D.complementTorusInclusion (Spec (CommRingCat.of k)) c ≫ a = 0} :=
  relativeRoots_splitTorusCentralizer_factor
    (G := (baseChange (algebraBaseMap M.ring k)).obj M.group)
    (M := (baseChange (algebraBaseMap M.ring k)).obj (D.relativeComponentModel c).centralizer)
    (A := D.complementTorus (Spec (CommRingCat.of k)) c)
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (splitTorus.baseChangeHom (K := k) M.group (D.Complement c) (D.complementAmbient c))
    (isSplitTorus_splitTorus (D.Complement c)) (D.fieldTorusInclusion k)
    (D.fieldComponentTorus c k)
    ((baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion)
    (D.fieldComponentCentralizer_represents c k) (D.fieldComponentTorus_comp c k)
    (D.complementTorusInclusion (Spec (CommRingCat.of k)) c) (D.fieldComponentComplement_factor c k)

/-- A constant root belongs to the centralizer exactly in its own selected
Cartan component. -/
theorem mem_fieldComponentCentralizer_roots_iff (r : M.rootIndex) :
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
      (M.rootDatum.root r) ∈ relativeRoots (D.fieldComponentTorus c k) ↔ D.rootComponent r = c := by
  have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) M.coordinates
      (M.rootDatum.root r) ∈ relativeRoots (D.fieldTorusInclusion k) :=
    D.componentRoots_subset k (D.rootComponent r) ⟨r, rfl, rfl⟩
  rw [D.fieldComponentCentralizer_roots_restrict c k]
  change (_ ∧ _) ↔ _
  rw [and_iff_right hroot, D.complementTorusInclusion_comp_character,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  have hz : (splitTorus.characterLatticeEquiv k (D.Complement c)).symm
      (D.restriction c (M.rootDatum.root r)) = 0 ↔ D.restriction c (M.rootDatum.root r) = 0 := by
    constructor
    · exact fun h => (splitTorus.characterLatticeEquiv k (D.Complement c)).symm.injective
        (h.trans (AddEquiv.map_zero _).symm)
    · exact fun h => by rw [h, AddEquiv.map_zero]
  exact hz.trans (D.restriction_root_eq_zero_iff c r)

/-- The actual centralizer root set is exactly the constant selected
component of the original actual field roots. -/
theorem fieldComponentCentralizer_roots :
    relativeRoots (D.fieldComponentTorus c k) = D.componentRoots k c := by
  ext alpha
  constructor
  · intro halpha
    have h := (D.fieldComponentCentralizer_roots_restrict c k).le halpha
    rw [relativeRoots_eq_roots, ← (M.fibrewiseRootDatum.field k).2.1] at h
    obtain ⟨r, hr⟩ := h.1
    rw [CoordinateRootDatum.fieldRealization_root] at hr
    subst alpha
    exact ⟨r, (D.mem_fieldComponentCentralizer_roots_iff c k r).mp halpha, rfl⟩
  · rintro ⟨r, hrc, rfl⟩
    exact (D.mem_fieldComponentCentralizer_roots_iff c k r).mpr hrc


/-- Every selected ambient root group lies in the actual complementary-torus
centralizer, on every field scheme test. -/
theorem selected_rootSubgroup_le_fieldComponentCentralizer
    {alpha : characterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)}
    (halpha : alpha ∈ D.componentRoots k c) :
    RelativeRoot.subgroup (D.fieldTorusInclusion k) alpha ≤
      SubgroupFunctor.range
        ((baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion) := by
  let T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates
  let A := D.complementTorus (Spec (CommRingCat.of k)) c
  let i : T.toGrp ⟶ _ := D.fieldTorusInclusion k
  let a : A.toGrp ⟶ _ :=
    splitTorus.baseChangeHom (K := k) M.group (D.Complement c) (D.complementAmbient c)
  let f : A ⟶ T := D.complementTorusInclusion (Spec (CommRingCat.of k)) c
  have hA : IsSplitTorus A.toGrp := isSplitTorus_splitTorus (D.Complement c)
  have hfactor : CommGroupScheme.groupHom f ≫ i = a := D.fieldComponentComplement_factor c k
  have hzero : f ≫ alpha = 0 := by
    have hmem : alpha ∈ relativeRoots (D.fieldComponentTorus c k) :=
      (D.fieldComponentCentralizer_roots c k).symm ▸ halpha
    exact ((D.fieldComponentCentralizer_roots_restrict c k).le hmem).2
  let nu : cocharacterLattice T := centralizingCocharacter hA a ≫ f
  have hnu : CommGroupScheme.groupHom nu ≫ i =
      CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫ a := by
    change (CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫
      CommGroupScheme.groupHom f) ≫ i = _
    rw [Category.assoc, hfactor]
  rw [(D.fieldComponentCentralizer_represents c k).2,
    ← centralizingCocharacter_spec hA a, ← hnu]
  apply RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i alpha nu
  simp only [latticePairing_apply, nu, Category.assoc, hzero, Limits.comp_zero, AddEquiv.map_zero]

/-- The group generated by the component roots has an actual factorization
through the corresponding centralizer fibre. -/
def fieldComponentGeneratedLift
    (N : RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c)) :
    N.group ⟶ (baseChange (algebraBaseMap M.ring k)).obj
      (D.relativeComponentModel c).centralizer :=
  (D.fieldComponentCentralizer_represents c k).factorHom N.inclusion (by
    rw [← (D.fieldComponentCentralizer_represents c k).2]
    exact N.minimal _ _ ((D.relativeComponentModel c).closed.baseChange _) (fun alpha halpha =>
      D.selected_rootSubgroup_le_fieldComponentCentralizer c k halpha))

/-- The lifted root-generated inclusion has exactly its original ambient map. -/
theorem fieldComponentGeneratedLift_comp
    (N : RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c)) :
    D.fieldComponentGeneratedLift c k N ≫
      (baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion =
        N.inclusion :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The root-generated component group is the full actual derived subgroup
of its complementary-torus centralizer fibre. -/
theorem fieldComponentGeneratedLift_isDerived [IsAlgClosed k]
    (N : RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c)) :
    IsDerivedSubgroup (D.fieldComponentGeneratedLift c k N) := by
  let C := (baseChange (algebraBaseMap M.ring k)).obj (D.relativeComponentModel c).centralizer
  let j : C ⟶ _ :=
    (baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).inclusion
  let n : N.group ⟶ C := D.fieldComponentGeneratedLift c k N
  have hj : IsClosedSubgroup j := (D.relativeComponentModel c).closed.baseChange _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hcomp : n ≫ j = N.inclusion := D.fieldComponentGeneratedLift_comp c k N
  have hn : IsClosedSubgroup n := IsClosedSubgroup.of_comp hj (by rw [hcomp]; exact N.closed)
  have hnormal : (SubgroupFunctor.range n).IsNormal :=
    SubgroupFunctor.isNormal_range_of_mono_comp n j (by rw [hcomp]; exact N.normal)
  have hmax := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise
    M.coordinates (D.relativeComponentModel c).centralizer (D.relativeComponentTorus c)
    (D.relativeComponentTorus_maximal c) k
  apply isDerivedSubgroup_of_semisimple_of_contains_rootGroups
    ((D.relativeComponentModel c).reductive.isConnectedReductive_algebraMap k)
    N.semisimple (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
    (D.fieldComponentTorus c k) (isSplitTorus_splitTorus M.coordinates) hmax n hn hnormal
  intro alpha halpha U x hx
  have hselected : alpha ∈ D.componentRoots k c :=
    (D.fieldComponentCentralizer_roots c k).le halpha
  have hxambient : x ≫ j.hom.hom ∈
      (RelativeRoot.subgroup (D.fieldTorusInclusion k) alpha).carrier U := by
    have h := RelativeRoot.comp_mem_subgroup
      (S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldComponentTorus c k) alpha j hx
    rwa [D.fieldComponentTorus_comp c k] at h
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (N.contains alpha hselected U hxambient)
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y, (cancel_mono j.hom.hom).mp ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hcomp]
  exact hy

/-- The actual component-generated field group is isomorphic to the field
fibre of the relative derived centralizer, compatibly with ambient inclusions. -/
def fieldComponentDerivedIso [IsAlgClosed k]
    (N : RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c)) :
    N.group ≅ (baseChange (algebraBaseMap M.ring k)).obj (D.componentDerivedGroup c) :=
  (D.fieldComponentGeneratedLift_isDerived c k N).iso
    ((D.relativeComponentModel c).isDerivedSubgroup_fieldFiber (algebraBaseMap M.ring k))

/-- The comparison isomorphism intertwines the actual ambient inclusions. -/
theorem fieldComponentDerivedIso_hom_comp [IsAlgClosed k]
    (N : RootPartitionNormalModel
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) M.coordinates)
      (D.fieldTorusInclusion k) (D.componentRoots k c)) :
    (D.fieldComponentDerivedIso c k N).hom ≫
      (baseChange (algebraBaseMap M.ring k)).map (D.componentDerivedInclusion c) = N.inclusion := by
  change _ ≫ (baseChange _).map
    ((D.relativeComponentModel c).derivedInclusion ≫ (D.relativeComponentModel c).inclusion) = _
  rw [Functor.map_comp, ← Category.assoc]
  rw [show (D.fieldComponentDerivedIso c k N).hom ≫
      (baseChange (algebraBaseMap M.ring k)).map (D.relativeComponentModel c).derivedInclusion =
      D.fieldComponentGeneratedLift c k N from IsDerivedSubgroup.iso_hom_comp _ _]
  exact D.fieldComponentGeneratedLift_comp c k N

/-- Every relative candidate component has almost-simple field fibre over
an algebraically closed field whenever the original field fibre is semisimple. -/
theorem componentDerivedGroup_isAlmostSimple_field [IsAlgClosed k]
    (hG : IsSemisimple ((baseChange (algebraBaseMap M.ring k)).obj M.group)) :
    IsAlmostSimple ((baseChange (algebraBaseMap M.ring k)).obj (D.componentDerivedGroup c)) :=
  IsAlmostSimple.of_iso
    (D.fieldComponentDerivedIso c k (D.fieldComponentNormalModel k hG c)).symm
    (D.fieldComponentNormalModel_isAlmostSimple k hG c)

/-- Semisimple ambient geometric fibres give almost-simple geometric fibres
for every actual relative derived component. -/
theorem componentDerivedGroup_isAlmostSimple_geometric
    (hss : ∀ s : M.base, IsSemisimple (geometricFiber M.group s)) (s : M.base) :
    IsAlmostSimple (geometricFiber (D.componentDerivedGroup c) s) := by
  let k := AlgebraicClosure (M.base.residueField s)
  let b := geometricPoint M.base s
  let : Algebra M.ring k := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap M.ring k = b := Spec.map_preimage b
  have hfield := D.componentDerivedGroup_isAlmostSimple_field c k
    (show IsSemisimple ((baseChange (algebraBaseMap M.ring k)).obj M.group) from by
      rw [hb]
      exact hss s)
  rw [hb] at hfield
  exact hfield

end RootComponentCoordinates

end Langlands.GroupScheme
