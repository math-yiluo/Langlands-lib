import Langlands.GroupScheme.Reductive.PinnedGaloisTorus
import Langlands.GroupScheme.Reductive.GeometricRootDatumComparison
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Reductive.StarAction

/-! # Effective torus solutions of pinned Galois data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut)

/-- Actual effective ambient and torus descent, retaining the torus comparison
and both compatibility equations. -/
structure GaloisTorusSolution where
  group : Solution (p.galoisDatum ρ)
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  torusIso : (CommGroupScheme.baseChange (fieldMap k K)).obj torus ≅ p.torus
  torusCompatible : Compatible (canonicalDatum (fieldMap k K) torus.toGrp)
    (p.galoisTorusDatum ρ) (CommGroupScheme.groupHom torusIso.hom)
  inclusion : torus.toGrp ⟶ group.obj
  recovery : (GroupScheme.baseChange (fieldMap k K)).map inclusion ≫ group.iso.hom =
    CommGroupScheme.groupHom torusIso.hom ≫ p.inclusion
  reductive : IsConnectedReductive group.obj
  groupAffine : IsAffine group.obj.X.left
  torusAffine : IsAffine torus.X.left

/-- Effective descent of the actual torus together with the pinned ambient group. -/
def galoisTorusSolution : GaloisTorusSolution p ρ := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective (fieldMap k K) := hsurj
  let : Flat (fieldMap k K) := hflat
  let : QuasiCompact (fieldMap k K) := hqc
  let : IsAffineHom p.torus.X.hom := p.isSplitTorus.isAffineHom
  let : IsAffine p.torus.X.left := isAffine_of_isAffineHom p.torus.X.hom
  let s := p.galoisQuasiSplitSolution ρ
  let r := (p.galoisTorusDatum ρ).affineSolution
  let T : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := r.obj
      comm := isCommMonObj_of_baseChange (fieldMap k K) r.obj
        (Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono r.iso.hom.hom.hom) }
  let t : (CommGroupScheme.baseChange (fieldMap k K)).obj T ≅ p.torus :=
    CommGroupScheme.isoOfGroupIso r.iso
  exact
    { group := s.group
      torus := T
      torusIso := t
      torusCompatible := r.compatible
      inclusion := r.descendHom s.group p.inclusion (p.compatible_galoisTorusDatum ρ)
      recovery := r.baseChange_descendHom s.group p.inclusion
        (p.compatible_galoisTorusDatum ρ)
      reductive := s.reductive
      groupAffine := s.groupAffine
      torusAffine := inferInstanceAs (IsAffine (p.galoisTorusDatum ρ).affineSolution.obj.X.left) }

namespace GaloisTorusSolution

variable {p ρ} (s : GaloisTorusSolution p ρ)

instance group_isAffineHom : IsAffineHom s.group.obj.X.hom :=
  s.reductive.isAffineHom

instance group_locallyOfFiniteType : LocallyOfFiniteType s.group.obj.X.hom := by
  let := s.reductive.smooth
  infer_instance

local instance baseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (fieldMap k K)).obj s.group.obj).X.hom := by
  change IsAffineHom (pullback.snd s.group.obj.X.hom (fieldMap k K))
  infer_instance

/-- The descended torus is split over the supplied Galois extension. -/
theorem isSplitTorus :
    IsSplitTorus ((CommGroupScheme.baseChange (fieldMap k K)).obj s.torus).toGrp :=
  IsSplitTorus.of_iso
    { hom := CommGroupScheme.groupHom s.torusIso.hom
      inv := CommGroupScheme.groupHom s.torusIso.inv
      hom_inv_id := by
        change CommGroupScheme.groupHom (s.torusIso.hom ≫ s.torusIso.inv) = _
        rw [Iso.hom_inv_id]
        rfl
      inv_hom_id := by
        change CommGroupScheme.groupHom (s.torusIso.inv ≫ s.torusIso.hom) = _
        rw [Iso.inv_hom_id]
        rfl } p.isSplitTorus

/-- The pulled-back torus inclusion is maximal in the pulled-back group. -/
theorem isMaximalTorus :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (fieldMap k K)).obj s.torus)
      ((GroupScheme.baseChange (fieldMap k K)).map s.inclusion) := by
  have hrec : (GroupScheme.baseChange (fieldMap k K)).map s.inclusion =
      CommGroupScheme.groupHom s.torusIso.hom ≫ p.inclusion ≫ s.group.iso.inv := by
    rw [← Category.assoc, ← s.recovery, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hrec, ← Category.assoc]
  exact (p.isMaximalTorus.iso_comp
    { hom := CommGroupScheme.groupHom s.torusIso.hom
      inv := CommGroupScheme.groupHom s.torusIso.inv
      hom_inv_id := by
        change CommGroupScheme.groupHom (s.torusIso.hom ≫ s.torusIso.inv) = _
        rw [Iso.hom_inv_id]
        rfl
      inv_hom_id := by
        change CommGroupScheme.groupHom (s.torusIso.inv ≫ s.torusIso.hom) = _
        rw [Iso.inv_hom_id]
        rfl }).comp_iso s.group.iso.symm

/-- A reduced root datum on the recovered pair with its actual character comparison. -/
structure RootComparison where
  rootIndex : Type u
  [finiteRootIndex : Finite rootIndex]
  rootDatum : RootDatum rootIndex
    (characterLattice ((CommGroupScheme.baseChange (fieldMap k K)).obj s.torus))
    (cocharacterLattice ((CommGroupScheme.baseChange (fieldMap k K)).obj s.torus))
  isRootDatum : IsRootDatumOf
    ((GroupScheme.baseChange (fieldMap k K)).map s.inclusion) rootDatum
  isReduced : rootDatum.IsReduced
  equiv : RootPairing.Equiv p.rootDatum rootDatum
  weightMap : ∀ χ, equiv.weightMap χ = s.torusIso.hom ≫ χ

attribute [instance] RootComparison.finiteRootIndex

/-- A root comparison obtained from the actual descended torus and ambient isomorphisms. -/
def rootComparison : RootComparison s := by
  apply Classical.choice
  have hG := IsConnectedReductive.of_iso s.group.iso p.isConnectedReductive
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    rootDatumExistence K _ hG _ s.isSplitTorus _ s.isMaximalTorus
  exact
    ⟨{
      rootIndex := J
      finiteRootIndex := hJ
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      equiv := rootDatumEquivOfTorusCompatibleIso hG p.isConnectedReductive s.isSplitTorus
        p.isSplitTorus s.isMaximalTorus p.isMaximalTorus
        s.group.iso s.torusIso s.recovery hP p.isRootDatum
      weightMap := fun χ => rootDatumEquivOfTorusCompatibleIso_weightMap hG
        p.isConnectedReductive s.isSplitTorus p.isSplitTorus s.isMaximalTorus
        p.isMaximalTorus s.group.iso s.torusIso s.recovery hP p.isRootDatum χ }⟩

/-- Galois pinning data with exactly the descended torus and inclusion. -/
def pinningData : GaloisPinningData k K s.group.obj where
  torus := s.torus
  inclusion := s.inclusion
  isConnectedReductive := IsConnectedReductive.of_iso s.group.iso p.isConnectedReductive
  isSplitTorus := s.isSplitTorus
  isMaximalTorus := s.isMaximalTorus
  rootIndex := s.rootComparison.rootIndex
  rootDatum := s.rootComparison.rootDatum
  isRootDatum := s.rootComparison.isRootDatum
  isReduced := s.rootComparison.isReduced
  base := p.base.map s.rootComparison.equiv
  pinning := RootPinning.ofSplitMaximalTorus
    (IsConnectedReductive.of_iso s.group.iso p.isConnectedReductive) s.isSplitTorus _
    s.isMaximalTorus s.rootComparison.rootDatum s.rootComparison.isRootDatum
    (p.base.map s.rootComparison.equiv)

/-- The root equivalence on the actual descended Galois pinning data. -/
def rootEquiv : RootPairing.Equiv p.rootDatum s.pinningData.toSplitPinning.rootDatum :=
  s.rootComparison.equiv

/-- The root equivalence preserves the supplied base. -/
theorem rootEquiv_preserves_base (a : p.rootIndex) :
    a ∈ p.base.support ↔ s.rootEquiv.indexEquiv a ∈ s.pinningData.toSplitPinning.base.support := by
  classical
  change a ∈ p.base.support ↔ s.rootComparison.equiv.indexEquiv a ∈
    (p.base.map s.rootComparison.equiv).support
  rw [RootPairing.Base.support_map_eq]
  constructor
  · intro ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · rintro h
    obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp h
    exact s.rootComparison.equiv.indexEquiv.injective heq ▸ ha'

/-- The root equivalence uses the forward torus comparison on every character. -/
theorem rootEquiv_weightMap (χ : characterLattice p.torus) :
    s.rootEquiv.weightMap χ = s.torusIso.hom ≫ χ :=
  s.rootComparison.weightMap χ

end GaloisTorusSolution
end Langlands.GroupScheme.SplitPinning
