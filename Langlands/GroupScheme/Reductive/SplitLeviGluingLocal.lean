import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Rational.RepresentedCrossTorusTransport
import Langlands.GroupScheme.Rational.RootProductTransport
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof

/-! # Actual local Levi comparisons and their root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i₁ : T.toGrp ⟶ G₁) (i₂ : T.toGrp ⟶ G₂)

/-- The condition on the cocharacter in the published Levi gluing hypothesis. -/
def IsRankOneDirection [IsAffineHom G₁.X.hom] (ν : cocharacterLattice T) : Prop :=
  ∀ α ∈ roots i₁, ∀ β ∈ roots i₁, latticePairing T α ν = 0 →
    latticePairing T β ν = 0 → ¬ LinearIndependent ℤ ![α, β]

/-- The local premise of the published gluing statement, with its all-test
representatives and torus factorizations unchanged. -/
def RankOneLeviHypothesis [IsAffineHom G₁.X.hom] : Prop :=
  ∀ ν : cocharacterLattice T, IsRankOneDirection i₁ ν →
    ∀ (Z₁ Z₂ : GroupScheme (Spec (CommRingCat.of k)))
      (z₁ : Z₁ ⟶ G₁) (z₂ : Z₂ ⟶ G₂),
      IsClosedSubgroup z₁ → IsClosedSubgroup z₂ →
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₁)).IsRepresentedBy z₁ →
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₂)).IsRepresentedBy z₂ →
      ∀ (t₁ : T.toGrp ⟶ Z₁) (t₂ : T.toGrp ⟶ Z₂), t₁ ≫ z₁ = i₁ → t₂ ≫ z₂ = i₂ →
        ∃ φ : Z₁ ≅ Z₂, t₁ ≫ φ.hom = t₂

/-- Actual local centralizers and an isomorphism over the common torus. -/
structure LocalComparison (ν : cocharacterLattice T) where
  left : GroupScheme (Spec (CommRingCat.of k))
  right : GroupScheme (Spec (CommRingCat.of k))
  leftInclusion : left ⟶ G₁
  rightInclusion : right ⟶ G₂
  leftClosed : IsClosedSubgroup leftInclusion
  rightClosed : IsClosedSubgroup rightInclusion
  leftRep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₁)).IsRepresentedBy
    leftInclusion
  rightRep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₂)).IsRepresentedBy
    rightInclusion
  leftTorus : T.toGrp ⟶ left
  rightTorus : T.toGrp ⟶ right
  leftTorusComp : leftTorus ≫ leftInclusion = i₁
  rightTorusComp : rightTorus ≫ rightInclusion = i₂
  iso : left ≅ right
  torusIsoComp : leftTorus ≫ iso.hom = rightTorus

/-- Instantiate the local gluing premise at the existing canonical affine
centralizers. No local representative or comparison map is an extra input. -/
def localComparison [IsAffineHom G₁.X.hom] [IsAffineHom G₂.X.hom]
    (hlocal : RankOneLeviHypothesis i₁ i₂)
    (ν : cocharacterLattice T) (hν : IsRankOneDirection i₁ ν) :
    LocalComparison i₁ i₂ ν := by
  let : IsAffine G₁.X.left := isAffine_of_isAffineHom G₁.X.hom
  let : IsAffine G₂.X.left := isAffine_of_isAffineHom G₂.X.hom
  let z₁ := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ν ≫ i₁)
  let z₂ := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ν ≫ i₂)
  have hz₁ := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ν ≫ i₁)
  have hz₂ := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ν ≫ i₂)
  let t₁ := Dynamic.torusFactor i₁ (CommGroupScheme.groupHom ν) hz₁
  let t₂ := Dynamic.torusFactor i₂ (CommGroupScheme.groupHom ν) hz₂
  have ht₁ : t₁ ≫ z₁ = i₁ := Dynamic.torusFactor_comp _ _ _
  have ht₂ : t₂ ≫ z₂ = i₂ := Dynamic.torusFactor_comp _ _ _
  have hexists : ∃ φ : _ ≅ _, t₁ ≫ φ.hom = t₂ :=
    hlocal ν hν _ _ z₁ z₂
      (Dynamic.Affine.isClosedSubgroup_centralizerHom _)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom _) hz₁ hz₂ t₁ t₂ ht₁ ht₂
  exact
    { left := _
      right := _
      leftInclusion := z₁
      rightInclusion := z₂
      leftClosed := Dynamic.Affine.isClosedSubgroup_centralizerHom _
      rightClosed := Dynamic.Affine.isClosedSubgroup_centralizerHom _
      leftRep := hz₁
      rightRep := hz₂
      leftTorus := t₁
      rightTorus := t₂
      leftTorusComp := ht₁
      rightTorusComp := ht₂
      iso := hexists.choose
      torusIsoComp := hexists.choose_spec }

section RootDirection

variable [IsAffineHom G₁.X.hom] [LocallyOfFiniteType G₁.X.hom]
    (hT : IsSplitTorus T.toGrp) {α : characterLattice T} (hα : α ≠ 0)

/-- The existing generic kernel cocharacter meets the exact condition of the
local gluing premise; no root reducedness is needed. -/
theorem kernelCocharacter_isRankOneDirection :
    IsRankOneDirection i₁
      (RootReducedness.kernelCocharacter hT hα (hT.finite_relativeRoots i₁)) := by
  intro β hβ δ hδ hβν hδν
  apply RootReducedness.not_linearIndependent_of_not_linearIndependent hT hα hδ.1
  · exact RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
      hT hα (hT.finite_relativeRoots i₁) hβ hβν
  · exact RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
      hT hα (hT.finite_relativeRoots i₁) hδ hδν

/-- Construct the local comparison for any nonzero character by the generic
kernel direction, using the supplied local gluing hypothesis. -/
def rootLocalComparison [IsAffineHom G₂.X.hom]
    (hlocal : RankOneLeviHypothesis i₁ i₂) :
    LocalComparison i₁ i₂
      (RootReducedness.kernelCocharacter hT hα (hT.finite_relativeRoots i₁)) :=
  localComparison i₁ i₂ hlocal _
    (kernelCocharacter_isRankOneDirection i₁ hT hα)

end RootDirection

namespace LocalComparison

variable {i₁ i₂} {ν : cocharacterLattice T} (C : LocalComparison i₁ i₂ ν)

instance [IsAffineHom G₁.X.hom] : IsAffineHom C.left.X.hom :=
  C.leftClosed.isAffineHom

instance [IsAffineHom G₂.X.hom] : IsAffineHom C.right.X.hom :=
  C.rightClosed.isAffineHom

instance [Smooth G₁.X.hom] [IsAffineHom G₁.X.hom] : Smooth C.left.X.hom :=
  (dynamicSmooth k G₁ _ _ C.leftInclusion).2.1 C.leftRep

instance [Smooth G₂.X.hom] [IsAffineHom G₂.X.hom] : Smooth C.right.X.hom :=
  (dynamicSmooth k G₂ _ _ C.rightInclusion).2.1 C.rightRep

instance [Smooth G₁.X.hom] [IsAffineHom G₁.X.hom] [ConnectedSpace G₁.X.left] :
    ConnectedSpace C.left.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G₁ _ C.leftRep

instance [Smooth G₂.X.hom] [IsAffineHom G₂.X.hom] [ConnectedSpace G₂.X.left] :
    ConnectedSpace C.right.X.left :=
  DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G₂ _ C.rightRep

theorem leftTorus_closed (hi : IsClosedSubgroup i₁) : IsClosedSubgroup C.leftTorus :=
  IsClosedSubgroup.of_comp C.leftClosed (by rw [C.leftTorusComp]; exact hi)

theorem rightTorus_closed (hi : IsClosedSubgroup i₂) : IsClosedSubgroup C.rightTorus :=
  IsClosedSubgroup.of_comp C.rightClosed (by rw [C.rightTorusComp]; exact hi)

end LocalComparison

section RootImage

variable {G Z : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (z : Z ⟶ G)
    (hz : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy z)
    (hzc : IsClosedSubgroup z) (t : T.toGrp ⟶ Z) (ht : t ≫ z = i)
    (hT : IsSplitTorus T.toGrp) (α : characterLattice T) (hα : α ≠ 0)
    (hαν : latticePairing T α ν = 0)

include hz hzc ht hT hα hαν in
/-- The full intrinsic root subgroup is unchanged in a cocharacter centralizer
when its character annihilates that cocharacter. This is an all-test equality. -/
theorem root_map_centralizer :
    (RelativeRoot.subgroup t α).map z = RelativeRoot.subgroup i α := by
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc k T hT α hα
  let : QuasiCompact (CommGroupScheme.groupHom α).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom α).hom.hom.left := hflat
  let : Surjective (CommGroupScheme.groupHom α).hom.hom.left := hsurj
  have hpre : (RelativeRoot.subgroup i α).comap z = RelativeRoot.subgroup t α := by
    rw [← ht]
    exact RelativeRoot.subgroup_comap_closedEmbedding t α z hzc
  have hle : RelativeRoot.subgroup i α ≤ SubgroupFunctor.range z := by
    rw [hz.2]
    exact RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i α ν hαν
  rw [← hpre, SubgroupFunctor.map_comap]
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  exact ⟨And.right, fun hx => ⟨hle U hx, hx⟩⟩

end RootImage

namespace LocalComparison

variable {i₁ i₂} {ν : cocharacterLattice T} (C : LocalComparison i₁ i₂ ν)
    (α : characterLattice T)

/-- Actual smooth closed representatives of the root subgroups in the local
Levis, with the isomorphism induced by their torus-compatible comparison. -/
structure RootComparison where
  left : GroupScheme (Spec (CommRingCat.of k))
  right : GroupScheme (Spec (CommRingCat.of k))
  leftInclusion : left ⟶ C.left
  rightInclusion : right ⟶ C.right
  leftRep : (RelativeRoot.subgroup C.leftTorus α).IsRepresentedBy leftInclusion
  rightRep : (RelativeRoot.subgroup C.rightTorus α).IsRepresentedBy rightInclusion
  leftClosed : IsClosedSubgroup leftInclusion
  rightClosed : IsClosedSubgroup rightInclusion
  leftSmooth : Smooth left.X.hom
  rightSmooth : Smooth right.X.hom
  leftConnected : ConnectedSpace left.X.left
  rightConnected : ConnectedSpace right.X.left
  iso : left ≅ right
  isoComp : iso.hom ≫ rightInclusion = leftInclusion ≫ C.iso.hom

/-- Root representatives and their comparison are constructed from the actual
local Levi comparison, using the published intrinsic-root realization theorem. -/
def rootComparison [Smooth G₁.X.hom] [IsAffineHom G₁.X.hom]
    [Smooth G₂.X.hom] [IsAffineHom G₂.X.hom]
    (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0) : C.RootComparison α := by
  apply Classical.choice
  obtain ⟨U₁, u₁, hu₁, huc₁, hus₁, huconn₁⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hT C.leftTorus α hα
  obtain ⟨U₂, u₂, hu₂, huc₂, hus₂, huconn₂⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hT C.rightTorus α hα
  have htorus : C.leftTorus ≫ C.iso.hom =
      CommGroupScheme.groupHom (Iso.refl T).hom ≫ C.rightTorus := by
    change C.leftTorus ≫ C.iso.hom = 𝟙 _ ≫ C.rightTorus
    simpa only [Category.id_comp] using C.torusIsoComp
  have hu₂' : (RelativeRoot.subgroup C.rightTorus
      (characterLattice.congr (Iso.refl T) α)).IsRepresentedBy u₂ := by
    simpa [characterLattice.congr_apply] using hu₂
  let e := RelativeRoot.subgroupTransportIso (Iso.refl T) C.iso htorus α hu₁ hu₂'
  exact ⟨
    { left := U₁
      right := U₂
      leftInclusion := u₁
      rightInclusion := u₂
      leftRep := hu₁
      rightRep := hu₂
      leftClosed := huc₁
      rightClosed := huc₂
      leftSmooth := hus₁
      rightSmooth := hus₂
      leftConnected := huconn₁
      rightConnected := huconn₂
      iso := e
      isoComp := RelativeRoot.subgroupTransportIso_hom_comp
        (Iso.refl T) C.iso htorus α hu₁ hu₂' }⟩

namespace RootComparison

variable {C α} (R : C.RootComparison α)

theorem left_ambientRep (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0)
    (hαν : latticePairing T α ν = 0) :
    (RelativeRoot.subgroup i₁ α).IsRepresentedBy
      (R.leftInclusion ≫ C.leftInclusion) := by
  rw [← root_map_centralizer i₁ ν C.leftInclusion C.leftRep C.leftClosed
    C.leftTorus C.leftTorusComp hT α hα hαν]
  exact R.leftRep.comp C.leftRep

theorem right_ambientRep (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0)
    (hαν : latticePairing T α ν = 0) :
    (RelativeRoot.subgroup i₂ α).IsRepresentedBy
      (R.rightInclusion ≫ C.rightInclusion) := by
  rw [← root_map_centralizer i₂ ν C.rightInclusion C.rightRep C.rightClosed
    C.rightTorus C.rightTorusComp hT α hα hαν]
  exact R.rightRep.comp C.rightRep

end RootComparison
end LocalComparison

end Langlands.GroupScheme.LeviGluing
