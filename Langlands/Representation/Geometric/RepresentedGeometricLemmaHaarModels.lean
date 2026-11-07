import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization
import Langlands.Representation.Geometric.RepresentedGeometricLemmaGeometryReduction
import Langlands.Representation.Aubert.General.CommonCentralizerFullHaarBalance
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates

/-! # The five original subgroup models for represented orbit Haar balance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "iU" => rQ ≫ q
local notation "iV" => r ≫ p ≫ Iso.hom (GroupScheme.innerIso G z⁻¹)
local notation "iA" => D.r' ≫ D.p' ≫ l ≫ p ≫ Iso.hom (GroupScheme.innerIso G z⁻¹)
local notation "iB" => D.rQ' ≫ D.q' ≫ lQ ≫ q
local notation "iZ" => D.lQ' ≫ D.q' ≫ lQ ≫ q
local notation "iT" => D.targetCommonTorusHom ≫ iZ

/-- The literal scheme intersection of the original target radical and the
original source radical conjugated by the original representative inverse. -/
def haarIntersectionScheme
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection iU iV

/-- Inclusion of that same intersection into the original ambient group. -/
def haarIntersectionHom : D.haarIntersectionScheme ⟶ G :=
  subgroupIntersectionHom iU iV

include D

omit [TopologicalSpace k] D in
include hq hrQ in
/-- Closedness of the original target radical in G. -/
theorem haarTargetRadical_closed : IsClosedSubgroup iU :=
  hrQ.1.isClosedSubgroup.comp hq.isClosedSubgroup

omit [TopologicalSpace k] D in
include hp hr in
/-- Closedness of the original inverse-conjugated source radical in G. -/
theorem haarSourceRadical_closed : IsClosedSubgroup iV :=
  hr.1.isClosedSubgroup.comp
    (hp.isClosedSubgroup.comp_iso (G.innerIso z⁻¹))

/-- Closedness of the inverse-conjugated original source endpoint radical. -/
theorem haarSourceEndpoint_closed : IsClosedSubgroup iA :=
  D.hr'.1.isClosedSubgroup.comp (D.hp'.isClosedSubgroup.comp
    (hl.isClosedSubgroup.comp (hp.isClosedSubgroup.comp_iso (G.innerIso z⁻¹))))

/-- Closedness of the original target endpoint radical. -/
theorem haarTargetEndpoint_closed : IsClosedSubgroup iB :=
  D.hrQ'.1.isClosedSubgroup.comp (D.hq'.isClosedSubgroup.comp
    (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))

/-- Closedness of the original target common Levi. -/
theorem haarCommonLevi_closed : IsClosedSubgroup iZ :=
  D.hlQ'.isClosedSubgroup.comp (D.hq'.isClosedSubgroup.comp
    (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))

/-- Closedness of the actual common radical intersection. -/
theorem haarIntersection_closed : IsClosedSubgroup D.haarIntersectionHom :=
  isClosedSubgroup_subgroupIntersectionHom
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)) (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z))

/-- Transport the source endpoint equality on all test schemes, retaining
N' and its original maps rather than choosing a new intersection model. -/
theorem haarSourceEndpoint_range :
    SubgroupFunctor.range iA =
      SubgroupFunctor.range iU ⊓
        SubgroupFunctor.range (l ≫ p ≫ Iso.hom (GroupScheme.innerIso G z⁻¹)) := by
  have h := range_comp_iso_eq_inf (G.innerIso z⁻¹) D.radical_eq
  have hzz : (G.innerIso z).hom ≫ Iso.hom (GroupScheme.innerIso G z⁻¹) = 𝟙 G := by
    rw [G.innerIso_inv_hom, Iso.hom_inv_id]
  simp only [Category.assoc, hzz, Category.comp_id] at h
  exact h.trans (subgroupFunctor_inf_comm _ _)

/-- The target endpoint is the other, distinct radical/Levi intersection. -/
theorem haarTargetEndpoint_range :
    SubgroupFunctor.range iB =
      SubgroupFunctor.range iV ⊓ SubgroupFunctor.range (lQ ≫ q) :=
  D.radical_eq'.trans (subgroupFunctor_inf_comm _ _)

namespace DynamicRealization

variable (R : D.DynamicRealization)

local notation "chi" => CommGroupScheme.groupHom R.targetCocharacter ≫ iT
local notation "psi" => CommGroupScheme.groupHom R.sourceCocharacter ≫ iT

/-- The same original common Levi centralizes the target cocharacter. -/
theorem haarCommonLevi_centralizes_target :
    SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi := by
  rw [← R.targetLevi, D.levi_eq']
  intro W x hx
  exact hx.1

/-- The same original common Levi centralizes the source cocharacter. -/
theorem haarCommonLevi_centralizes_source :
    SubgroupFunctor.range iZ ≤ Dynamic.centralizer psi := by
  rw [← R.sourceLevi, D.levi_eq']
  intro W x hx
  exact hx.2

/-- The first full dynamic radical is represented by the original U. -/
theorem haarTargetRadical_represented :
    (Dynamic.unipotent chi).IsRepresentedBy iU := by
  rw [← R.targetRadical]
  exact (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).isRepresentedBy_range

/-- The second full dynamic radical is represented by the original N,
with inverse-conjugated inclusion. -/
theorem haarSourceRadical_represented :
    (Dynamic.unipotent psi).IsRepresentedBy iV := by
  rw [← R.sourceRadical]
  exact (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).isRepresentedBy_range

/-- The first axis intersection is represented by the original N'. -/
theorem haarSourceEndpoint_represented :
    (Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).IsRepresentedBy iA := by
  rw [← R.targetRadical, ← R.sourceLevi, ← D.haarSourceEndpoint_range]
  exact D.haarSourceEndpoint_closed.isRepresentedBy_range

/-- The second axis intersection is represented by the original U'. -/
theorem haarTargetEndpoint_represented :
    (Dynamic.unipotent psi ⊓ Dynamic.centralizer chi).IsRepresentedBy iB := by
  rw [← R.sourceRadical, ← R.targetLevi, ← D.haarTargetEndpoint_range]
  exact D.haarTargetEndpoint_closed.isRepresentedBy_range

/-- The common dynamic radical is represented by the literal closed
intersection of the two original radical embeddings. -/
theorem haarIntersection_represented :
    (Dynamic.unipotent chi ⊓ Dynamic.unipotent psi).IsRepresentedBy
      D.haarIntersectionHom := by
  rw [← R.targetRadical, ← R.sourceRadical]
  exact isRepresentedBy_subgroupIntersectionHom
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)) (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z))

section Coordinates

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance haarModelsTorusClosed : IsClosedImmersion (iT).hom.hom.left :=
  D.targetCommonTorus_isMaximalSplitTorus_ambient.1.2

local instance haarModelsSourceEndpointAffine : IsAffineHom D.N'.X.hom :=
  D.haarSourceEndpoint_closed.isAffineHom
local instance haarModelsTargetEndpointAffine : IsAffineHom D.U'.X.hom :=
  D.haarTargetEndpoint_closed.isAffineHom
local instance haarModelsIntersectionAffine : IsAffineHom D.haarIntersectionScheme.X.hom :=
  D.haarIntersection_closed.isAffineHom
local instance haarModelsCommonLeviAffine : IsAffine D.L'.X.left := by
  let := D.haarCommonLevi_closed.isAffineHom
  exact isAffine_of_isAffineHom D.L'.X.hom

local instance haarModelsSourceEndpointFiniteType : LocallyOfFiniteType D.N'.X.hom :=
  D.haarSourceEndpoint_closed.locallyOfFiniteType
local instance haarModelsTargetEndpointFiniteType : LocallyOfFiniteType D.U'.X.hom :=
  D.haarTargetEndpoint_closed.locallyOfFiniteType
local instance haarModelsIntersectionFiniteType :
    LocallyOfFiniteType D.haarIntersectionScheme.X.hom :=
  D.haarIntersection_closed.locallyOfFiniteType

/-- The actual five-factor determinant discrepancy on D.L', using the
original U, N, N', U' and their literal common radical intersection, with
canonical finite coordinates of each actual Lie kernel. -/
def haarDeterminantBalanceDefect : rationalCharacters D.L' := by
  letI : IsAffineHom U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).isAffineHom
  letI : IsAffineHom N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).isAffineHom
  letI : LocallyOfFiniteType U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).locallyOfFiniteType
  letI : LocallyOfFiniteType N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).locallyOfFiniteType
  exact Dynamic.centralizingDeterminantBalanceDefect
    R.targetCocharacter R.sourceCocharacter iZ
    R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
    R.haarTargetRadical_represented R.haarSourceRadical_represented
    R.haarSourceEndpoint_represented R.haarTargetEndpoint_represented
    R.haarIntersection_represented
    (Lie.finiteCoordinates U) (Lie.finiteCoordinates N)
    (Lie.finiteCoordinates D.N') (Lie.finiteCoordinates D.U')
    (Lie.finiteCoordinates D.haarIntersectionScheme)

/-- Relative-root balance makes the discrepancy vanish on the original
common torus. Character detection is not needed for this restriction. -/
theorem haarDeterminantBalanceDefect_restrict_eq_zero
    (hroot : HasRelativeRootSystem iT) :
    characterRestrict D.targetCommonTorusHom R.haarDeterminantBalanceDefect = 0 := by
  let : IsAffineHom U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).isAffineHom
  let : IsAffineHom N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).isAffineHom
  let : LocallyOfFiniteType U.X.hom :=
    (haarTargetRadical_closed (hq := hq) (hrQ := hrQ)).locallyOfFiniteType
  let : LocallyOfFiniteType N.X.hom :=
    (haarSourceRadical_closed (hp := hp) (hr := hr) (z := z)).locallyOfFiniteType
  have hi := D.targetCommonTorus_isMaximalSplitTorus_ambient
  exact Dynamic.characterRestrict_centralizingDeterminantBalanceDefect_eq_zero
    hroot hi.1.1 R.targetCocharacter R.sourceCocharacter iZ
    R.haarCommonLevi_centralizes_target R.haarCommonLevi_centralizes_source
    R.haarTargetRadical_represented R.haarSourceRadical_represented
    R.haarSourceEndpoint_represented R.haarTargetEndpoint_represented
    R.haarIntersection_represented D.targetCommonTorusHom rfl
    (Lie.finiteCoordinates U) (Lie.finiteCoordinates N)
    (Lie.finiteCoordinates D.N') (Lie.finiteCoordinates D.U')
    (Lie.finiteCoordinates D.haarIntersectionScheme)

/-- Explicit algebraic character detection upgrades restricted vanishing
to vanishing on the entire original target common Levi. -/
theorem haarDeterminantBalanceDefect_eq_zero_of_characterRestrict_injective
    (hroot : HasRelativeRootSystem iT)
    (hinj : Function.Injective (characterRestrict D.targetCommonTorusHom)) :
    R.haarDeterminantBalanceDefect = 0 := by
  apply hinj
  rw [map_zero]
  exact haarDeterminantBalanceDefect_restrict_eq_zero D R hroot

end Coordinates

end DynamicRealization

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
