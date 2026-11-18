import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # A compact remainder for the full center modulo the actual split component -/

noncomputable section

universe u v

open scoped Pointwise

namespace Langlands

section QuotientRepresentatives

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]

/-- A compact coset space of a locally compact group admits a compact set
of representatives, without choosing a continuous global section. -/
theorem exists_isCompact_quotient_representatives (A : Subgroup H)
    [CompactSpace (H ⧸ A)] :
    ∃ C : Set H, IsCompact C ∧ ∀ h : H,
      ∃ c ∈ C, ∃ a ∈ A, h = c * a := by
  classical
  obtain ⟨D, hD, hDn⟩ := exists_compact_mem_nhds (1 : H)
  have h1 : (1 : H) ∈ interior D := mem_interior_iff_mem_nhds.mpr hDn
  have hopen (h : H) : IsOpen (QuotientGroup.mk '' (h • interior D) : Set (H ⧸ A)) :=
    QuotientGroup.isOpenMap_coe _ (isOpen_interior.smul h)
  have hcover : Set.univ ⊆ ⋃ h : H,
      (QuotientGroup.mk '' (h • interior D) : Set (H ⧸ A)) := by
    intro q _
    induction q using QuotientGroup.induction_on with
    | H h =>
      exact Set.mem_iUnion.mpr ⟨h, h, Set.mem_smul_set.mpr ⟨1, h1, mul_one h⟩, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun h : H => (QuotientGroup.mk '' (h • interior D) : Set (H ⧸ A))) hopen hcover
  let C : Set H := ⋃ h ∈ t, h • D
  have hC : IsCompact C := t.finite_toSet.isCompact_biUnion fun h _ => hD.smul h
  refine ⟨C, hC, fun h => ?_⟩
  obtain ⟨g, hg, c, hc, hch⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (h : H ⧸ A)))
  obtain ⟨d, hd, rfl⟩ := Set.mem_smul_set.mp hc
  have hgc : g * d ∈ C := Set.mem_iUnion₂.mpr
    ⟨g, hg, Set.mem_smul_set.mpr ⟨d, interior_subset hd, rfl⟩⟩
  have ha : (g * d)⁻¹ * h ∈ A := QuotientGroup.eq.mp hch
  refine ⟨g * d, hgc, (g * d)⁻¹ * h, ha, ?_⟩
  group

end QuotientRepresentatives

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

/-- The full rational-point center is covered by the product of a compact
central subset and the point image of the split component. -/
def RationalSplitCenterCompactRemainder
    {F : Type u} [Field F] [TopologicalSpace F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G) : Prop :=
  ∃ C : Set (rationalPoints G), IsCompact C ∧
    C ⊆ (Subgroup.center (rationalPoints G) : Set (rationalPoints G)) ∧
    ∀ z ∈ Subgroup.center (rationalPoints G),
      ∃ c ∈ C, ∃ a ∈ (rationalPoints.map s).range, z = c * a

/-- Every point of the full abstract center is a point of one compact central
remainder times an actual split-component point. -/
theorem exists_isCompact_rationalSplitCenter_remainder
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s) :
    RationalSplitCenterCompactRemainder s := by
  let : TopologicalSpace (schemeCenterPoints G) := schemeCenterPointTopology G
  let : TopologicalSpace (CentralPointQuotient s hs.isCentralSplitTorus.isCentral) :=
    centralPointQuotientTopology s hs.isCentralSplitTorus.isCentral
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have hZ : IsClosed ((schemeCenterPoints G : Subgroup (rationalPoints G)) :
      Set (rationalPoints G)) := by
    rw [rationalCenterComparison F G hG]
    have heq : (Subgroup.center (rationalPoints G) : Set (rationalPoints G)) =
        ⋂ g : rationalPoints G, {z | g * z = z * g} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_center_iff]
    rw [heq]
    exact isClosed_iInter fun g => isClosed_eq
      (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have : LocallyCompactSpace (schemeCenterPoints G) := hZ.locallyCompactSpace
  have : CompactSpace (CentralPointQuotient s hs.isCentralSplitTorus.isCentral) :=
    centerSplitComponentCompactness F G hG T s hs
  obtain ⟨D, hD, hrep⟩ := Langlands.exists_isCompact_quotient_representatives
    (centralRationalPointImage s hs.isCentralSplitTorus.isCentral)
  refine ⟨Subtype.val '' D, hD.image continuous_subtype_val, ?_, ?_⟩
  · rintro _ ⟨d, _, rfl⟩
    exact schemeCenterPoints_le_center G d.property
  · intro z hz
    have hz' : z ∈ schemeCenterPoints G := by
      rwa [rationalCenterComparison F G hG]
    obtain ⟨d, hd, a, ha, heq⟩ := hrep ⟨z, hz'⟩
    obtain ⟨t, ht⟩ := (mem_centralRationalPointImage s
      hs.isCentralSplitTorus.isCentral a).mp ha
    exact ⟨d, ⟨d, hd, rfl⟩, a, ⟨t, ht⟩, congrArg Subtype.val heq⟩

/-- A cover by compact right factors and arbitrary full-central factors gives
a cover on the actual split-central quotient with one compact right factor. -/
theorem exists_rationalSplitCentralQuotient_cover_of_central_cover
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    {J : Type v} (a : J → rationalPoints G) (K : Set (rationalPoints G))
    {R : Set (rationalPoints G)} (hR : IsCompact R)
    (hcover : ∀ g : rationalPoints G, ∃ j : J, ∃ k ∈ K, ∃ y ∈ R,
      ∃ z ∈ Subgroup.center (rationalPoints G), g = k * a j * y * z) :
    ∃ Y : Set (rationalPoints G), IsCompact Y ∧
      ∀ q : LeftQuotient (rationalPoints.map s).range, ∃ j : J,
        q ∈ leftQuotientMap (rationalPoints.map s).range '' (K * {a j} * Y) := by
  obtain ⟨C, hC, -, hrep⟩ := exists_isCompact_rationalSplitCenter_remainder hG s hs
  refine ⟨R * C, hR.mul hC, fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨j, k, hk, y, hy, z, hz, hg⟩ := hcover g
    obtain ⟨c, hc, b, hb, hzb⟩ := hrep z hz
    have hbcent := hs.isCentralSplitTorus.isCentral.range_le_center hb
    have heq : g = b * (k * a j * (y * c)) := by
      rw [hg, hzb]
      calc
        k * a j * y * (c * b) = (k * a j * (y * c)) * b := by group
        _ = b * (k * a j * (y * c)) := Subgroup.mem_center_iff.mp hbcent _
    refine ⟨j, k * a j * (y * c), ?_, ?_⟩
    · exact ⟨k * a j, ⟨k, hk, a j, Set.mem_singleton _, rfl⟩,
        y * c, ⟨y, hy, c, hc, rfl⟩, rfl⟩
    · apply Quotient.sound
      change QuotientGroup.rightRel (rationalPoints.map s).range (k * a j * (y * c)) g
      rw [QuotientGroup.rightRel_apply]
      have hm : g * (k * a j * (y * c))⁻¹ = b := by rw [heq]; group
      rw [hm]
      exact hb

end Langlands.HarishChandraSchwartz
