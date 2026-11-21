import Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction
import Langlands.Geometry.Building.KPCentralizerNormKernelCompactness
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Rational.AnisotropicCompactnessProof
import Langlands.GroupScheme.Rational.RelativeRankProof
import Langlands.GroupScheme.Rational.TrivialRelativeTitsSystem
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.Representation.Plancherel.FullLatticeRepresentativeProof

/-! # Cartan and congruence data for relative semisimple rank zero -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.Geometry.Building
open Langlands.Plancherel Langlands.Plancherel.RenardCartan

namespace Langlands.HarishChandraSchwartz

namespace RankZero

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

local instance rankZeroAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance rankZeroAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance rankZeroAmbientTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G
local instance rankZeroFieldT2 : T2Space F := Langlands.BruhatTits.localField_t2Space F
local instance rankZeroAmbientT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rankZeroAmbientNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

open Langlands.LinearAlgebra.RationalSpan in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- When the relative root span has rank zero, each actual root would
rationalize to zero, contrary to injectivity on the split character lattice. -/
theorem relativeRoots_eq_empty_of_rankZero (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : relativeRootRank i = 0) : relativeRoots i = ∅ := by
  let := (relativeRank.2 F G hG S i hi).2.1
  have hb : relativeRootSpan i = ⊥ := Submodule.finrank_eq_zero.mp hzero
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro α hα
  have hx : toRat α ∈ relativeRootSpan i := toRat_mem_ratSpan hα
  rw [hb, Submodule.mem_bot] at hx
  exact (mem_relativeRoots.mp hα).1 (hi.isSplitSubtorus.1.character_toRat_injective
    (hx.trans (map_zero toRat).symm))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem isCentral_of_rankZero (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hzero : relativeRootRank i = 0) : IsCentral i := by
  let := hG.smooth
  let := hG.connectedSpace
  exact isCentral_of_roots_eq_empty hi.isSplitSubtorus.1 i
    (relativeRoots_eq_empty_of_rankZero hG hi hzero)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem centralizerPoints_eq_top (hc : IsCentral i) : centralizerPoints i = ⊤ := by
  rw [← torusCentralizer_carrier_base, (isCentral_iff_torusCentralizer_eq_top i).mp hc]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem standardLeviPoints_eq_top (ν : cocharacterLattice S) (hc : IsCentral i)
    (J : Set (characterLattice S)) : standardLeviPoints i ν J = ⊤ :=
  top_unique ((centralizerPoints_eq_top hc).ge.trans (centralizerPoints_le_standardLeviPoints i ν J))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem standardUnipotentPoints_eq_bot (ν : cocharacterLattice S)
    (hroots : relativeRoots i = ∅) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) : standardUnipotentPoints i ν J = ⊥ := by
  have hs := simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν hroots
  have heq : J = simpleRelativeRoots i ν := le_antisymm hJ (by rw [hs]; exact Set.empty_subset _)
  rw [heq]
  change (standardUnipotent i ν _).carrier (Over.mk (𝟙 _)) = _
  rw [standardUnipotent_simple_eq_bot]
  rfl

private theorem trivialIwahori {H : Type u} [Group H] (K : Subgroup H) :
    HasIwahoriIntersectionDecomposition K ⊤ ⊥ ⊥ := by
  have hleft (x : ↥(K ⊓ ⊥)) : (x : H) = 1 := Subgroup.mem_bot.mp x.property.2
  constructor
  · intro x y hxy
    refine Prod.ext (Subtype.ext ((hleft x.1).trans (hleft y.1).symm))
      (Prod.ext (Subtype.ext ?_) (Subtype.ext ((hleft x.2.2).trans (hleft y.2.2).symm)))
    simpa only [orderedIntersectionProduct, hleft, one_mul, mul_one] using
      congrArg Subtype.val hxy
  · intro k
    refine ⟨(1, ⟨k, k.property, Subgroup.mem_top _⟩, 1), Subtype.ext ?_⟩
    simp [orderedIntersectionProduct]

private theorem trivialWeakContraction {H : Type u} [Group H] (K : Subgroup H) (C : Set H) :
    WeakChamberContraction K ⊥ ⊥ C := by
  intro m _
  simp only [inf_bot_eq]
  constructor <;> rintro _ ⟨x, hx, rfl⟩ <;>
    simp only [SetLike.mem_coe, Subgroup.mem_bot] at hx ⊢ <;> simp [hx]

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter i ν) (hzero : relativeRootRank i = 0)

include hG hi hν hzero in
private theorem basis_of_rankZero {K0 : Subgroup (rationalPoints G)}
    (hKc : IsCompact (K0 : Set (rationalPoints G)))
    (hKo : IsOpen (K0 : Set (rationalPoints G))) :
    SimultaneousStandardBasisAt i ν K0 := by
  have hr := relativeRoots_eq_empty_of_rankZero hG hi hzero
  have hc := isCentral_of_rankZero hG hi hzero
  let C := standardSplitComponentFamily i ν hG hi hν
  obtain ⟨B, hB⟩ := exists_compactOpenNormalBasis K0 hKc hKo
  apply simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily i ν hG hi hν C K0
  intro W hW
  obtain ⟨K, hK, hKW⟩ := hB.2.mem_iff.mp hW
  refine ⟨K, ⟨hB.1 K hK, fun J hJ => ?_⟩, hKW⟩
  have hU := standardUnipotentPoints_eq_bot ν hr hJ
  have hU' : standardOppositeUnipotentPoints i ν J = ⊥ := by
    apply standardUnipotentPoints_eq_bot (-ν) hr
    have hJ0 : J = ∅ :=
      Set.subset_empty_iff.mp ((simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν hr) ▸ hJ)
    rw [hJ0, Set.image_empty]
    exact Set.empty_subset _
  rw [standardLeviPoints_eq_top ν hc J, hU, hU']
  exact ⟨trivialIwahori K, trivialWeakContraction K _⟩

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hzero in
private theorem cartan_of_rankZero
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    StandardLeviCartanCovering F i ν J (rationalCommonNormKernel G) := by
  classical
  have hr := relativeRoots_eq_empty_of_rankZero hG hi hzero
  have hc := isCentral_of_rankZero hG hi hzero
  have hJ0 : J = ∅ :=
    Set.subset_empty_iff.mp ((simpleRelativeRoots_eq_empty_of_relativeRoots_eq_empty i ν hr) ▸ hJ)
  have hsc : IsSplitComponent i :=
    ⟨⟨hi.1, hc⟩, fun A a ha f hf => hi.2 A a ha.1 f hf⟩
  obtain ⟨⟨D, hD⟩, hsection⟩ := fullLatticeRepresentative F G hG S i hsc
  let lift (x : rationalPoints G) : centralizerPoints i :=
    ⟨x, by rw [centralizerPoints_eq_top hc]; exact Subgroup.mem_top _⟩
  refine ⟨hD.1.toFinset.image lift, fun g _ => ?_⟩
  obtain ⟨z, hz⟩ := (hsection D hD).1.2 ((rationalCharacterValuation G).rangeRestrict g)
  obtain ⟨c, hc₀, f, hf, hcf⟩ := (mem_tildeC0 i D z.val).mp z.property
  obtain ⟨v, hv⟩ := (mem_C0 S i c).mp hc₀
  let a := uniformizerSection S (Multiplicative.ofAdd v)
  have hcomm : Commute c f :=
    (Subgroup.mem_center_iff.mp (hsc.1.range_le_center (show c ∈ (rationalPoints.map i).range
      from ⟨a, hv⟩)) f).symm
  have hzval : rationalCharacterValuation G (f * c) = rationalCharacterValuation G g := by
    rw [← hcomm.eq, hcf]
    exact congrArg Subtype.val hz
  let k : rationalPoints G := (f * c)⁻¹ * g
  have hk : k ∈ rationalCommonNormKernel G := by
    rw [← rationalCharacterValuation_ker, MonoidHom.mem_ker]
    change rationalCharacterValuation G ((f * c)⁻¹ * g) = 1
    rw [map_mul, map_inv, hzval, inv_mul_cancel]
  have ha : a ∈ CocharacterUniformizer.CAplus F S J := by
    refine ⟨⟨Multiplicative.ofAdd v, rfl⟩, ?_⟩
    simp [hJ0]
  refine ⟨1, k, lift f, a, (rationalCommonNormKernel G ⊓ standardLeviPoints i ν J).one_mem,
    ⟨hk, by rw [standardLeviPoints_eq_top ν hc]; exact Subgroup.mem_top _⟩,
    Finset.mem_image.mpr ⟨f, hD.1.mem_toFinset.mpr hf, rfl⟩, ha, ?_⟩
  have he : rationalPoints.map i a = c := hv
  change g = 1 * f * rationalPoints.map i a * k
  rw [one_mul, he]
  simp only [k, mul_inv_cancel_left]

/-- The compactness, basis and Cartan properties used by the packet
estimate at the common norm kernel. -/
def HasPacketStructureAtNormKernel : Prop :=
    IsCompact (rationalCommonNormKernel G : Set (rationalPoints G)) ∧
    SimultaneousStandardBasisAt i ν (rationalCommonNormKernel G) ∧
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
      StandardLeviCartanCovering F i ν J (rationalCommonNormKernel G)

include hG hi hν hzero in
/-- Relative semisimple rank zero gives all the required geometry at
the common norm kernel. -/
theorem packetStructure_of_rankZero : HasPacketStructureAtNormKernel (i := i) ν := by
  have hc := isCentral_of_rankZero hG hi hzero
  have hKc := Langlands.BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    centralQuotientReductive anisotropicCompactness_proof G hG hi hc
  exact ⟨hKc, basis_of_rankZero hG hi ν hν hzero hKc (isOpen_rationalCommonNormKernel G),
    cartan_of_rankZero hG hi ν hzero⟩

end RankZero

end Langlands.HarishChandraSchwartz
