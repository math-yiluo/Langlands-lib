import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardNestedFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProjectionContinuityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.BruhatTits.SpecialCompact.SemistandardParabolicSplitting
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.Representation.Aubert.General.NestedParabolicModulus
import Langlands.Representation.Plancherel.SemidirectSourceHaarNormalization

/-! # Common-compact radical normalization for nested constant terms -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General
open Langlands.BruhatTits.SpecialCompact Langlands.GroupScheme Langlands.Haar Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p r : SemistandardSpectralIndex i} (m : LeviModel p)

omit [LocallyOfFiniteType G.X.hom] in
private theorem outerLevi_isClosed (m : LeviModel p) :
    IsClosed (levi p : Set (rationalPoints G)) :=
  isClosed_rationalPoint_subgroup F p.levi m.inclusion m.represents m.closed

local instance nestedRadicalSubgroupSecondCountable {H : Type*} [Group H] [TopologicalSpace H]
    [SecondCountableTopology H] (L : Subgroup H) : SecondCountableTopology L :=
  TopologicalSpace.Subtype.secondCountableTopology (L : Set H)

private theorem intermediateRadical_embedding (m : LeviModel p) :
    Topology.IsClosedEmbedding
      (((levi p).subtype.comp ((radical r).subgroupOf (levi p)).subtype) :
        (radical r).subgroupOf (levi p) → rationalPoints G) :=
  (outerLevi_isClosed m).isClosedEmbedding_subtypeVal.comp
    ((isClosed_radical r).preimage continuous_subtype_val).isClosedEmbedding_subtypeVal

/-- Haar on the inner radical in the literal outer Levi, with mass one on
its trace of the original ambient compact. -/
def intermediateRadicalHaar (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G))) :
    Measure ((radical r).subgroupOf (levi p)) :=
  compactOpenHaarAlong K hK ((levi p).subtype.comp ((radical r).subgroupOf (levi p)).subtype)
    (intermediateRadical_embedding (r := r) m)

instance intermediateRadicalHaar_isHaarMeasure (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G))) :
    (intermediateRadicalHaar (r := r) m K hK).IsHaarMeasure := by
  unfold intermediateRadicalHaar
  infer_instance

/-- The Haar modulus of the literal final Levi on the intermediate radical. -/
def intermediateModulus : (levi r).subgroupOf (levi p) →* ℝ≥0ˣ :=
  let : LocallyCompactSpace (levi p) := (outerLevi_isClosed m).locallyCompactSpace
  HaarModulus.closedRestrictCharacter ((radical r).subgroupOf (levi p))
    ((isClosed_radical r).preimage continuous_subtype_val) ((levi r).subgroupOf (levi p))
    (normalizes_subgroupOf (semistandardLeviPoints_le_normalizer_radicalPoints r))

variable {m} {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {q : SemistandardSpectralIndex iM} (h : RationalSemistandardParabolicLift p m q r)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include h in
private theorem radical_points_product
    (hprod : r.radical.IsPointwiseProduct (q.radical.map m.inclusion) p.radical) :
    (radical r : Set (rationalPoints G)) =
      ((levi p ⊓ radical r : Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        (radical p : Set (rationalPoints G)) := by
  rw [h.radical_comap, SubgroupFunctor.map_comap, m.represents.2] at hprod
  ext x
  exact (hprod _ x).trans Set.mem_mul.symm

private theorem radical_compactCover (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : radical r) : ∃ C : OpenSubgroup (radical r), IsCompact (C : Set (radical r)) ∧ x ∈ C := by
  obtain ⟨ζ, rfl⟩ := semistandardSpectralDynamicCoverage F G hG S i hi r
  obtain ⟨C, hC, hx⟩ := BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup
    (CommGroupScheme.groupHom ζ ≫ i) {x} isCompact_singleton
  exact ⟨C, hC, hx (Set.mem_singleton x)⟩

include h in
/-- The source-normalized measures on the three radicals satisfy the
Levi-then-radical product formula. The actual conjugation characters
satisfy the two identities used in transitivity of constant terms. -/
theorem sourceRadicalTransitivity (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hspecial : SpecialCompactProperties F i ν K.toSubgroup)
    (hprod : r.radical.IsPointwiseProduct (q.radical.map m.inclusion) p.radical) :
    TransitivityData (subgroupCompactOpenHaar K hK (radical r) (isClosed_radical r))
      (semistandardUnipotentModulus r)
      (subgroupCompactOpenHaar K hK (radical p) (isClosed_radical p))
      (semistandardUnipotentModulus p) (intermediateRadicalHaar (r := r) m K hK)
      (intermediateModulus (r := r) m) := by
  have hRP : parabolic r ≤ parabolic p := by
    intro x hx
    exact (RationalSemistandardParabolicLift.parabolic_le p m q r h)
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) hx
  have hNQ : radical r ≤ parabolic p := (decomposition r).unipotent_le.trans hRP
  have hpoints := h.radical_points_product hprod
  have hp := projectionContinuity (i := i) ‹IsNonarchimedeanLocalField F› hG hi p
  let d := NestedParabolic.radicalDecomposition (decomposition p) hNQ hpoints
  have hd := NestedParabolic.continuous_radical_projection (decomposition p) hNQ hpoints hp
  have hL := outerLevi_isClosed m
  let e := NestedParabolic.interSubgroupOfEquiv (levi p) (radical r)
  let : LocallyCompactSpace (radical p) := (isClosed_radical p).locallyCompactSpace
  refine ⟨d.unipotent_le, ?_, ?_, ?_⟩
  · have hsplit (x : ↥(levi p ⊓ radical r)) (u : radical p) :
        (x : rationalPoints G) * (u : rationalPoints G) ∈ K ↔
          (x : rationalPoints G) ∈ K ∧ (u : rationalPoints G) ∈ K := by
      let outer := CocharacterPresentation.ofCoverage hG semistandardSpectralDynamicCoverage hi p
      have hm : (x : rationalPoints G) ∈ (Dynamic.centralizer outer.hom).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := outer.levi_eq ▸ x.property.1
      have hu : (u : rationalPoints G) ∈ (Dynamic.unipotent outer.hom).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := outer.radical_eq ▸ u.property
      exact mul_mem_iff_of_weylRepresentatives hG hi hν hspecial.2.2.1 hspecial.2.2.2
        outer.cocharacter hm hu
    have hHaar := semidirectSourceParabolicMeasure_eq_subgroupHaar d hd (isClosed_radical r)
      (hL.inter (isClosed_radical r)) (isClosed_radical p) K hK hsplit
    have he := (measurePreserving_compactOpenHaarAlong K hK
      (levi p ⊓ radical r : Subgroup (rationalPoints G)).subtype
      (hL.inter (isClosed_radical r)).isClosedEmbedding_subtypeVal
      ((levi p).subtype.comp ((radical r).subgroupOf (levi p)).subtype)
      (intermediateRadical_embedding (r := r) m) e (fun _ => rfl)).map_eq
    let μU := subgroupCompactOpenHaar K hK (radical p) (isClosed_radical p)
    let μJ := subgroupCompactOpenHaar K hK (levi p ⊓ radical r) (hL.inter (isClosed_radical r))
    have he_measurable : Measurable (⇑e) := e.continuous.measurable
    have hμ : (intermediateRadicalHaar (r := r) m K hK).prod μU =
        (μJ.prod μU).map (Prod.map e id) := by
      calc
        _ = (Measure.map e μJ).prod (Measure.map id μU) :=
          congrArg₂ Measure.prod he.symm Measure.map_id.symm
        _ = _ := Measure.map_prod_map _ _ he_measurable measurable_id
    rw [← hHaar, semidirectSourceParabolicMeasure, hμ,
      Measure.map_map (continuous_unipotentMul d.unipotent_le).measurable
        (he_measurable.prodMap measurable_id)]
    rfl
  · intro l
    have hN := semistandardLeviPoints_le_normalizer_radicalPoints r
    have hlevi := h.levi_points_le
    let x : levi r := ⟨(l : levi p), l.property⟩
    have hmod := NestedParabolic.ambient_modulus_product (decomposition p) hNQ hpoints hp
      (isClosed_radical r) (isClosed_radical p) hL hlevi hN x
    have hinner := NestedParabolic.inner_modulus_eq (isClosed_radical r) hL hlevi hN x
    change intermediateModulus (r := r) m l = _ at hinner
    rw [← hinner, mul_comm] at hmod
    exact hmod
  · intro v
    let v' : radical r := ⟨(v : levi p), v.property⟩
    obtain ⟨C, hC, hv⟩ := radical_compactCover hG hi v'
    let projection : radical r →* levi p := (decomposition p).projection.comp (Subgroup.inclusion hNQ)
    have hprojection : Continuous projection := hp.comp (continuous_subtype_val.subtype_mk _)
    have hmember : (v : levi p) ∈ C.toSubgroup.map projection := by
      refine ⟨v', hv, ?_⟩
      exact (decomposition p).projection_levi (v : levi p)
    exact eq_one_of_isOpen_ker_of_isCompact (semistandardUnipotentModulus p)
      (HaarModulus.isOpen_ker_restrictCharacter _ _ _) (hC.image hprojection) hmember

/-- Conjugation on the outer radical scales its normalized Haar by the
actual outer character. -/
theorem sourceRadicalConjugation (K : OpenSubgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G))) :
    IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p)
      (subgroupCompactOpenHaar K hK (radical p) (isClosed_radical p))
      (semistandardUnipotentModulus p) := by
  let : LocallyCompactSpace (radical p) := (isClosed_radical p).locallyCompactSpace
  exact isConjModulus_restrictCharacter _ _

section Model

local instance nestedRadicalModelAffine : IsAffineHom m.scheme.X.hom :=
  m.reductive.isAffineHom

local instance nestedRadicalModelFiniteType : LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

/-- The maps through the actual outer Levi inclusion preserve the inner
radical Haar and its conjugation character at the common compact trace. -/
theorem sourceConstantTermModelComparison
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (KM : OpenSubgroup (rationalPoints m.scheme))
    (hKM : IsCompact (KM : Set (rationalPoints m.scheme)))
    (htrace : ∀ x : rationalPoints m.scheme, x ∈ KM ↔ rationalPoints.map m.inclusion x ∈ K)
    (eL : levi q ≃ₜ* (levi r).subgroupOf (levi p))
    (eU : radical q ≃ₜ* (radical r).subgroupOf (levi p))
    (hL : ∀ l : levi q, (eL l : levi p) = m.pointHomeomorph l)
    (hU : ∀ v : radical q, (eU v : levi p) = m.pointHomeomorph v) :
    RationalSemistandardConstantTermModelComparison p m q r
      (subgroupCompactOpenHaar KM hKM (radical q) (isClosed_radical q))
      (intermediateRadicalHaar (r := r) m K hK) (intermediateModulus (r := r) m) eL eU := by
  let μQ := subgroupCompactOpenHaar KM hKM (radical q) (isClosed_radical q)
  let : LocallyCompactSpace (radical q) := (isClosed_radical q).locallyCompactSpace
  let : LocallyCompactSpace (levi p) := (outerLevi_isClosed m).locallyCompactSpace
  let hI : IsClosed (((radical r).subgroupOf (levi p)) : Set (levi p)) :=
    (isClosed_radical r).preimage continuous_subtype_val
  let : LocallyCompactSpace ((radical r).subgroupOf (levi p)) := hI.locallyCompactSpace
  refine ⟨hL, hU, ?_, ?_⟩
  · let embed := (levi p).subtype.comp ((radical r).subgroupOf (levi p)).subtype
    have : (Measure.map eU μQ).IsHaarMeasure := eU.isHaarMeasure_map μQ
    have : (Measure.map eU μQ).Regular := Measure.Regular.map eU.toHomeomorph
    have hset : MeasurableSet {v | embed v ∈ K} := (K.isOpen.preimage
      (intermediateRadical_embedding (r := r) m).continuous).measurableSet
    have hpreimage : eU ⁻¹' {v | embed v ∈ K} =
        {v : radical q | (v : rationalPoints m.scheme) ∈ KM} := by
      ext v
      change ((eU v : levi p) : rationalPoints G) ∈ K ↔ (v : rationalPoints m.scheme) ∈ KM
      rw [hU]
      exact (htrace v).symm
    unfold intermediateRadicalHaar
    apply compactOpenHaarAlong_eq_of_mass_one
    rw [Measure.map_apply (show Measurable (⇑eU) from eU.continuous.measurable) hset,
      hpreimage]
    exact subgroupCompactOpenHaar_mass KM hKM (radical q) (isClosed_radical q)
  · intro l
    let : MeasurableSpace (radical q) := borel _
    have : BorelSpace (radical q) := ⟨rfl⟩
    let : MeasurableSpace ((radical r).subgroupOf (levi p)) := borel _
    have : BorelSpace ((radical r).subgroupOf (levi p)) := ⟨rfl⟩
    apply Units.ext
    change mulEquivHaarChar (HaarModulus.normalizerConj (radical q)
      ⟨l, semistandardLeviPoints_le_normalizer_radicalPoints q l.property⟩) =
        mulEquivHaarChar (HaarModulus.normalizerConj ((radical r).subgroupOf (levi p))
          ⟨eL l, normalizes_subgroupOf (semistandardLeviPoints_le_normalizer_radicalPoints r)
            (eL l).property⟩)
    apply Geometric.haarChar_eq_of_conjugacy eU
    intro v
    apply Subtype.ext
    simp only [HaarModulus.normalizerConj_apply, hU, hL, map_mul, map_inv]

end Model

end Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift
