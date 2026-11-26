import Langlands.Representation.Exponents.CentralUniformizerSquareIntegrabilityStatement
import Langlands.Representation.Plancherel.CentralSubgroupComparisonProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # The central uniformizer lattice comparison in Renard VII.1.2 -/

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme GroupScheme.CocharacterUniformizer
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel

private theorem isClosed_uniformizerLattice
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (A : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine A.X.left]
    [LocallyOfFiniteType A.toGrp.X.hom] (hA : IsSplitTorus A.toGrp) :
    letI : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology k A.X
    IsClosed (CA k A : Set (rationalPoints A.toGrp)) := by
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology k A.X
  have : T2Space k := BruhatTits.localField_t2Space k
  let := rationalPoint_t2Space k A.toGrp
  let := rationalPoint_isTopologicalGroup k A.toGrp
  let U := rationalCommonNormKernel A.toGrp
  have hU : IsOpen (U : Set (rationalPoints A.toGrp)) :=
    isOpen_rationalCommonNormKernel A.toGrp
  have hpre : (Subtype.val : CA k A → rationalPoints A.toGrp) ⁻¹' (U : Set _) =
      ({1} : Set (CA k A)) := by
    ext x
    change x.val ∈ U ↔ x = 1
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := x.property
      have hs := (isUniformizerLatticeSection k A hA).2.2 x.val
      have hrep : x.val * (latticeSection k A c)⁻¹ ∈ U := by
        rw [hc, mul_inv_cancel]
        exact U.one_mem
      have hone : x.val * (latticeSection k A 1)⁻¹ ∈ U := by simpa using hx
      apply Subtype.ext
      change x.val = 1
      rw [← hc, hs.unique hrep hone, map_one]
    · rintro rfl
      exact U.one_mem
  have hdiscrete : DiscreteTopology (CA k A) := discreteTopology_of_isOpen_singleton_one <| by
    rw [← hpre]
    exact hU.preimage continuous_subtype_val
  exact Subgroup.isClosed_of_discreteTopology

/-- The actual central lattice is closed and cocompact, so the coefficient
comparison applies to any Haar measure on its quotient. -/
theorem centralUniformizerSquareIntegrability :
    CentralUniformizerSquareIntegrabilityStatement.{u, v} := by
  intro k _ _ _ _ G hG A a ha
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space k := BruhatTits.localField_t2Space k
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  have := rationalPoint_isTopologicalGroup k G
  have := rationalPoint_t2Space k G
  have := rationalPoint_locallyCompactSpace k G
  have := rationalPoint_secondCountableTopology k G
  have hA := ha.isCentralSplitTorus.isSplitSubtorus.1
  have : IsAffineHom A.toGrp.X.hom := hA.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.toGrp.X.hom
  have : Smooth A.toGrp.X.hom := hA.smooth
  have : IsClosedImmersion a.hom.hom.left := ha.isCentralSplitTorus.isSplitSubtorus.2
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology k A.X
  have hEmb : IsClosedEmbedding (rationalPoints.map a :
      rationalPoints A.toGrp → rationalPoints G) := isClosedEmbedding_rationalPointMap k a.hom.hom
  let C := RenardCartan.C0 A a
  let D₀ := (rationalPoints.map a).range
  let Z := Subgroup.center (rationalPoints G)
  have hCD₀ : C ≤ D₀ := by
    change RenardCartan.C0 A a ≤ _
    rw [RenardCartan.C0_eq_map_CA]
    exact Subgroup.map_le_range _ _
  have hD₀Z : D₀ ≤ Z := ha.isCentralSplitTorus.isCentral.range_le_center
  have hCZ : C ≤ Z := hCD₀.trans hD₀Z
  have : C.Normal := C.normal_of_le_center hCZ
  have hCclosed : IsClosed (C : Set (rationalPoints G)) := by
    change IsClosed (RenardCartan.C0 A a : Set (rationalPoints G))
    rw [RenardCartan.C0_eq_map_CA, Subgroup.coe_map]
    exact hEmb.isClosedMap _ (isClosed_uniformizerLattice k A hA)
  have hD₀closed : IsClosed (D₀ : Set (rationalPoints G)) := hEmb.isClosed_range
  let H := C.subgroupOf Z
  let D := D₀.subgroupOf Z
  have hHD : H ≤ D := fun z hz => hCD₀ hz
  have hZclosed : IsClosed (Z : Set (rationalPoints G)) := by
    simpa only [Z, Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set (rationalPoints G)))
  have : LocallyCompactSpace Z := hZclosed.locallyCompactSpace
  have : IsClosed (H : Set Z) := hCclosed.preimage continuous_subtype_val
  have : IsClosed (D : Set Z) := hD₀closed.preimage continuous_subtype_val
  have : CompactSpace (Z ⧸ D) :=
    HarishChandraSchwartz.compactSpace_center_quotient_splitComponent hG ha
  let q : (Z ⧸ H) →ₜ* (Z ⧸ D) :=
    { toMonoidHom := QuotientGroup.map H D (MonoidHom.id Z) hHD
      continuous_toFun := by
        apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
        exact QuotientGroup.continuous_mk }
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨QuotientGroup.mk z, rfl⟩
  have hopen : IsOpenMap q := by
    apply (QuotientGroup.isOpenQuotientMap_mk (N := H)).isOpenMap_iff.mpr
    exact QuotientGroup.isOpenMap_coe
  let f : rationalPoints A.toGrp →* Z :=
    (rationalPoints.map a).codRestrict Z fun x => hD₀Z ⟨x, rfl⟩
  let g : rationalPoints A.toGrp → (Z ⧸ H) := fun x => QuotientGroup.mk (f x)
  have hg : Continuous g :=
    QuotientGroup.continuous_mk.comp (hEmb.continuous.subtype_mk _)
  let U := rationalCommonNormKernel A.toGrp
  have hker : (q.ker : Set (Z ⧸ H)) = g '' (U : Set (rationalPoints A.toGrp)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      have hzD : z ∈ D := (QuotientGroup.eq_one_iff z).mp hz
      obtain ⟨x, hx⟩ := hzD
      have hfx : f x = z := Subtype.ext hx
      obtain ⟨c, hc, -⟩ := (isUniformizerLatticeSection k A hA).2.2 x
      let y := x * (latticeSection k A c)⁻¹
      have hxy : f y * f (latticeSection k A c) = z := by
        rw [← map_mul]
        simpa only [y, inv_mul_cancel_right] using hfx
      have hmem : f (latticeSection k A c) ∈ H := ⟨c, rfl⟩
      have hmk : (QuotientGroup.mk (f (latticeSection k A c)) : Z ⧸ H) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      refine ⟨y, hc, ?_⟩
      change QuotientGroup.mk (f y) = QuotientGroup.mk z
      rw [← hxy, QuotientGroup.mk_mul, hmk, mul_one]
    · rintro ⟨x, -, rfl⟩
      change (QuotientGroup.mk (f x) : Z ⧸ D) = 1
      exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  have hcompactKernel : IsCompact (q.ker : Set (Z ⧸ H)) := by
    rw [hker]
    exact (SplitTorus.isCompact_commonNormKernel hA).image hg
  have hproper := Langlands.compactKernelProperMap (Z ⧸ H) (Z ⧸ D) q hsurj hopen hcompactKernel
  have : CompactSpace (Z ⧸ H) :=
    ⟨by simpa using hproper.isCompact_preimage (isCompact_univ : IsCompact (Set.univ : Set (Z ⧸ D)))⟩
  refine ⟨hCclosed, inferInstance, ?_⟩
  intro _ _ _ _ μC _ μZ _ π
  exact (centralSubgroupCoefficientLpComparison (rationalPoints G) C hCZ hCclosed
    μC μZ _ π.representation).2

end Langlands.Aubert.General.RepresentedParabolic
