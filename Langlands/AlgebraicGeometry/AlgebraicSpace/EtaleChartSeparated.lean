import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartLocalSeparation
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalCompactnessProofs

/-!
# Separated spaces: Hausdorff and locally compact rational points

Over a henselian valued field `K`, the rational points of a separated, quasi-separated
algebraic space locally of finite type are Hausdorff for the étale-chart topology, and
locally compact when `K` is locally compact.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

section PairClosed

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))} {U V : Over (Spec (CommRingCat.of K))}
  (a : (schemeYoneda _).obj U ⟶ X.presheaf) (b : (schemeYoneda _).obj V ⟶ X.presheaf)

/-- If `X` is separated, the rational points of `U ×_X V` form a closed subspace of
`U(K) × V(K)`. -/
theorem isClosedEmbedding_pairPullback_points (hX : IsSeparated X) :
    @IsClosedEmbedding _ _ (schemePointTopology K (pairPullback a b) K)
      (@instTopologicalSpaceProd _ _ (schemePointTopology K U K) (schemePointTopology K V K))
      (fun w : RingPoint K (pairPullback a b) K =>
        ((w ≫ pairPullbackFst a b : RingPoint K U K), (w ≫ pairPullbackSnd a b : RingPoint K V K))) := by
  have := isClosedImmersion_pairPullbackLift a b hX
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  let : TopologicalSpace (RingPoint K (pairPullback a b) K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K (U ⊗ V) K) := schemePointTopology K (U ⊗ V) K
  have hιe := PointTopology.isClosedEmbedding_schemeClosedPointMap K K
    (lift (pairPullbackFst a b) (pairPullbackSnd a b))
  have k₃ : ∀ p : PointTopology.ringTest K K ⟶ pairPullback a b,
      (p ≫ lift (pairPullbackFst a b) (pairPullbackSnd a b)) ≫ fst U V =
        p ≫ pairPullbackFst a b := fun p => by
    rw [Category.assoc, lift_fst]
  have k₄ : ∀ p : PointTopology.ringTest K K ⟶ pairPullback a b,
      (p ≫ lift (pairPullbackFst a b) (pairPullbackSnd a b)) ≫ snd U V =
        p ≫ pairPullbackSnd a b := fun p => by
    rw [Category.assoc, lift_snd]
  have : (fun w : RingPoint K (pairPullback a b) K =>
      ((w ≫ pairPullbackFst a b : RingPoint K U K), (w ≫ pairPullbackSnd a b : RingPoint K V K))) =
      (PointTopology.schemeProductPointHomeomorph K K U V) ∘
        (fun w : RingPoint K (pairPullback a b) K =>
          (w ≫ lift (pairPullbackFst a b) (pairPullbackSnd a b) : RingPoint K (U ⊗ V) K)) := by
    funext w
    exact Prod.ext (k₃ w).symm (k₄ w).symm
  exact (congrArg (fun F : RingPoint K (pairPullback a b) K → RingPoint K U K × RingPoint K V K =>
    IsClosedEmbedding F) this).mpr
      ((PointTopology.schemeProductPointHomeomorph K K U V).isClosedEmbedding.comp hιe)

end PairClosed

/-- **Hausdorff**: over a henselian valued field, the rational points of a separated,
quasi-separated space locally of finite type are Hausdorff for the étale-chart topology. -/
theorem t2Space_etaleChartTopology (hK : IsHenselianValuedField K)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (hs : IsSeparated X) : @T2Space _ (etaleChartTopology K X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨c, u, rfl⟩ := hX.exists_chart x
  obtain ⟨d, v, rfl⟩ := hX.exists_chart y
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K (pairPullback (hom c.hom) (hom d.hom)) K) :=
    schemePointTopology K _ K
  let pairK : RingPoint K (pairPullback (hom c.hom) (hom d.hom)) K →
      RingPoint K c.scheme K × RingPoint K d.scheme K :=
    fun w => (w ≫ pairPullbackFst (hom c.hom) (hom d.hom),
      w ≫ pairPullbackSnd (hom c.hom) (hom d.hom))
  have hE : IsClosed (Set.range pairK) :=
    (isClosedEmbedding_pairPullback_points (hom c.hom) (hom d.hom) hs).isClosed_range
  have huv : (u, v) ∉ Set.range pairK := by
    rintro ⟨w, hw⟩
    apply hxy
    have h₁ : w ≫ pairPullbackFst (hom c.hom) (hom d.hom) = u := congrArg Prod.fst hw
    have h₂ : w ≫ pairPullbackSnd (hom c.hom) (hom d.hom) = v := congrArg Prod.snd hw
    rw [← h₁, ← h₂]
    exact schemePointsMap_pairPullbackFst (hom c.hom) (hom d.hom) w
  obtain ⟨N, M, hN, hM, hu, hv, hdisj⟩ := isOpen_prod_iff.1 hE.isOpen_compl u v huv
  refine ⟨c.pointMap '' N, d.pointMap '' M, c.isOpenMap_pointMap hK N hN,
    d.isOpenMap_pointMap hK M hM, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨n, hn, rfl⟩ ⟨m, hm, hmn⟩
  obtain ⟨w, hw₁, hw₂⟩ := exists_pairPullback_point (hom c.hom) (hom d.hom) hmn.symm
  exact hdisj ⟨hn, hm⟩ ⟨w, (Prod.ext hw₁ hw₂ : pairK w = (n, m))⟩

/-- **Locally compact**: over a locally compact henselian valued field, the rational points
of a quasi-separated space locally of finite type are locally compact for the étale-chart
topology. -/
theorem locallyCompactSpace_etaleChartTopology (hK : IsHenselianValuedField K)
    [LocallyCompactSpace K] {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : IsQuasiSeparatedLocallyFiniteType K X) :
    @LocallyCompactSpace _ (etaleChartTopology K X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  refine ⟨fun x n hn => ?_⟩
  obtain ⟨c, u, rfl⟩ := hX.exists_chart x
  have := c.locallyOfFiniteType
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  have : LocallyCompactSpace (RingPoint K c.scheme K) :=
    PointTopology.schemePointLocalCompactness_proof K K c.scheme
  obtain ⟨s, hs, hsn, hsc⟩ := local_compact_nhds (c.continuous_pointMap.continuousAt hn)
  exact ⟨c.pointMap '' s, (c.isOpenMap_pointMap hK).image_mem_nhds hs,
    Set.image_subset_iff.2 hsn, hsc.image c.continuous_pointMap⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
