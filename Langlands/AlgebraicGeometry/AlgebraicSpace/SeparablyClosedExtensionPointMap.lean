import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionPointMap
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Points over relatively separably closed normed extensions

The coefficient-extension map identifies rational points homeomorphically with
its range when the base field is separably closed in the extension and the
extension field is henselian. This generalizes the rational-fibre step in the
published completion-embedding proof.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest schemePointTopology IsHenselianValuedField
    ringBaseChange ringPointBaseChangeEquiv isEmbedding_schemeChangeRing
    exists_changeRing_eq_of_formallyUnramified)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]
  (L : Type u) [NontriviallyNormedField L] [NormedAlgebra K L]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- An extension-valued point of an étale scheme chart lying over a rational
point is rational if `K` is separably closed in `L`. -/
theorem exists_rational_of_separablyClosed_extension
    (hsep : separableClosure K L = ⊥)
    {U V : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (b : (schemeYoneda _).obj V ⟶ X.presheaf)
    (ha : IsEtale a) (η : RingPoint K U L) (v : RingPoint K V K)
    (h : a.app (op (ringTest K L)) (ULift.up η) =
      b.app (op (ringTest K L))
        (ULift.up (RingPoint.changeRing (Algebra.ofId K L) v))) :
    ∃ u : RingPoint K U K, RingPoint.changeRing (Algebra.ofId K L) u = η ∧
      schemePointsMap a u = schemePointsMap b v := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a b)
    (ringTest K L) (ULift.up η) (ULift.up _) h
  let w : RingPoint K (pairPullback a b) L := p.down
  have hw₁ : w ≫ pairPullbackFst a b = η := congrArg ULift.down hp₁
  have hw₂ : w ≫ pairPullbackSnd a b =
      RingPoint.changeRing (Algebra.ofId K L) v := congrArg ULift.down hp₂
  have := etale_pairPullbackSnd a b ha
  obtain ⟨w₀, hw₀⟩ :=
    exists_changeRing_eq_of_formallyUnramified K L hsep (pairPullbackSnd a b) w v hw₂
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  let : TopologicalSpace (RingPoint K V L) := schemePointTopology K V L
  have hι : IsEmbedding (Algebra.ofId K L) := (algebraMap_isometry K L).isEmbedding
  have hinjV := (isEmbedding_schemeChangeRing K K L V (Algebra.ofId K L) hι).injective
  have hv : w₀ ≫ pairPullbackSnd a b = v := by
    apply hinjV
    change RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₂]
  refine ⟨w₀ ≫ pairPullbackFst a b, ?_, ?_⟩
  · change RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₁]
  · rw [schemePointsMap_pairPullbackFst, hv]

/-- Over a relatively separably closed normed extension with henselian target,
coefficient extension embeds rational points of every quasi-separated space
locally of finite type, without a separation hypothesis. -/
theorem isEmbedding_extensionPointMap_of_separablyClosed
    (hL : IsHenselianValuedField L) (hsep : separableClosure K L = ⊥)
    (hqs : IsQuasiSeparated X) (hlft : LocallyOfFiniteTypeOverBase X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (extensionPointMap L X) := by
  let : ∀ U : Over (Spec (CommRingCat.of K)), TopologicalSpace (RingPoint K U K) :=
    fun U => schemePointTopology K U K
  let : ∀ U : Over (Spec (CommRingCat.of L)), TopologicalSpace (RingPoint L U L) :=
    fun U => schemePointTopology L U L
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  have hcov := exists_chart_pointMap_eq hqs hlft
  have hopen : ∀ c : EtaleFiniteTypeChart K X,
      IsOpenMap (c.extension L).pointMap := fun c =>
    (c.extension L).isOpenMap_pointMap hL
  have hcomm := fun (c : EtaleFiniteTypeChart K X) => extensionPointMap_pointMap L c
  have hrat : ∀ (c : EtaleFiniteTypeChart K X)
      (η : RingPoint L (c.extension L).scheme L) (y : RingPoints K X K),
      (c.extension L).pointMap η = extensionPointMap L X y →
        ∃ u : RingPoint K c.scheme K, extensionSchemePointMap L c.scheme u = η ∧
          c.pointMap u = y := by
    intro c η y h
    obtain ⟨d, v, rfl⟩ := hcov y
    have h' := congrArg (baseChangeRingPointsEquiv K L L X) h
    rw [baseChangeRingPointsEquiv_extension_pointMap, extensionPointMap,
      Equiv.apply_symm_apply, EtaleFiniteTypeChart.pointMap, RingPoints.changeRing_map] at h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_rational_of_separablyClosed_extension L hsep
      (hom c.hom) (hom d.hom) c.isEtale _ v h'
    refine ⟨u, ?_, hu₂⟩
    rw [extensionSchemePointMap, hu₁, Equiv.apply_symm_apply]
  have hinj : Function.Injective (extensionPointMap L X) := by
    intro x y h
    obtain ⟨c, u, rfl⟩ := hcov x
    rw [hcomm] at h
    obtain ⟨u', hu'₁, hu'₂⟩ := hrat c _ y h
    rw [← hu'₂, (isEmbedding_extensionSchemePointMap L c.scheme).injective hu'₁]
  refine ⟨⟨le_antisymm
    (continuous_iff_le_induced.mp (continuous_extensionPointMap L)) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hWc : ∀ c : EtaleFiniteTypeChart K X,
      ∃ t : Set (RingPoint L (c.extension L).scheme L), IsOpen t ∧
        extensionSchemePointMap L c.scheme ⁻¹' t = c.pointMap ⁻¹' W := fun c =>
    (isEmbedding_extensionSchemePointMap L c.scheme).isInducing.isOpen_iff.mp
      ((etaleChartTopology_isOpen_iff X W).mp hW c)
  choose t ht hte using hWc
  refine isOpen_induced_iff.mpr ⟨⋃ c, (c.extension L).pointMap '' t c,
    isOpen_iUnion fun c => hopen c _ (ht c), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨c, η, hηt, hη⟩
    obtain ⟨u, rfl, rfl⟩ := hrat c η y hη
    have hu : u ∈ extensionSchemePointMap L c.scheme ⁻¹' t c := hηt
    rw [hte c] at hu
    exact hu
  · intro hy
    obtain ⟨c, u, rfl⟩ := hcov y
    refine ⟨c, extensionSchemePointMap L c.scheme u, ?_, (hcomm c u).symm⟩
    change u ∈ extensionSchemePointMap L c.scheme ⁻¹' t c
    rw [hte c]
    exact hy

/-- The homeomorphism onto the image for a relatively separably closed normed
extension with henselian target. -/
def separablyClosedExtensionPointHomeomorphRange
    (hL : IsHenselianValuedField L) (hsep : separableClosure K L = ⊥)
    (hqs : IsQuasiSeparated X) (hlft : LocallyOfFiniteTypeOverBase X) :
    letI : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
    letI : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
      etaleChartTopology L _
    RingPoints K X K ≃ₜ Set.range (extensionPointMap L X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  exact (isEmbedding_extensionPointMap_of_separablyClosed L hL hsep hqs hlft).toHomeomorph

end Langlands.AlgebraicGeometry.AlgebraicSpace
