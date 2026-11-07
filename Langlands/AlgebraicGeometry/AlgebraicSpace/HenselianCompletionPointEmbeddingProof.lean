import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianCompletionPointEmbeddingStatement
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof

/-!
# Rational points over a henselian field embed into points over its completion

Conrad's Proposition 5.11(2) (printed p.18): for a quasi-separated algebraic space `X`
locally of finite type over a henselian valued field `K`, the natural map
`X(K) → X_{K̂}(K̂)` is a topological embedding for the étale-chart topologies.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest schemePointTopology IsHenselianValuedField schemePointContinuity_proof
    ringBaseChange ringPointBaseChangeEquiv schemeBaseChangeTopology_proof
    isEmbedding_schemeChangeRing exists_changeRing_eq_of_formallyUnramified
    separableClosure_completion_eq_bot completionNontriviallyNormedField
    isOpenMap_smoothSchemePointMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section OpenOfEtaleOpen

variable {K : Type u} [NontriviallyNormedField K]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- If étale maps of schemes locally of finite type over `K` are open on rational points,
then so is every étale map `h_U → X` from such a scheme, for the étale-chart topology. -/
theorem isOpenMap_schemePointsMap_of_etaleOpen
    (hopen : ∀ (Y Z : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType Z.hom] (f : Y ⟶ Z) [Etale f.left],
      @IsOpenMap _ _ (schemePointTopology K Y K) (schemePointTopology K Z K)
        (fun p : RingPoint K Y K => (p ≫ f : RingPoint K Z K)))
    {U : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    @IsOpenMap _ _ (schemePointTopology K U K) (etaleChartTopology K X)
      (schemePointsMap a) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  intro V hV
  rw [etaleChartTopology_isOpen_iff]
  intro d
  let : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K d.scheme K
  let : TopologicalSpace (RingPoint K (pairPullback a (hom d.hom)) K) :=
    schemePointTopology K _ K
  have e : d.pointMap ⁻¹' (schemePointsMap a '' V) = _ :=
    preimage_image_schemePointsMap a (hom d.hom) V
  rw [e]
  have := locallyOfFiniteType_pairPullback a (hom d.hom) d.isEtale
  have := d.locallyOfFiniteType
  have := etale_pairPullbackSnd a (hom d.hom) ha
  exact hopen _ _ (pairPullbackSnd a (hom d.hom)) _
    (hV.preimage (schemePointContinuity_proof K K _ _ (pairPullbackFst a (hom d.hom))))

/-- Over a complete field, every étale chart map is open for the étale-chart topology. -/
theorem isOpenMap_schemePointsMap_of_complete [CompleteSpace K]
    {U : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    @IsOpenMap _ _ (schemePointTopology K U K) (etaleChartTopology K X)
      (schemePointsMap a) :=
  isOpenMap_schemePointsMap_of_etaleOpen
    (fun _ _ _ _ f _ => isOpenMap_smoothSchemePointMap K f) a ha

end OpenOfEtaleOpen

section Completion

variable (K : Type u) [NontriviallyNormedField K]

local notation "K̂" => UniformSpace.Completion K

variable {K} {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- The base change to the completion of an étale chart of finite type. -/
abbrev EtaleFiniteTypeChart.completion (c : EtaleFiniteTypeChart K X) :
    EtaleFiniteTypeChart K̂ (baseChange (Spec.algebraMap K K̂) X) where
  scheme := ringBaseChange K K̂ c.scheme
  hom := homMk (restrictAtlas (Spec.algebraMap K K̂) (AlgebraicSpace.hom c.hom))
  isEtale := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h := c.isEtale
    unfold IsEtale at h ⊢
    exact relative_restrictAtlas (g := Spec.algebraMap K K̂) (@Etale.{u}) h
  locallyOfFiniteType := by
    have := c.locallyOfFiniteType
    change LocallyOfFiniteType (pullback.snd c.scheme.hom (Spec.algebraMap K K̂))
    infer_instance
  quasiCompact := by
    have := c.quasiCompact
    change QuasiCompact (pullback.snd c.scheme.hom (Spec.algebraMap K K̂))
    infer_instance

/-- The chart map of the base-changed chart, read on `K̂`-valued points of `X`. -/
theorem baseChangeRingPointsEquiv_completion_pointMap (c : EtaleFiniteTypeChart K X)
    (p : RingPoint K̂ (ringBaseChange K K̂ c.scheme) K̂) :
    baseChangeRingPointsEquiv K K̂ K̂ X (c.completion.pointMap p) =
      RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme K̂).symm
        ((ringPointBaseChangeEquiv K K̂ K̂ c.scheme).symm p)) := by
  rw [baseChangeRingPointsEquiv_apply]
  refine (mapSections_naturality c.hom
    (PointTopology.ringTestRestrictScalarsIso K K̂ K̂).inv _).trans ?_
  change mapSections c.hom _ (ULift.up _) = mapSections c.hom _ (ULift.up _)
  congr 2

/-- The coefficient change `U(K) → U_{K̂}(K̂)` of scheme points. -/
def completionSchemePointMap (U : Over (Spec (CommRingCat.of K))) :
    RingPoint K U K → RingPoint K̂ (ringBaseChange K K̂ U) K̂ :=
  fun u => ringPointBaseChangeEquiv K K̂ K̂ U (RingPoint.changeRing (Algebra.ofId K K̂) u)

/-- The coefficient change of scheme points to the completion is a topological
embedding. -/
theorem isEmbedding_completionSchemePointMap (U : Over (Spec (CommRingCat.of K))) :
    @IsEmbedding _ _ (schemePointTopology K U K)
      (schemePointTopology K̂ (ringBaseChange K K̂ U) K̂) (completionSchemePointMap U) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K U K̂) := schemePointTopology K U K̂
  let : TopologicalSpace (RingPoint K̂ (ringBaseChange K K̂ U) K̂) :=
    schemePointTopology K̂ (ringBaseChange K K̂ U) K̂
  have hι : IsEmbedding (Algebra.ofId K K̂) :=
    (UniformSpace.Completion.isUniformEmbedding_coe K).isEmbedding
  exact (schemeBaseChangeTopology_proof K K̂ K̂ U).isEmbedding.comp
    (isEmbedding_schemeChangeRing K K K̂ U (Algebra.ofId K K̂) hι)

/-- The natural map `X(K) → X_{K̂}(K̂)`. -/
def completionPointMap (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    RingPoints K X K → RingPoints K̂ (baseChange (Spec.algebraMap K K̂) X) K̂ :=
  fun x => (baseChangeRingPointsEquiv K K̂ K̂ X).symm
    (RingPoints.changeRing (Algebra.ofId K K̂) x)

/-- The natural map commutes with chart maps and their base changes. -/
theorem completionPointMap_pointMap (c : EtaleFiniteTypeChart K X) (u : RingPoint K c.scheme K) :
    completionPointMap X (c.pointMap u) =
      c.completion.pointMap (completionSchemePointMap c.scheme u) := by
  apply (baseChangeRingPointsEquiv K K̂ K̂ X).injective
  rw [completionPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_completion_pointMap,
    completionSchemePointMap, Equiv.symm_apply_apply, EtaleFiniteTypeChart.pointMap,
    RingPoints.changeRing_map]
  rfl

/-- **Rationality of completed points over a rational point.** If a `K̂`-valued point
`η` of `U` and a rational point `v` of `V` have the same image in `X(K̂)`, where
`a : h_U → X` is étale, then `η` is rational and maps to the image of `v` in `X(K)`. -/
theorem exists_rational_of_completion (hK : IsHenselianValuedField K)
    {U V : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (b : (schemeYoneda _).obj V ⟶ X.presheaf)
    (ha : IsEtale a) (η : RingPoint K U K̂) (v : RingPoint K V K)
    (h : a.app (op (ringTest K K̂)) (ULift.up η) =
      b.app (op (ringTest K K̂)) (ULift.up (RingPoint.changeRing (Algebra.ofId K K̂) v))) :
    ∃ u : RingPoint K U K, RingPoint.changeRing (Algebra.ofId K K̂) u = η ∧
      schemePointsMap a u = schemePointsMap b v := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a b)
    (ringTest K K̂) (ULift.up η) (ULift.up _) h
  let w : RingPoint K (pairPullback a b) K̂ := p.down
  have hw₁ : w ≫ pairPullbackFst a b = η := congrArg ULift.down hp₁
  have hw₂ : w ≫ pairPullbackSnd a b = RingPoint.changeRing (Algebra.ofId K K̂) v :=
    congrArg ULift.down hp₂
  have := etale_pairPullbackSnd a b ha
  have hsep := separableClosure_completion_eq_bot K hK
  obtain ⟨w₀, hw₀⟩ :=
    exists_changeRing_eq_of_formallyUnramified K K̂ hsep (pairPullbackSnd a b) w v hw₂
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K U K̂) := schemePointTopology K U K̂
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  let : TopologicalSpace (RingPoint K V K̂) := schemePointTopology K V K̂
  have hι : IsEmbedding (Algebra.ofId K K̂) :=
    (UniformSpace.Completion.isUniformEmbedding_coe K).isEmbedding
  have hinjV := (isEmbedding_schemeChangeRing K K K̂ V (Algebra.ofId K K̂) hι).injective
  have hv : w₀ ≫ pairPullbackSnd a b = v := by
    apply hinjV
    change RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₂]
  refine ⟨w₀ ≫ pairPullbackFst a b, ?_, ?_⟩
  · change RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₁]
  · rw [schemePointsMap_pairPullbackFst, hv]

end Completion

/-- **Conrad's Proposition 5.11(2).** Over a henselian valued field `K`, the natural map
`X(K) → X_{K̂}(K̂)` is a topological embedding for every quasi-separated algebraic space
`X` locally of finite type. -/
theorem henselianCompletionPointEmbedding : HenselianCompletionPointEmbeddingStatement.{u} := by
  intro K _ hK X hX
  obtain ⟨hqs, hlft⟩ := hX
  let : ∀ U : Over (Spec (CommRingCat.of K)), TopologicalSpace (RingPoint K U K) :=
    fun U => schemePointTopology K U K
  let : ∀ U : Over (Spec (CommRingCat.of (UniformSpace.Completion K))),
      TopologicalSpace (RingPoint _ U (UniformSpace.Completion K)) :=
    fun U => schemePointTopology _ U _
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace
      (RingPoints (UniformSpace.Completion K)
        (baseChange (Spec.algebraMap K (UniformSpace.Completion K)) X)
        (UniformSpace.Completion K)) :=
    etaleChartTopology (UniformSpace.Completion K) _
  change IsEmbedding (completionPointMap X)
  have hcov := exists_chart_pointMap_eq hqs hlft
  -- Base-changed chart maps are open over the complete field `K̂`.
  have hopen : ∀ c : EtaleFiniteTypeChart K X,
      @IsOpenMap _ _ (schemePointTopology _ c.completion.scheme _)
        (etaleChartTopology _ _) c.completion.pointMap := by
    intro c
    let := completionNontriviallyNormedField K
    have := c.completion.locallyOfFiniteType
    exact isOpenMap_schemePointsMap_of_complete _ c.completion.isEtale
  -- The chart maps over `K` and over `K̂` are compatible.
  have hcomm := fun (c : EtaleFiniteTypeChart K X) => completionPointMap_pointMap c
  -- Completed points of a base-changed chart over a rational point are rational.
  have hrat : ∀ (c : EtaleFiniteTypeChart K X)
      (η : RingPoint _ c.completion.scheme (UniformSpace.Completion K)) (y : RingPoints K X K),
      c.completion.pointMap η = completionPointMap X y →
        ∃ u : RingPoint K c.scheme K, completionSchemePointMap c.scheme u = η ∧
          c.pointMap u = y := by
    intro c η y h
    obtain ⟨d, v, rfl⟩ := hcov y
    have := c.locallyOfFiniteType
    have h' := congrArg (baseChangeRingPointsEquiv K _ _ X) h
    rw [baseChangeRingPointsEquiv_completion_pointMap, completionPointMap,
      Equiv.apply_symm_apply, EtaleFiniteTypeChart.pointMap, RingPoints.changeRing_map] at h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_rational_of_completion hK (hom c.hom) (hom d.hom) c.isEtale
      _ v h'
    refine ⟨u, ?_, hu₂⟩
    rw [completionSchemePointMap, hu₁, Equiv.apply_symm_apply]
  have hinj : Function.Injective (completionPointMap X) := by
    intro x y h
    obtain ⟨c, u, rfl⟩ := hcov x
    rw [hcomm] at h
    obtain ⟨u', hu'₁, hu'₂⟩ := hrat c _ y h
    rw [← hu'₂, (isEmbedding_completionSchemePointMap c.scheme).injective hu'₁]
  have hcont : Continuous (completionPointMap X) := by
    rw [etaleChartTopology_continuous_iff]
    intro c
    have : completionPointMap X ∘ c.pointMap =
        c.completion.pointMap ∘ completionSchemePointMap c.scheme := funext (hcomm c)
    rw [this]
    exact c.completion.continuous_pointMap.comp
      (isEmbedding_completionSchemePointMap c.scheme).continuous
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hWc : ∀ c : EtaleFiniteTypeChart K X,
      ∃ t : Set (RingPoint _ c.completion.scheme (UniformSpace.Completion K)),
        IsOpen[schemePointTopology _ c.completion.scheme _] t ∧
          completionSchemePointMap c.scheme ⁻¹' t = c.pointMap ⁻¹' W := fun c =>
    (isEmbedding_completionSchemePointMap c.scheme).isInducing.isOpen_iff.mp
      ((etaleChartTopology_isOpen_iff X W).mp hW c)
  choose t ht hte using hWc
  refine isOpen_induced_iff.mpr ⟨⋃ c, c.completion.pointMap '' t c,
    isOpen_iUnion fun c => hopen c _ (ht c), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨c, η, hηt, hη⟩
    obtain ⟨u, rfl, rfl⟩ := hrat c η y hη
    have hu : u ∈ completionSchemePointMap c.scheme ⁻¹' t c := hηt
    rw [hte c] at hu
    exact hu
  · intro hy
    obtain ⟨c, u, rfl⟩ := hcov y
    refine ⟨c, completionSchemePointMap c.scheme u, ?_, (hcomm c u).symm⟩
    change u ∈ completionSchemePointMap c.scheme ⁻¹' t c
    rw [hte c]
    exact hy

end Langlands.AlgebraicGeometry.AlgebraicSpace
