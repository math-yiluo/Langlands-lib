import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.PointTopology.SchemeClosedPointProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-!
# Functoriality and immersions for the étale-chart topology

Over a henselian valued field, the étale-chart topology on rational points of
quasi-separated algebraic spaces locally of finite type is functorial, agrees with the
scheme topology on schemes, and carries open immersions, closed immersions and étale
morphisms to open embeddings, closed embeddings and open maps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField schemePointContinuity_proof
    henselianEtalePointLocalHomeomorph)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- Rational points of quasi-separated spaces locally of finite type are covered by
charts. -/
theorem IsQuasiSeparatedLocallyFiniteType.exists_chart
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (x : RingPoints K X K) :
    ∃ (d : EtaleFiniteTypeChart K X) (y : RingPoint K d.scheme K), d.pointMap y = x :=
  exists_chart_pointMap_eq hX.1 hX.2 x

/-- **Functoriality**: a morphism to a quasi-separated space locally of finite type induces
a continuous map on rational points. -/
theorem continuous_ringPointsMap (hK : IsHenselianValuedField K)
    {X Y : AlgebraicSpace (Spec (CommRingCat.of K))} (hY : IsQuasiSeparatedLocallyFiniteType K Y)
    (f : X ⟶ Y) :
    @Continuous _ _ (etaleChartTopology K X) (etaleChartTopology K Y)
      (RingPoints.map (A := K) f) := by
  let : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  rw [etaleChartTopology_continuous_iff]
  intro c
  have := c.locallyOfFiniteType
  exact continuous_schemePointsMap hK hY.exists_chart (hom c.hom ≫ hom f)

/-- **The case of schemes**: on a scheme locally of finite type, the étale-chart topology is
the scheme point topology. -/
theorem isHomeomorph_schemeRingPointsEquiv (hK : IsHenselianValuedField K)
    (U : Over (Spec (CommRingCat.of K)))
    (hU : IsQuasiSeparatedLocallyFiniteType K ((schemeToSpace _).obj U)) :
    @IsHomeomorph _ _ (etaleChartTopology K ((schemeToSpace _).obj U))
      (schemePointTopology K U K) (schemeRingPointsEquiv K U K) := by
  let : TopologicalSpace (RingPoints K ((schemeToSpace _).obj U) K) :=
    etaleChartTopology K ((schemeToSpace _).obj U)
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  have : LocallyOfFiniteType U.hom := (locallyOfFiniteTypeOverBase_schemeToSpace_iff U).mp hU.2
  have h₁ : Continuous (schemeRingPointsEquiv K U K) := by
    rw [etaleChartTopology_continuous_iff]
    intro c
    obtain ⟨g, hg⟩ := (schemeYoneda _).map_surjective (hom c.hom)
    have : (schemeRingPointsEquiv K U K ∘ c.pointMap) = fun x => x ≫ g := by
      funext x
      change ((hom c.hom).app _ (ULift.up x)).down = x ≫ g
      rw [← hg]
      rfl
    rw [this]
    exact schemePointContinuity_proof K K _ _ g
  have h₂ : Continuous (schemeRingPointsEquiv K U K).symm :=
    continuous_schemePointsMap hK hU.exists_chart
      (𝟙 _ : (schemeYoneda _).obj U ⟶ ((schemeToSpace _).obj U).presheaf)
  exact (Homeomorph.mk (schemeRingPointsEquiv K U K) h₁ h₂).isHomeomorph

section SpacePullback

variable {X X' : AlgebraicSpace (Spec (CommRingCat.of K))} (f : X' ⟶ X)
  (hf : IsRepresentableMorphism (hom f)) {U : Over (Spec (CommRingCat.of K))}
  (a : (schemeYoneda _).obj U ⟶ X.presheaf)

/-- Points of a represented pullback of `f` along `a` map compatibly. -/
theorem map_schemePointsMap_fst (w : RingPoint K (hf.pullback a) K) :
    RingPoints.map f (schemePointsMap (hf.fst a) w) = schemePointsMap a (w ≫ hf.snd a) :=
  congrArg (fun φ => φ.app (op (PointTopology.ringTest K K)) (ULift.up w)) (hf.isPullback a).w

/-- A point of `X'` and a point of `U` with the same image in `X` come from a point of the
represented pullback. -/
theorem exists_pullback_point {x' : RingPoints K X' K} {y : RingPoint K U K}
    (h : RingPoints.map f x' = schemePointsMap a y) :
    ∃ w : RingPoint K (hf.pullback a) K, schemePointsMap (hf.fst a) w = x' ∧ w ≫ hf.snd a = y := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (hf.isPullback a)
    (PointTopology.ringTest K K) x' (ULift.up y) h
  exact ⟨p.down, hp₁, congrArg ULift.down hp₂⟩

/-- The preimage under `a` of the image of a set of points of `X'`. -/
theorem preimage_image_ringPointsMap (O : Set (RingPoints K X' K)) :
    schemePointsMap a ⁻¹' (RingPoints.map f '' O) =
      (fun w : RingPoint K (hf.pullback a) K => w ≫ hf.snd a) ''
        (schemePointsMap (hf.fst a) ⁻¹' O) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨w, hw₁, hw₂⟩ := exists_pullback_point f hf a hxy
    exact ⟨w, (congrArg (· ∈ O) hw₁).mpr hx, hw₂⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw, map_schemePointsMap_fst f hf a w⟩

end SpacePullback

/-- A representable morphism whose represented projections are monomorphisms is injective on
rational points. -/
theorem injective_ringPointsMap_of_mono {X X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (f : X' ⟶ X) (hf : IsRepresentableMorphism (hom f))
    (hmono : ∀ {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf),
      Mono (hf.snd a)) :
    Function.Injective (RingPoints.map (A := K) f) := by
  intro x₁ x₂ h
  let a : (schemeYoneda _).obj (PointTopology.ringTest K K) ⟶ X.presheaf :=
    uliftYonedaEquiv.{u + 1}.symm (RingPoints.map f x₂)
  have ha : schemePointsMap a (𝟙 _) = RingPoints.map f x₂ := uliftYonedaEquiv.{u + 1}.apply_symm_apply _
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_pullback_point f hf a (h.trans ha.symm)
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_pullback_point f hf a ha.symm
  have : w₁ = w₂ := (cancel_mono (hf.snd a)).mp (hw₁'.trans hw₂'.symm)
  rw [← hw₁, ← hw₂, this]

/-- A set of rational points is closed exactly when its preimage in every chart is
closed. -/
theorem etaleChartTopology_isClosed_iff (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (C : Set (RingPoints K X K)) :
    IsClosed[etaleChartTopology K X] C ↔
      ∀ c : EtaleFiniteTypeChart K X,
        IsClosed[schemePointTopology K c.scheme K] (c.pointMap ⁻¹' C) := by
  simp only [← isOpen_compl_iff, etaleChartTopology_isOpen_iff, Set.preimage_compl]

/-- **Open immersions** induce open embeddings on rational points. -/
theorem isOpenEmbedding_ringPointsMap (hK : IsHenselianValuedField K)
    {X X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX' : IsQuasiSeparatedLocallyFiniteType K X') (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (f : X' ⟶ X) (hf : IsOpenImmersion (hom f)) :
    @IsOpenEmbedding _ _ (etaleChartTopology K X') (etaleChartTopology K X)
      (RingPoints.map (A := K) f) := by
  let : TopologicalSpace (RingPoints K X' K) := etaleChartTopology K X'
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  have hr : IsRepresentableMorphism (hom f) := hf.1
  have hproj : ∀ {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf),
      _root_.AlgebraicGeometry.IsOpenImmersion (hr.snd a).left :=
    fun a => hf.2 a _ _ (hr.isPullback a)
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_ringPointsMap hK hX f)
    (injective_ringPointsMap_of_mono f hr fun a => ?_) ?_
  · have := hproj a
    exact Over.mono_of_mono_left _
  · intro O hO
    rw [etaleChartTopology_isOpen_iff]
    intro c
    let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
    let : TopologicalSpace (RingPoint K (hr.pullback (hom c.hom)) K) := schemePointTopology K _ K
    have e : c.pointMap ⁻¹' (RingPoints.map f '' O) = _ :=
      preimage_image_ringPointsMap f hr (hom c.hom) O
    rw [e]
    have := hproj (hom c.hom)
    have := c.locallyOfFiniteType
    have : LocallyOfFiniteType (hr.pullback (hom c.hom)).hom := by
      rw [← Over.w (hr.snd (hom c.hom))]
      infer_instance
    exact (PointTopology.isOpenEmbedding_schemePointMap K K (hr.snd (hom c.hom))).isOpenMap _
      (hO.preimage (continuous_schemePointsMap hK hX'.exists_chart (hr.fst (hom c.hom))))

/-- **Closed immersions** induce closed embeddings on rational points. -/
theorem isClosedEmbedding_ringPointsMap (hK : IsHenselianValuedField K)
    {X X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX' : IsQuasiSeparatedLocallyFiniteType K X') (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (f : X' ⟶ X) (hf : IsClosedImmersion (hom f)) :
    @IsClosedEmbedding _ _ (etaleChartTopology K X') (etaleChartTopology K X)
      (RingPoints.map (A := K) f) := by
  let : TopologicalSpace (RingPoints K X' K) := etaleChartTopology K X'
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  have hr : IsRepresentableMorphism (hom f) := hf.1
  have hproj : ∀ {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf),
      _root_.AlgebraicGeometry.IsClosedImmersion (hr.snd a).left :=
    fun a => hf.2 a _ _ (hr.isPullback a)
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_ringPointsMap hK hX f) (injective_ringPointsMap_of_mono f hr fun a => ?_) ?_
  · have := hproj a
    exact Over.mono_of_mono_left _
  · intro C hC
    rw [etaleChartTopology_isClosed_iff]
    intro c
    let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
    let : TopologicalSpace (RingPoint K (hr.pullback (hom c.hom)) K) := schemePointTopology K _ K
    have e : c.pointMap ⁻¹' (RingPoints.map f '' C) = _ :=
      preimage_image_ringPointsMap f hr (hom c.hom) C
    rw [e]
    have := hproj (hom c.hom)
    have := c.locallyOfFiniteType
    have : LocallyOfFiniteType (hr.pullback (hom c.hom)).hom := by
      rw [← Over.w (hr.snd (hom c.hom))]
      infer_instance
    exact (PointTopology.isClosedEmbedding_schemeClosedPointMap K K
      (hr.snd (hom c.hom))).isClosedMap _
      (hC.preimage (continuous_schemePointsMap hK hX'.exists_chart (hr.fst (hom c.hom))))

/-- **Étale morphisms** induce open maps on rational points. -/
theorem isOpenMap_ringPointsMap_of_isEtaleMorphism (hK : IsHenselianValuedField K)
    {X X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX' : IsQuasiSeparatedLocallyFiniteType K X') (f : X' ⟶ X) (hf : IsEtaleMorphism f) :
    @IsOpenMap _ _ (etaleChartTopology K X') (etaleChartTopology K X)
      (RingPoints.map (A := K) f) := by
  intro O hO
  have hO' := (etaleChartTopology_isOpen_iff X' O).1 hO
  have : RingPoints.map f '' O = ⋃ c : EtaleFiniteTypeChart K X',
      schemePointsMap (hom c.hom ≫ hom f) '' (c.pointMap ⁻¹' O) := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      obtain ⟨c, y, rfl⟩ := hX'.exists_chart x'
      exact Set.mem_iUnion.2 ⟨c, y, hx', rfl⟩
    · intro hx
      obtain ⟨c, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      exact ⟨c.pointMap y, hy, rfl⟩
  rw [this]
  refine @isOpen_iUnion _ _ (etaleChartTopology K X) _ fun c => ?_
  have := c.locallyOfFiniteType
  exact isOpenMap_schemePointsMap hK _ (hf c.scheme (hom c.hom) c.isEtale) _ (hO' c)

end Langlands.AlgebraicGeometry.AlgebraicSpace
