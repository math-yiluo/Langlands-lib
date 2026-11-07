import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.PointTopology.SchemeProducts

/-!
# Local separatedness and the étale-chart topology

For a locally separated algebraic space `X` over a henselian valued field `K` and maps
`a : h_U → X`, `b : h_V → X` from schemes, the rational points of the represented
pullback `U ×_X V` embed into `U(K) × V(K)`. Consequently étale maps from schemes are
locally injective on rational points, and étale morphisms of quasi-separated, locally
separated spaces locally of finite type induce local homeomorphisms.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField schemePointContinuity_proof
    openOver openOverι)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A section of an étale morphism of schemes is an open immersion. -/
theorem isOpenImmersion_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) : _root_.AlgebraicGeometry.IsOpenImmersion s := by
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.lift (𝟙 Y) s (by simp) : Y ⟶ Limits.pullback (s ≫ f) f) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion)
      (pullback_lift_diagonal_isPullback s f) inferInstance
  have : IsIso (s ≫ f) := hs ▸ inferInstance
  rw [← Limits.pullback.lift_snd (f := s ≫ f) (g := f) (𝟙 Y) s (by simp)]
  infer_instance

variable {K : Type u} [NontriviallyNormedField K]

/-- An immersion of schemes induces an embedding on rational points. -/
theorem isEmbedding_schemePointMap_of_isImmersion {W T : Over (Spec (CommRingCat.of K))}
    (f : W ⟶ T) [IsImmersion f.left] :
    @IsEmbedding _ _ (schemePointTopology K W K) (schemePointTopology K T K)
      (fun p : RingPoint K W K => (p ≫ f : RingPoint K T K)) := by
  let O := f.left.coborderRange
  let g : W ⟶ openOver K T O := Over.homMk f.left.liftCoborder (by
    change f.left.liftCoborder ≫ O.ι ≫ T.hom = W.hom
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, Over.w f])
  have hg : g ≫ openOverι K T O = f := by
    ext1
    exact f.left.liftCoborder_ι
  have : _root_.AlgebraicGeometry.IsClosedImmersion g.left := by
    change _root_.AlgebraicGeometry.IsClosedImmersion f.left.liftCoborder
    infer_instance
  have : _root_.AlgebraicGeometry.IsOpenImmersion (openOverι K T O).left := by
    change _root_.AlgebraicGeometry.IsOpenImmersion O.ι
    infer_instance
  let : TopologicalSpace (RingPoint K W K) := schemePointTopology K W K
  let : TopologicalSpace (RingPoint K T K) := schemePointTopology K T K
  let : TopologicalSpace (RingPoint K (openOver K T O) K) := schemePointTopology K _ K
  have h₁ := PointTopology.isEmbedding_schemeClosedPointMap K K g
  have h₂ := (PointTopology.isOpenEmbedding_schemePointMap K K (openOverι K T O)).isEmbedding
  have key : ∀ p : PointTopology.ringTest K K ⟶ W, p ≫ f = (p ≫ g) ≫ openOverι K T O :=
    fun p => by rw [Category.assoc, hg]
  have : (fun p : RingPoint K W K => (p ≫ f : RingPoint K T K)) =
      (fun q : RingPoint K (openOver K T O) K => (q ≫ openOverι K T O : RingPoint K T K)) ∘
        (fun p : RingPoint K W K => (p ≫ g : RingPoint K (openOver K T O) K)) :=
    funext key
  rw [this]
  exact h₂.comp h₁

section PairEmbedding

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))} {U V : Over (Spec (CommRingCat.of K))}
  (a : (schemeYoneda _).obj U ⟶ X.presheaf) (b : (schemeYoneda _).obj V ⟶ X.presheaf)

/-- If the diagonal of `X` is representable with projections in a property `P` of
monomorphisms respecting isomorphisms, the pairing `U ×_X V → U ×_K V` of the two
projections is in `P`. -/
theorem pairPullbackLift_mem_of_relative_diag (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (hmono : ∀ ⦃A B : Scheme.{u}⦄ (f : A ⟶ B), P f → Mono f)
    (hX : (MorphismProperty.inverseImage P (Over.forget _)).relative (schemeYoneda _)
      (diag X.presheaf)) :
    P (lift (pairPullbackFst a b) (pairPullbackSnd a b)).left := by
  obtain ⟨Z, ι, hι, himm⟩ := exists_representsEqualizer_of_relative_diag hX
    (uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map (fst U V) ≫ a))
    (uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map (snd U V) ≫ b))
  have : Mono ι.left := hmono _ himm
  have : Mono ι := Over.mono_of_mono_left ι
  obtain ⟨φ, hφ⟩ : ∃ φ : pairPullback a b ⟶ Z,
      φ ≫ ι = lift (pairPullbackFst a b) (pairPullbackSnd a b) := by
    apply (hι _).2
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
    congr 1
    simp only [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, lift_fst, lift_snd]
    exact (pairPullback_isPullback a b).w
  have hw : (schemeYoneda _).map (ι ≫ fst U V) ≫ a =
      (schemeYoneda _).map (ι ≫ snd U V) ≫ b := by
    have := (hι ι).1 ⟨𝟙 _, Category.id_comp _⟩
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality] at this
    simpa [Functor.map_comp_assoc] using uliftYonedaEquiv.injective this
  obtain ⟨ψ, hψ⟩ := (schemeYoneda _).map_surjective
    ((pairPullback_isPullback a b).lift _ _ hw)
  have hψ₁ : ψ ≫ pairPullbackFst a b = ι ≫ fst U V :=
    (schemeYoneda _).map_injective (by rw [Functor.map_comp, hψ, IsPullback.lift_fst])
  have hψ₂ : ψ ≫ pairPullbackSnd a b = ι ≫ snd U V :=
    (schemeYoneda _).map_injective (by rw [Functor.map_comp, hψ, IsPullback.lift_snd])
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply (schemeYoneda _).map_injective
    apply (pairPullback_isPullback a b).hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hψ₁, reassoc_of% hφ, lift_fst,
        Category.id_comp]
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hψ₂, reassoc_of% hφ, lift_snd,
        Category.id_comp]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono ι, Category.assoc, hφ, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, hψ₁]
    · rw [Category.assoc, lift_snd, hψ₂]
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsIso φ.left := (Over.forget _).map_isIso φ
  rw [← hφ, Over.comp_left]
  exact (MorphismProperty.cancel_left_of_respectsIso P φ.left ι.left).mpr himm

/-- **Overlaps are locally closed in products**: if `X` is locally separated, the pairing
`U ×_X V → U ×_K V` of the two projections is an immersion. -/
theorem isImmersion_pairPullbackLift (hX : IsLocallySeparated X) :
    IsImmersion (lift (pairPullbackFst a b) (pairPullbackSnd a b)).left :=
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    IsImmersion.isStableUnderBaseChange.respectsIso
  pairPullbackLift_mem_of_relative_diag a b @IsImmersion (fun _ _ _ _ => inferInstance) hX

/-- **Overlaps are closed in products**: if `X` is separated, the pairing
`U ×_X V → U ×_K V` of the two projections is a closed immersion. -/
theorem isClosedImmersion_pairPullbackLift (hX : IsSeparated X) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (lift (pairPullbackFst a b) (pairPullbackSnd a b)).left :=
  pairPullbackLift_mem_of_relative_diag a b @_root_.AlgebraicGeometry.IsClosedImmersion
    (fun _ _ _ _ => inferInstance) hX

/-- If `X` is locally separated, the pullback of two schemes locally of finite type over `X`
is locally of finite type. -/
theorem locallyOfFiniteType_pairPullback_of_isLocallySeparated (hX : IsLocallySeparated X)
    [LocallyOfFiniteType U.hom] [LocallyOfFiniteType V.hom] :
    LocallyOfFiniteType (pairPullback a b).hom := by
  have := isImmersion_pairPullbackLift a b hX
  have : LocallyOfFiniteType (U ⊗ V).hom := by
    change LocallyOfFiniteType (pullback.fst U.hom V.hom ≫ U.hom)
    infer_instance
  rw [← Over.w (lift (pairPullbackFst a b) (pairPullbackSnd a b))]
  infer_instance

/-- **Rational points of overlaps embed into products**: if `X` is locally separated, the
rational points of `U ×_X V` carry the subspace topology of `U(K) × V(K)`. -/
theorem isEmbedding_pairPullback_points (hX : IsLocallySeparated X) :
    @IsEmbedding _ _ (schemePointTopology K (pairPullback a b) K)
      (@instTopologicalSpaceProd _ _ (schemePointTopology K U K) (schemePointTopology K V K))
      (fun w : RingPoint K (pairPullback a b) K =>
        ((w ≫ pairPullbackFst a b : RingPoint K U K), (w ≫ pairPullbackSnd a b : RingPoint K V K))) := by
  have := isImmersion_pairPullbackLift a b hX
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  let : TopologicalSpace (RingPoint K (pairPullback a b) K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K (U ⊗ V) K) := schemePointTopology K (U ⊗ V) K
  have hιe := isEmbedding_schemePointMap_of_isImmersion (K := K)
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
    IsEmbedding F) this).mpr ((PointTopology.schemeProductPointHomeomorph K K U V).isEmbedding.comp hιe)

/-- **Local injectivity**: if `X` is locally separated, an étale map `h_U → X` from a
scheme is injective on rational points near every rational point. -/
theorem exists_isOpen_injOn_schemePointsMap (hX : IsLocallySeparated X) (ha : IsEtale a)
    (u : RingPoint K U K) :
    ∃ N : Set (RingPoint K U K), IsOpen[schemePointTopology K U K] N ∧ u ∈ N ∧
      Set.InjOn (schemePointsMap a) N := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K (pairPullback a a) K) := schemePointTopology K _ K
  have := etale_pairPullbackSnd a a ha
  obtain ⟨δ, hδ⟩ := (schemeYoneda _).map_surjective
    ((pairPullback_isPullback a a).lift (𝟙 _) (𝟙 _) rfl)
  have hδ₁ : δ ≫ pairPullbackFst a a = 𝟙 U :=
    (schemeYoneda _).map_injective (by
      rw [Functor.map_comp, hδ, IsPullback.lift_fst]
      exact ((schemeYoneda _).map_id U).symm)
  have hδ₂ : δ ≫ pairPullbackSnd a a = 𝟙 U :=
    (schemeYoneda _).map_injective (by
      rw [Functor.map_comp, hδ, IsPullback.lift_snd]
      exact ((schemeYoneda _).map_id U).symm)
  have : _root_.AlgebraicGeometry.IsOpenImmersion δ.left :=
    isOpenImmersion_of_section (pairPullbackSnd a a).left δ.left
      (by rw [← Over.comp_left, hδ₂, Over.id_left])
  let δK : RingPoint K U K → RingPoint K (pairPullback a a) K := fun v => v ≫ δ
  let pairK : RingPoint K (pairPullback a a) K → RingPoint K U K × RingPoint K U K :=
    fun w => (w ≫ pairPullbackFst a a, w ≫ pairPullbackSnd a a)
  have hD : IsOpen (Set.range δK) :=
    (PointTopology.isOpenEmbedding_schemePointMap K K δ).isOpen_range
  obtain ⟨G, hG, hGD⟩ := (isEmbedding_pairPullback_points a a hX).isOpen_iff.1 hD
  have hGD' : pairK ⁻¹' G = Set.range δK := hGD
  have k : ∀ v : PointTopology.ringTest K K ⟶ U,
      ((v ≫ δ) ≫ pairPullbackFst a a = v) ∧ ((v ≫ δ) ≫ pairPullbackSnd a a = v) :=
    fun v => ⟨by rw [Category.assoc, hδ₁, Category.comp_id],
      by rw [Category.assoc, hδ₂, Category.comp_id]⟩
  have huu : (u, u) ∈ G := by
    have hu : pairK (δK u) ∈ G := by
      rw [← Set.mem_preimage, hGD']
      exact ⟨u, rfl⟩
    have e : pairK (δK u) = (u, u) := Prod.ext (k u).1 (k u).2
    exact e ▸ hu
  obtain ⟨N₁, N₂, hN₁, hN₂, hu₁, hu₂, hsub⟩ := isOpen_prod_iff.1 hG u u huu
  refine ⟨N₁ ∩ N₂, hN₁.inter hN₂, ⟨hu₁, hu₂⟩, fun n hn m hm hnm => ?_⟩
  obtain ⟨w, hw₁, hw₂⟩ := exists_pairPullback_point a a hnm
  have hwG : pairK w ∈ G := by
    have e : pairK w = (n, m) := Prod.ext hw₁ hw₂
    rw [e]
    exact hsub ⟨hn.1, hm.2⟩
  rw [← Set.mem_preimage, hGD'] at hwG
  obtain ⟨v, hv⟩ := hwG
  have e₁ : n = v := by
    rw [← hw₁, ← hv]
    exact (k v).1
  have e₂ : m = v := by
    rw [← hw₂, ← hv]
    exact (k v).2
  exact e₁.trans e₂.symm

end PairEmbedding

variable {K : Type u} [NontriviallyNormedField K] in
/-- **Étale morphisms** of quasi-separated spaces locally of finite type, with locally
separated target, induce local homeomorphisms on rational points. -/
theorem isLocalHomeomorph_ringPointsMap (hK : IsHenselianValuedField K)
    {X X' : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX' : IsQuasiSeparatedLocallyFiniteType K X') (hX : IsLocallySeparatedLocallyFiniteType K X)
    (f : X' ⟶ X) (hf : IsEtaleMorphism f) :
    @IsLocalHomeomorph _ _ (etaleChartTopology K X') (etaleChartTopology K X)
      (RingPoints.map (A := K) f) := by
  let : TopologicalSpace (RingPoints K X' K) := etaleChartTopology K X'
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  have hcont := continuous_ringPointsMap hK hX.1 f
  have hopen := isOpenMap_ringPointsMap_of_isEtaleMorphism hK hX' f hf
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x'
  obtain ⟨c, u, rfl⟩ := hX'.exists_chart x'
  obtain ⟨N, hN, huN, hinj⟩ := exists_isOpen_injOn_schemePointsMap (hom c.hom ≫ hom f) hX.2
    (hf _ _ c.isEtale) u
  have hO : IsOpen (c.pointMap '' N) := c.isOpenMap_pointMap hK N hN
  refine ⟨c.pointMap '' N, hO.mem_nhds ⟨u, huN, rfl⟩, ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hcont.comp continuous_subtype_val) ?_ (hopen.domRestrict hO)
  rintro ⟨_, n, hn, rfl⟩ ⟨_, m, hm, rfl⟩ h
  exact Subtype.ext (congrArg c.pointMap (hinj hn hm h))

variable {K : Type u} [NontriviallyNormedField K] in
/-- **Fibre products**: for a pullback square of quasi-separated spaces locally of finite
type with locally separated base, the rational points of the pullback carry the subspace
topology of the product of the rational points of the two factors. -/
theorem isEmbedding_pullbackPoints (hK : IsHenselianValuedField K)
    {P X' X'' X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (p' : P ⟶ X') (p'' : P ⟶ X'') (f' : X' ⟶ X) (f'' : X'' ⟶ X)
    (hP : IsQuasiSeparatedLocallyFiniteType K P) (hX' : IsQuasiSeparatedLocallyFiniteType K X')
    (hX'' : IsQuasiSeparatedLocallyFiniteType K X'')
    (hX : IsLocallySeparatedLocallyFiniteType K X)
    (h : IsPullback (hom p') (hom p'') (hom f') (hom f'')) :
    @IsEmbedding _ _ (etaleChartTopology K P)
      (@instTopologicalSpaceProd _ _ (etaleChartTopology K X') (etaleChartTopology K X''))
      (fun w : RingPoints K P K => (RingPoints.map p' w, RingPoints.map p'' w)) := by
  let : TopologicalSpace (RingPoints K P K) := etaleChartTopology K P
  let : TopologicalSpace (RingPoints K X' K) := etaleChartTopology K X'
  let : TopologicalSpace (RingPoints K X'' K) := etaleChartTopology K X''
  let g : RingPoints K P K → RingPoints K X' K × RingPoints K X'' K :=
    fun w => (RingPoints.map p' w, RingPoints.map p'' w)
  change IsEmbedding g
  have hcont : Continuous g :=
    (continuous_ringPointsMap hK hX' p').prodMk (continuous_ringPointsMap hK hX'' p'')
  have hinj : Function.Injective g := fun w₁ w₂ hw =>
    ext_app_of_isPullback h _ (congrArg Prod.fst hw) (congrArg Prod.snd hw)
  have hw : ∀ w : RingPoints K P K,
      RingPoints.map f' (RingPoints.map p' w) = RingPoints.map f'' (RingPoints.map p'' w) :=
    fun w => congrArg (fun φ => φ.app (op (PointTopology.ringTest K K)) w) h.w
  refine ⟨isInducing_iff_nhds.2 fun w => le_antisymm (hcont.tendsto w).le_comap
    (fun s hs => ?_), hinj⟩
  obtain ⟨O, hOs, hO, hwO⟩ := mem_nhds_iff.1 hs
  obtain ⟨c', u', hu'⟩ := hX'.exists_chart (RingPoints.map p' w)
  obtain ⟨c'', u'', hu''⟩ := hX''.exists_chart (RingPoints.map p'' w)
  have := c'.locallyOfFiniteType
  have := c''.locallyOfFiniteType
  let a : (schemeYoneda _).obj c'.scheme ⟶ X.presheaf := hom c'.hom ≫ hom f'
  let b : (schemeYoneda _).obj c''.scheme ⟶ X.presheaf := hom c''.hom ≫ hom f''
  have hpt : ∀ {n' : RingPoint K c'.scheme K} {n'' : RingPoint K c''.scheme K}
      {w₂ : RingPoints K P K}, c'.pointMap n' = RingPoints.map p' w₂ →
        c''.pointMap n'' = RingPoints.map p'' w₂ → schemePointsMap a n' = schemePointsMap b n'' :=
    fun h₁ h₂ => (congrArg (RingPoints.map f') h₁).trans ((hw _).trans
      (congrArg (RingPoints.map f'') h₂).symm)
  let ρ : (schemeYoneda _).obj (pairPullback a b) ⟶ P.presheaf :=
    h.lift ((schemeYoneda _).map (pairPullbackFst a b) ≫ hom c'.hom)
      ((schemeYoneda _).map (pairPullbackSnd a b) ≫ hom c''.hom)
      ((Category.assoc _ _ _).trans ((pairPullback_isPullback a b).w.trans
        (Category.assoc _ _ _).symm))
  have hρ₁ : ∀ v : RingPoint K (pairPullback a b) K,
      RingPoints.map p' (schemePointsMap ρ v) = c'.pointMap (v ≫ pairPullbackFst a b) :=
    fun v => congrArg (fun φ : (schemeYoneda _).obj (pairPullback a b) ⟶ X'.presheaf =>
      φ.app (op (PointTopology.ringTest K K)) (ULift.up v)) (h.lift_fst _ _ _)
  have hρ₂ : ∀ v : RingPoint K (pairPullback a b) K,
      RingPoints.map p'' (schemePointsMap ρ v) = c''.pointMap (v ≫ pairPullbackSnd a b) :=
    fun v => congrArg (fun φ : (schemeYoneda _).obj (pairPullback a b) ⟶ X''.presheaf =>
      φ.app (op (PointTopology.ringTest K K)) (ULift.up v)) (h.lift_snd _ _ _)
  have hρeq : ∀ {v : RingPoint K (pairPullback a b) K} {w₂ : RingPoints K P K},
      c'.pointMap (v ≫ pairPullbackFst a b) = RingPoints.map p' w₂ →
        c''.pointMap (v ≫ pairPullbackSnd a b) = RingPoints.map p'' w₂ →
          schemePointsMap ρ v = w₂ :=
    fun h₁ h₂ => hinj (Prod.ext ((hρ₁ _).trans h₁) ((hρ₂ _).trans h₂))
  obtain ⟨w₀, hw₀₁, hw₀₂⟩ := exists_pairPullback_point a b (hpt hu' hu'')
  have := locallyOfFiniteType_pairPullback_of_isLocallySeparated a b hX.2
  let : TopologicalSpace (RingPoint K c'.scheme K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K c''.scheme K) := schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K (pairPullback a b) K) := schemePointTopology K _ K
  have hρc : Continuous (schemePointsMap ρ) := continuous_schemePointsMap hK hP.exists_chart ρ
  let pairK : RingPoint K (pairPullback a b) K → RingPoint K c'.scheme K × RingPoint K c''.scheme K :=
    fun v => (v ≫ pairPullbackFst a b, v ≫ pairPullbackSnd a b)
  obtain ⟨G, hG, hGO⟩ := (isEmbedding_pairPullback_points a b hX.2).isOpen_iff.1
    (hO.preimage hρc)
  have hGO' : pairK ⁻¹' G = schemePointsMap ρ ⁻¹' O := hGO
  have hu : (u', u'') ∈ G := by
    have e : pairK w₀ = (u', u'') := Prod.ext hw₀₁ hw₀₂
    rw [← e, ← Set.mem_preimage, hGO', Set.mem_preimage,
      hρeq ((congrArg c'.pointMap hw₀₁).trans hu') ((congrArg c''.pointMap hw₀₂).trans hu'')]
    exact hwO
  obtain ⟨N', N'', hN', hN'', hu'N, hu''N, hsub⟩ := isOpen_prod_iff.1 hG _ _ hu
  refine Filter.mem_comap.2 ⟨(c'.pointMap '' N') ×ˢ (c''.pointMap '' N''), ?_, ?_⟩
  · exact prod_mem_nhds ((c'.isOpenMap_pointMap hK N' hN').mem_nhds ⟨u', hu'N, hu'⟩)
      ((c''.isOpenMap_pointMap hK N'' hN'').mem_nhds ⟨u'', hu''N, hu''⟩)
  · rintro w₂ ⟨⟨n', hn', hn'eq⟩, ⟨n'', hn'', hn''eq⟩⟩
    obtain ⟨v, hv₁, hv₂⟩ := exists_pairPullback_point a b (hpt hn'eq hn''eq)
    have hvG : pairK v ∈ G := by
      have e : pairK v = (n', n'') := Prod.ext hv₁ hv₂
      rw [e]
      exact hsub ⟨hn', hn''⟩
    rw [← Set.mem_preimage, hGO', Set.mem_preimage,
      hρeq ((congrArg c'.pointMap hv₁).trans hn'eq) ((congrArg c''.pointMap hv₂).trans hn''eq)]
      at hvG
    exact hOs hvG

end Langlands.AlgebraicGeometry.AlgebraicSpace
