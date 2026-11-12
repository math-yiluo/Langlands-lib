import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteExtensionPointEmbeddingReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartLocalSeparation
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Rational points embed along finite extensions of henselian valued fields

The proof uses descent on étale charts for finite Galois extensions, rationality
of étale lifts under extensions with trivial relative separable closure, and
factorization through the maximal separable subextension.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology IsHenselianValuedField
    ringBaseChange ringPointBaseChangeEquiv schemeBaseChangeTopology_proof
    isEmbedding_schemeChangeRing exists_changeRing_eq_of_formallyUnramified)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FiniteExtensionEmbedding

section Algebra

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

/-- Uniqueness of the extending absolute value makes algebraic embeddings isometric. -/
theorem isometry_algHom (hK : IsHenselianValuedField K)
    {M : Type u} [NontriviallyNormedField M] [NormedAlgebra K M] (φ : L →ₐ[K] M) :
    Isometry φ := by
  obtain ⟨w, hw, huniq⟩ := hK L
  let v := (NormedField.toAbsoluteValue M).comp (f := φ.toRingHom) φ.injective
  have hv : v = w := huniq v (by
    intro c
    change ‖φ (algebraMap K L c)‖ = ‖c‖
    rw [φ.commutes, norm_algebraMap'])
  have hn : NormedField.toAbsoluteValue L = w :=
    huniq _ (fun c => norm_algebraMap' L c)
  exact AddMonoidHomClass.isometry_of_norm φ
    (fun x => congrArg (fun a : AbsoluteValue L ℝ => a x) (hv.trans hn.symm))

/-- In particular, algebraic automorphisms are isometries. -/
theorem isometry_aut (hK : IsHenselianValuedField K) (σ : L ≃ₐ[K] L) :
    Isometry σ := isometry_algHom hK σ.toAlgHom

/-- Algebraic normed extensions of henselian valued fields are henselian. -/
theorem isHenselianValuedField_extension (hK : IsHenselianValuedField K) :
    IsHenselianValuedField L := by
  intro E _ _ _
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.trans K L E
  obtain ⟨w, hw, huniq⟩ := hK E
  let v := w.comp (f := algebraMap L E) (algebraMap L E).injective
  have hvK : ∀ c : K, v (algebraMap K L c) = ‖c‖ := by
    intro c
    change w (algebraMap L E (algebraMap K L c)) = ‖c‖
    rw [← IsScalarTower.algebraMap_apply K L E, hw]
  obtain ⟨a, ha, hauniq⟩ := hK L
  have hv : v = NormedField.toAbsoluteValue L :=
    (hauniq v hvK).trans (hauniq _ (fun c => norm_algebraMap' L c)).symm
  refine ⟨w, ?_, ?_⟩
  · intro c
    exact congrArg (fun b : AbsoluteValue L ℝ => b c) hv
  · intro w' hw'
    apply huniq
    intro c
    rw [IsScalarTower.algebraMap_apply K L E, hw', norm_algebraMap']

end Algebra

section SeparableClosure

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- An étale lift over an extension with trivial relative separable closure is rational. -/
theorem exists_rational_of_extension (hsep : separableClosure K L = ⊥)
    {U V : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (b : (schemeYoneda _).obj V ⟶ X.presheaf) (ha : IsEtale a)
    (η : RingPoint K U L) (v : RingPoint K V K)
    (h : a.app (op (ringTest K L)) (ULift.up η) =
      b.app (op (ringTest K L))
        (ULift.up (PointTopology.RingPoint.changeRing (Algebra.ofId K L) v))) :
    ∃ u : RingPoint K U K,
      PointTopology.RingPoint.changeRing (Algebra.ofId K L) u = η ∧
        schemePointsMap a u = schemePointsMap b v := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a b)
    (ringTest K L) (ULift.up η) (ULift.up _) h
  let w : RingPoint K (pairPullback a b) L := p.down
  have hw₁ : w ≫ pairPullbackFst a b = η := congrArg ULift.down hp₁
  have hw₂ : w ≫ pairPullbackSnd a b =
      PointTopology.RingPoint.changeRing (Algebra.ofId K L) v :=
    congrArg ULift.down hp₂
  have := etale_pairPullbackSnd a b ha
  obtain ⟨w₀, hw₀⟩ := exists_changeRing_eq_of_formallyUnramified K L hsep
    (pairPullbackSnd a b) w v hw₂
  let : TopologicalSpace (RingPoint K V K) := schemePointTopology K V K
  let : TopologicalSpace (RingPoint K V L) := schemePointTopology K V L
  have hι : IsEmbedding (Algebra.ofId K L) :=
    (PointTopology.FiniteExtensionCompletion.isometry_algebraMap K L).isEmbedding
  have hinj := (isEmbedding_schemeChangeRing K K L V (Algebra.ofId K L) hι).injective
  have hv : w₀ ≫ pairPullbackSnd a b = v := by
    apply hinj
    change PointTopology.RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₂]
  refine ⟨w₀ ≫ pairPullbackFst a b, ?_, ?_⟩
  · change PointTopology.RingPoint.changeRing _ w₀ ≫ _ = _
    rw [hw₀, hw₁]
  · rw [schemePointsMap_pairPullbackFst, hv]

/-- If the relative separable closure is trivial, the completion-embedding chart
argument works for the given extension itself. -/
theorem isEmbedding_of_separableClosure_eq_bot (hL : IsHenselianValuedField L)
    (hsep : separableClosure K L = ⊥) (hX : IsQuasiSeparatedLocallyFiniteType K X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (fieldExtensionPointMap K L X) := by
  let : ∀ U : Over (Spec (CommRingCat.of K)), TopologicalSpace (RingPoint K U K) :=
    fun U => schemePointTopology K U K
  let : ∀ U : Over (Spec (CommRingCat.of L)), TopologicalSpace (RingPoint L U L) :=
    fun U => schemePointTopology L U L
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  have hcov := exists_chart_pointMap_eq hX.1 hX.2
  have hcomm := fun (c : EtaleFiniteTypeChart K X) =>
    fieldExtensionPointMap_pointMap (L := L) c
  have hrat : ∀ (c : EtaleFiniteTypeChart K X)
      (η : RingPoint L (ringBaseChange K L c.scheme) L) (y : RingPoints K X K),
      c.fieldExtension.pointMap η = fieldExtensionPointMap K L X y →
        ∃ u : RingPoint K c.scheme K,
          fieldExtensionSchemePointMap K L c.scheme u = η ∧ c.pointMap u = y := by
    intro c η y h
    obtain ⟨d, v, rfl⟩ := hcov y
    have h' := congrArg (baseChangeRingPointsEquiv K L L X) h
    rw [baseChangeRingPointsEquiv_fieldExtension_pointMap, fieldExtensionPointMap,
      Equiv.apply_symm_apply, EtaleFiniteTypeChart.pointMap, RingPoints.changeRing_map] at h'
    obtain ⟨u, hu₁, hu₂⟩ := exists_rational_of_extension hsep
      (hom c.hom) (hom d.hom) c.isEtale _ v h'
    refine ⟨u, ?_, hu₂⟩
    rw [fieldExtensionSchemePointMap, hu₁, Equiv.apply_symm_apply]
  have hinj : Function.Injective (fieldExtensionPointMap K L X) := by
    intro x y h
    obtain ⟨c, u, rfl⟩ := hcov x
    rw [hcomm] at h
    obtain ⟨u', hu'₁, hu'₂⟩ := hrat c _ y h
    rw [← hu'₂, (isEmbedding_fieldExtensionSchemePointMap K L c.scheme).injective hu'₁]
  refine ⟨⟨le_antisymm
    (continuous_iff_le_induced.mp (continuous_fieldExtensionPointMap K L X)) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hWc : ∀ c : EtaleFiniteTypeChart K X,
      ∃ t : Set (RingPoint L (ringBaseChange K L c.scheme) L),
        IsOpen[schemePointTopology L (ringBaseChange K L c.scheme) L] t ∧
          fieldExtensionSchemePointMap K L c.scheme ⁻¹' t = c.pointMap ⁻¹' W := fun c =>
    (isEmbedding_fieldExtensionSchemePointMap K L c.scheme).isInducing.isOpen_iff.mp
      ((etaleChartTopology_isOpen_iff X W).mp hW c)
  choose t ht hte using hWc
  refine isOpen_induced_iff.mpr ⟨⋃ c, c.fieldExtension.pointMap '' t c,
    isOpen_iUnion (fun c => c.fieldExtension.isOpenMap_pointMap hL _ (ht c)), ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨c, η, hηt, hη⟩
    obtain ⟨u, rfl, rfl⟩ := hrat c η y hη
    have hu : u ∈ fieldExtensionSchemePointMap K L c.scheme ⁻¹' t c := hηt
    rw [hte c] at hu
    exact hu
  · intro hy
    obtain ⟨c, u, rfl⟩ := hcov y
    refine ⟨c, fieldExtensionSchemePointMap K L c.scheme u, ?_, (hcomm c u).symm⟩
    change u ∈ fieldExtensionSchemePointMap K L c.scheme ⁻¹' t c
    rw [hte c]
    exact hy

end SeparableClosure

section Galois

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Rational points can be lifted to affine finite-type étale charts. -/
theorem exists_affine_chart (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (x : RingPoints K X K) :
    ∃ (c : EtaleFiniteTypeChart K X), IsAffine c.scheme.left ∧
      ∃ u : RingPoint K c.scheme K, c.pointMap u = x := by
  obtain ⟨U, f, hU, hf, u, hu⟩ :=
    RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement K X hX.1 x
  have hlft := locallyOfFiniteType_of_isEtale hX.2 (hom f) hf
  have := hU
  exact ⟨⟨U, f, hf, hlft, inferInstance⟩, hU, u, hu⟩

/-- Finite Galois extensions give embeddings by invariant neighbourhoods in affine
étale charts. -/
theorem isEmbedding_of_isGalois (hK : IsHenselianValuedField K)
    (hL : IsHenselianValuedField L) (hX : IsLocallySeparatedLocallyFiniteType K X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (fieldExtensionPointMap K L X) := by
  classical
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  let f := fieldExtensionPointMap K L X
  have hinj : Function.Injective f := by
    intro x y h
    apply GaloisChartPoint.changeRing_injective (K := L) X
    exact (baseChangeRingPointsEquiv K L L X).symm.injective h
  have hcont : Continuous f := continuous_fieldExtensionPointMap K L X
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hlocal : ∀ x : W, ∃ N : Set (RingPoints L (baseChange (Spec.algebraMap K L) X) L),
      IsOpen N ∧ f x ∈ N ∧ f ⁻¹' N ⊆ W := by
    intro x
    obtain ⟨c, hc, u, hu⟩ := exists_affine_chart hX.1 x
    let := hc
    let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
    let : TopologicalSpace (RingPoint K c.scheme L) := schemePointTopology K c.scheme L
    let d : EtaleFiniteTypeChart L (baseChange (Spec.algebraMap K L) X) :=
      c.fieldExtension
    let : TopologicalSpace (RingPoint L d.scheme L) := schemePointTopology L d.scheme L
    let e := ringPointBaseChangeEquiv K L L c.scheme
    let i := PointTopology.RingPoint.changeRing (X := c.scheme) (Algebra.ofId K L)
    let q : RingPoint K c.scheme L →
        RingPoints L (baseChange (Spec.algebraMap K L) X) L := d.pointMap ∘ e
    have he : IsHomeomorph e := schemeBaseChangeTopology_proof K L L c.scheme
    have hι : IsEmbedding (Algebra.ofId K L) :=
      (PointTopology.FiniteExtensionCompletion.isometry_algebraMap K L).isEmbedding
    have hi : IsEmbedding i :=
      isEmbedding_schemeChangeRing K K L c.scheme (Algebra.ofId K L) hι
    have hqopen : IsOpenMap q := (d.isOpenMap_pointMap hL).comp he.isOpenMap
    have hqi (v : RingPoint K c.scheme K) : f (c.pointMap v) = q (i v) :=
      fieldExtensionPointMap_pointMap c v
    have hqeval (η : RingPoint K c.scheme L) :
        baseChangeRingPointsEquiv K L L X (q η) =
          RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme L).symm η) := by
      change baseChangeRingPointsEquiv K L L X
        (c.fieldExtension.pointMap (ringPointBaseChangeEquiv K L L c.scheme η)) = _
      rw [baseChangeRingPointsEquiv_fieldExtension_pointMap, Equiv.symm_apply_apply]
    obtain ⟨A, hAo, hAeq⟩ := hi.isInducing.isOpen_iff.mp
      (hW.preimage c.continuous_pointMap)
    have huA : i u ∈ A := by
      change u ∈ i ⁻¹' A
      rw [hAeq]
      change c.pointMap u ∈ W
      rw [hu]
      exact x.property
    obtain ⟨V₀, hV₀o, huV₀, hV₀inj⟩ := exists_isOpen_injOn_schemePointsMap
      (hom d.hom) (hX.2.baseChange (Spec.algebraMap K L)) d.isEtale (e (i u))
    let V := e ⁻¹' V₀
    have hVo : IsOpen V := hV₀o.preimage he.continuous
    have huV : i u ∈ V := huV₀
    have hVinj : Set.InjOn q V := fun η hη ξ hξ heq =>
      he.injective (hV₀inj hη hξ heq)
    let r : (L ≃ₐ[K] L) → RingPoint K c.scheme L → RingPoint K c.scheme L :=
      fun σ => PointTopology.RingPoint.changeRing σ.toAlgHom
    have hrcont (σ : L ≃ₐ[K] L) : Continuous (r σ) :=
      (isEmbedding_schemeChangeRing K L L c.scheme σ.toAlgHom
        (isometry_aut hK σ).isEmbedding).continuous
    have hrbase (σ : L ≃ₐ[K] L) : r σ (i u) = i u := by
      change ringTest K K ⟶ c.scheme at u
      change ringTestMap K σ.toAlgHom ≫ (ringTestMap K (Algebra.ofId K L) ≫ u) =
        ringTestMap K (Algebra.ofId K L) ≫ u
      rw [← Category.assoc, ← PointTopology.ringTestMap_comp]
      congr 2
      ext
    let E := (A ∩ V) ∩ ⋂ σ : L ≃ₐ[K] L, r σ ⁻¹' V
    have hEo : IsOpen E :=
      (hAo.inter hVo).inter (isOpen_iInter_of_finite fun σ => hVo.preimage (hrcont σ))
    have huE : i u ∈ E :=
      ⟨⟨huA, huV⟩, Set.mem_iInter.mpr fun σ => by
        change r σ (i u) ∈ V
        rw [hrbase]
        exact huV⟩
    refine ⟨q '' E, hqopen _ hEo, ?_, ?_⟩
    · exact ⟨i u, huE, (hqi u).symm.trans (congrArg f hu)⟩
    · intro y hy
      obtain ⟨η, hη, hηq⟩ := hy
      have hηeval : RingPoints.map c.hom
          ((schemeRingPointsEquiv K c.scheme L).symm η) =
          RingPoints.changeRing (Algebra.ofId K L) y := by
        rw [← hqeval, hηq]
        exact Equiv.apply_symm_apply _ _
      have hηfix : ∀ σ : L ≃ₐ[K] L, r σ η = η := by
        intro σ
        have hση : r σ η ∈ V := Set.mem_iInter.mp hη.2 σ
        apply hVinj hση hη.1.2
        apply (baseChangeRingPointsEquiv K L L X).injective
        rw [hqeval, hqeval]
        have hact : RingPoints.map c.hom
            ((schemeRingPointsEquiv K c.scheme L).symm (r σ η)) =
            RingPoints.changeRing σ.toAlgHom
              (RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme L).symm η)) :=
          (RingPoints.changeRing_map c.hom σ.toAlgHom _).symm
        rw [hact, hηeval, RingPoints.changeRing_comp]
        congr 1
        ext
      obtain ⟨v, hv⟩ := GaloisChartPoint.exists_desc_of_galois_invariant η
        (fun σ => hηfix σ)
      change RingPoint K c.scheme K at v
      have hiv : i v = η := hv
      have hvW : v ∈ c.pointMap ⁻¹' W := by
        rw [← hAeq]
        change i v ∈ A
        rw [hiv]
        exact hη.1.1
      have hyc : c.pointMap v = y := hinj (by rw [hqi, hiv, hηq])
      exact hyc ▸ hvW
  choose N hNo hNx hNsub using hlocal
  refine isOpen_induced_iff.mpr ⟨⋃ x : W, N x, isOpen_iUnion hNo, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx⟩
    exact hNsub x hx
  · intro hy
    exact ⟨⟨y, hy⟩, hNx ⟨y, hy⟩⟩

end Galois

section Separable

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Embed a finite separable extension in a finite Galois extension with the uniquely
extending norm, then cancel the continuous map to that extension. -/
theorem isEmbedding_of_isSeparable (hK : IsHenselianValuedField K)
    (hX : IsLocallySeparatedLocallyFiniteType K X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (fieldExtensionPointMap K L X) := by
  obtain ⟨N, _, _, hNfin, hNgal, ⟨ι⟩⟩ :=
    GaloisChartPoint.exists_galois_of_separable (k := K) L
  have : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.of_finite K N
  obtain ⟨v, hv, -⟩ := hK N
  let : NontriviallyNormedField N :=
    { v.toNormedField with
      non_trivial := by
        obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
        refine ⟨algebraMap K N c, ?_⟩
        change 1 < v (algebraMap K N c)
        rw [hv]
        exact hc }
  let : NormedAlgebra K N :=
    { norm_smul_le := fun c x => by
        change v (c • x) ≤ ‖c‖ * v x
        rw [Algebra.smul_def, map_mul, hv] }
  have hι := isometry_algHom hK ι
  let : Algebra L N := ι.toRingHom.toAlgebra
  have : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  let : NormedAlgebra L N :=
    { norm_smul_le := fun c x => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (congrArg (· * ‖x‖)
          (hι.norm_map_of_map_zero (map_zero ι) c)) }
  have hNhenselian : IsHenselianValuedField N := isHenselianValuedField_extension hK
  let XL := baseChange (Spec.algebraMap K L) X
  let XN := baseChange (Spec.algebraMap K N) X
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L XL L) := etaleChartTopology L XL
  let : TopologicalSpace (RingPoints N XN N) := etaleChartTopology N XN
  let : TopologicalSpace (RingPoints N (baseChange (Spec.algebraMap L N) XL) N) :=
    etaleChartTopology N _
  let g := RingPoints.map (A := N) (towerIso K L N X).hom ∘
    fieldExtensionPointMap L N XL
  have hg : Continuous g :=
    (isHomeomorph_ringPointsMap_of_iso (towerIso K L N X)).continuous.comp
      (continuous_fieldExtensionPointMap L N XL)
  have hcomp : IsEmbedding (g ∘ fieldExtensionPointMap K L X) := by
    have heq : g ∘ fieldExtensionPointMap K L X = fieldExtensionPointMap K N X :=
      funext (fieldExtensionPointMap_tower K L N X)
    rw [heq]
    exact isEmbedding_of_isGalois hK hNhenselian hX
  exact IsEmbedding.of_comp (continuous_fieldExtensionPointMap K L X) hg hcomp

end Separable

end FiniteExtensionEmbedding

/-- Conrad's finite-degree supplement to Proposition 5.11(3), without completeness:
the natural point map of a quasi-separated, locally separated algebraic space locally
of finite type embeds along a finite henselian normed field extension. -/
theorem henselianFiniteExtensionPointEmbedding :
    HenselianFiniteExtensionPointEmbeddingStatement.{u} := by
  intro K L _ _ _ _ hK hL X hX
  let S := separableClosure K L
  let : NormedAlgebra S L :=
    { norm_smul_le := fun c x => by
        change ‖(c : L) * x‖ ≤ ‖(c : L)‖ * ‖x‖
        exact (norm_mul _ _).le }
  let XS := baseChange (Spec.algebraMap K S) X
  let XL := baseChange (Spec.algebraMap K L) X
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints S XS S) := etaleChartTopology S XS
  let : TopologicalSpace (RingPoints L XL L) := etaleChartTopology L XL
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap S L) XS) L) :=
    etaleChartTopology L _
  have hXS : IsQuasiSeparatedLocallyFiniteType S XS :=
    ⟨hX.1.1.baseChange, hX.1.2.baseChange⟩
  have hfirst : IsEmbedding (fieldExtensionPointMap K S X) :=
    FiniteExtensionEmbedding.isEmbedding_of_isSeparable hK hX
  have hsecond : IsEmbedding (fieldExtensionPointMap S L XS) :=
    FiniteExtensionEmbedding.isEmbedding_of_separableClosure_eq_bot hL
      (separableClosure.separableClosure_eq_bot K L) hXS
  have hcomp := (isHomeomorph_ringPointsMap_of_iso (towerIso K S L X)).isEmbedding.comp
    (hsecond.comp hfirst)
  have heq : RingPoints.map (A := L) (towerIso K S L X).hom ∘
      fieldExtensionPointMap S L XS ∘ fieldExtensionPointMap K S X =
      fieldExtensionPointMap K L X :=
    funext (fieldExtensionPointMap_tower K S L X)
  change IsEmbedding (fieldExtensionPointMap K L X)
  rw [heq] at hcomp
  exact hcomp

end Langlands.AlgebraicGeometry.AlgebraicSpace
