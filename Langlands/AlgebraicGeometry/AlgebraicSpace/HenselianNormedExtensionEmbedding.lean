import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFiniteExtensionPointEmbeddingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparablyClosedExtensionPointMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Embeddings along arbitrary henselian normed extensions

Invariant finite-coordinate neighbourhoods remove the degree restriction from the
Galois chart argument. Closedness of the image is a separate obligation.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology IsHenselianValuedField
    ringBaseChange ringPointBaseChangeEquiv schemeBaseChangeTopology_proof
    isEmbedding_schemeChangeRing AlgPoint AffineCoordinateRing affineSchemePointEquiv
    affineSchemePointEquiv_changeRing affineSchemePointHomeomorph)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace NormedExtensionEmbedding

section InvariantNeighbourhoods

variable {K L A : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L] [CommRing A] [Algebra K A]

/-- A rational affine point has arbitrarily small open neighbourhoods invariant under
all isometric automorphisms of the extension, even when the automorphism group is infinite. -/
theorem exists_invariant_open (u : AlgPoint K A K)
    (hisom : ∀ σ : L ≃ₐ[K] L, Isometry σ)
    {N : Set (AlgPoint K A L)}
    (hN : N ∈ 𝓝 (AlgPoint.mapCoefficients (Algebra.ofId K L) u)) :
    ∃ B : Set (AlgPoint K A L), IsOpen B ∧
      AlgPoint.mapCoefficients (Algebra.ofId K L) u ∈ B ∧ B ⊆ N ∧
      ∀ (σ : L ≃ₐ[K] L) (p : AlgPoint K A L), p ∈ B →
        AlgPoint.mapCoefficients σ.toAlgHom p ∈ B := by
  classical
  let v := AlgPoint.mapCoefficients (Algebra.ofId K L) u
  rw [AlgPoint.isEmbedding_evaluation.isInducing.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨t, ht, htN⟩ := hN
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, V, hV, hIV⟩ := ht
  choose ε hε hεV using fun a => Metric.mem_nhds_iff.mp (hV a)
  let B : Set (AlgPoint K A L) := {p | ∀ a ∈ I, dist (p a) (v a) < ε a}
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · simp only [B, Set.ofPred_forall]
    exact isOpen_biInter_finset fun a _ =>
      isOpen_lt ((AlgPoint.continuous_eval a).dist continuous_const) continuous_const
  · intro a _
    change dist (v a) (v a) < ε a
    simpa only [dist_self] using hε a
  · intro p hp
    apply htN
    apply hIV
    intro a ha
    exact hεV a (hp a ha)
  · intro σ p hp a ha
    have hbase : σ (v a) = v a := σ.commutes (u a)
    change dist (σ (p a)) (v a) < ε a
    rw [← hbase, (hisom σ).dist_eq]
    exact hp a ha

/-- Affine points fixed by every automorphism of an arbitrary Galois extension descend. -/
theorem exists_desc_of_galois_invariant [IsGalois K L] (p : AlgPoint K A L)
    (hp : ∀ σ : L ≃ₐ[K] L, AlgPoint.mapCoefficients σ.toAlgHom p = p) :
    ∃ q : AlgPoint K A K, AlgPoint.mapCoefficients (Algebra.ofId K L) q = p := by
  classical
  have hmem (a : A) : p a ∈ Set.range (algebraMap K L) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (p a)).2 fun σ =>
      congrArg (fun q : AlgPoint K A L => q a) (hp σ)
  choose c hc using hmem
  change ∀ a, algebraMap K L (c a) = p.toAlgHom a at hc
  have hinj := (algebraMap K L).injective
  let q : A →ₐ[K] K :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, hc, hc, hc, map_mul])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [map_add, hc, hc, hc, map_add])
      commutes' := fun k => hinj (by rw [hc, p.toAlgHom.commutes]; rfl) }
  exact ⟨AlgPoint.ofAlgHom q, AlgPoint.ext hc⟩

end InvariantNeighbourhoods

section Galois

variable {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L] [IsGalois K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Arbitrary algebraic Galois extensions give embeddings for separated spaces,
using invariant neighbourhoods instead of a finite intersection over the group. -/
theorem isEmbedding_of_isGalois (hK : IsHenselianValuedField K)
    (hL : IsHenselianValuedField L) (hX : IsQuasiSeparatedLocallyFiniteType K X)
    (hs : IsSeparated X) :
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
    apply RelativeIntegralPoints.changeRing_injective hs (Algebra.ofId K L)
      (algebraMap K L).injective
    exact (baseChangeRingPointsEquiv K L L X).symm.injective h
  have hcont : Continuous f := continuous_fieldExtensionPointMap K L X
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, hinj⟩
  rw [TopologicalSpace.le_def]
  intro W hW
  have hlocal : ∀ x : W, ∃ N : Set (RingPoints L (baseChange (Spec.algebraMap K L) X) L),
      IsOpen N ∧ f x ∈ N ∧ f ⁻¹' N ⊆ W := by
    intro x
    obtain ⟨c, hc, u, hu⟩ := FiniteExtensionEmbedding.exists_affine_chart hX x
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
      (hom d.hom) ((isLocallySeparated_of_isSeparated hs).baseChange (Spec.algebraMap K L)) d.isEtale (e (i u))
    let V := e ⁻¹' V₀
    have hVo : IsOpen V := hV₀o.preimage he.continuous
    have huV : i u ∈ V := huV₀
    have hVinj : Set.InjOn q V := fun η hη ξ hξ heq =>
      he.injective (hV₀inj hη hξ heq)
    let r : (L ≃ₐ[K] L) → RingPoint K c.scheme L → RingPoint K c.scheme L :=
      fun σ => PointTopology.RingPoint.changeRing σ.toAlgHom
    let aE := affineSchemePointEquiv K c.scheme L
    have hAE : IsHomeomorph aE := by
      change @IsHomeomorph _ _ (schemePointTopology K c.scheme L) _ aE
      rw [PointTopology.schemePointTopology_eq_affine]
      exact @Homeomorph.isHomeomorph _ _
        (PointTopology.instTopologicalSpaceRingPointOfIsAffineLeftScheme K c.scheme L)
        AlgPoint.instTopologicalSpace (affineSchemePointHomeomorph K c.scheme L)
    have hn : aE '' (A ∩ V) ∈ 𝓝 (AlgPoint.mapCoefficients (Algebra.ofId K L)
        (affineSchemePointEquiv K c.scheme K u)) := by
      rw [← affineSchemePointEquiv_changeRing]
      have hAV : IsOpen (aE '' (A ∩ V)) := by
        exact hAE.isOpenMap _ (hAo.inter hVo)
      exact hAV.mem_nhds ⟨i u, ⟨huA, huV⟩, rfl⟩
    obtain ⟨B, hBo, huB, hBsub, hBinv⟩ := exists_invariant_open
      (affineSchemePointEquiv K c.scheme K u)
      (fun σ => FiniteExtensionEmbedding.isometry_aut hK σ) hn
    let E := aE ⁻¹' B
    have hEo : IsOpen E := hBo.preimage hAE.continuous
    have huE : i u ∈ E := by
      change aE (i u) ∈ B
      rw [affineSchemePointEquiv_changeRing]
      exact huB
    have hEsub : E ⊆ A ∩ V := by
      intro η hη
      obtain ⟨ξ, hξ, heq⟩ := hBsub hη
      exact (aE.injective heq) ▸ hξ
    have hEinv (σ : L ≃ₐ[K] L) (η : RingPoint K c.scheme L) (hη : η ∈ E) :
        r σ η ∈ E := by
      change aE (r σ η) ∈ B
      rw [affineSchemePointEquiv_changeRing]
      exact hBinv σ _ hη
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
        have hση : r σ η ∈ V := (hEsub (hEinv σ η hη)).2
        apply hVinj hση (hEsub hη).2
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
      have hfix : ∀ σ : L ≃ₐ[K] L,
          AlgPoint.mapCoefficients σ.toAlgHom (aE η) = aE η := by
        intro σ
        rw [← affineSchemePointEquiv_changeRing]
        exact congrArg aE (hηfix σ)
      obtain ⟨v₀, hv₀⟩ := exists_desc_of_galois_invariant (aE η) hfix
      let v := (affineSchemePointEquiv K c.scheme K).symm v₀
      have hiv : i v = η := by
        apply aE.injective
        rw [affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
        exact hv₀
      have hvW : v ∈ c.pointMap ⁻¹' W := by
        rw [← hAeq]
        change i v ∈ A
        rw [hiv]
        exact (hEsub hη).1
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
variable [NormedAlgebra K L] [Algebra.IsSeparable K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- A separable algebraic extension embeds in the separable closure with the unique
extending norm, reducing the point embedding to the arbitrary Galois case. -/
theorem isEmbedding_of_isSeparable (hK : IsHenselianValuedField K)
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (fieldExtensionPointMap K L X) := by
  let N := SeparableClosure K
  let ι : L →ₐ[K] N := IsSepClosed.lift
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
  have hι := FiniteExtensionEmbedding.isometry_algHom hK ι
  let : Algebra L N := ι.toRingHom.toAlgebra
  have : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_eq fun c => (ι.commutes c).symm
  let : NormedAlgebra L N :=
    { norm_smul_le := fun c x => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (congrArg (· * ‖x‖)
          (hι.norm_map_of_map_zero (map_zero ι) c)) }
  have hNhenselian : IsHenselianValuedField N := FiniteExtensionEmbedding.isHenselianValuedField_extension hK
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
    exact isEmbedding_of_isGalois hK hNhenselian hX hs
  exact IsEmbedding.of_comp (continuous_fieldExtensionPointMap K L X) hg hcomp


end Separable

end NormedExtensionEmbedding

/-- Coefficient extension embeds rational points of every separated quasi-separated
algebraic space locally of finite type along an arbitrary henselian normed extension. -/
theorem isEmbedding_henselianExtensionPointMap
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    @IsEmbedding _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (extensionPointMap L X) := by
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
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have hfirst : IsEmbedding (fieldExtensionPointMap K S X) :=
    NormedExtensionEmbedding.isEmbedding_of_isSeparable hK hX hs
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


/-- The canonical homeomorphism onto the image over an arbitrary henselian normed
extension, for a separated algebraic space locally of finite type. -/
def henselianExtensionPointHomeomorphRange
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hK : IsHenselianValuedField K) (hL : IsHenselianValuedField L)
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    letI : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
    letI : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
      etaleChartTopology L _
    RingPoints K X K ≃ₜ Set.range (extensionPointMap L X) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  exact (isEmbedding_henselianExtensionPointMap hK hL hX hs).toHomeomorph

end Langlands.AlgebraicGeometry.AlgebraicSpace
