import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ValuativeExistenceCore
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasComponentIncidence
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteTypeMorphismAtlas

/-!
# The valuative existence criterion for algebraic spaces

Stacks Project, Lemma 67.42.3 (Tag 0A3Y), (1) ⇒ (3): for a separated, universally closed
morphism `f : X ⟶ Y` of algebraic spaces, every square from `Spec K ⟶ Spec A` (with `A` a
valuation ring with fraction field `K`) has a lift. Quasi-compactness is not used.

Write `Z = X ×_Y Spec A` and `ζ ∈ |Z|` for the point given by `x`. Universal closedness gives a
point `ζ'` in the closure of `ζ` over the closed point of `Spec A`. An affine étale chart
`Spec P ⟶ Z` through `ζ'` and the prime `v` of `P` at `ζ'` satisfy the hypotheses of
`ValuativeExistence.exists_lift_of_chart`: every basic open `D(p) ∋ v` has open image in `|Z|`,
so it contains `ζ`, and a common refinement of the two points gives ring maps to a field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An étale chart maps open sets to open sets of the point topology. -/
theorem isOpen_image_chartPointMap {F : Presheaf S} {V : Over S}
    (b : (schemeYoneda S).obj V ⟶ F) (hb : IsEtale b) {O : Set V.left} (hO : IsOpen O) :
    @IsOpen _ (pointTopology F) (chartPointMap b '' O) := by
  apply (isOpen_pointTopology_iff F _).mpr
  intro U a ha
  let hr := ha.representable
  have hsq := hr.isPullback' b
  have hleft : Etale (hr.fst' b).left :=
    hb.projection a ((schemeYoneda S).map (hr.snd b)) (hr.fst' b) hsq.flip
  have heq : (Points.map a ∘ schemePoint U) ⁻¹' (chartPointMap b '' O) =
      (hr.fst' b).left '' ((hr.snd b).left ⁻¹' O) := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      obtain ⟨r, hr₁, hr₂⟩ :=
        (chartPointMap_eq_iff_exists_pullback b a ha.representable w z).mp hwz
      exact ⟨r, by rwa [Set.mem_preimage, hr₁], hr₂⟩
    · rintro ⟨r, hrO, rfl⟩
      exact ⟨_, hrO, (chartPointMap_comm hsq.w r).symm⟩
  rw [heq]
  exact (hr.fst' b).left.isOpenMap _ (hO.preimage (hr.snd b).left.continuous)

namespace ValuativeExistence

variable {A : Type u} [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S)

/-- A morphism of test spectra over `Spec A` comes from an `A`-algebra map. -/
theorem exists_algHom_eq {R Q : Type u} [CommRing R] [CommRing Q] [Algebra A R] [Algebra A Q]
    (m : algTest s R ⟶ algTest s Q) (hm : m ≫ algTestBase s Q = algTestBase s R) :
    ∃ φ : Q →ₐ[A] R, algTestMap s φ = m := by
  have hψ : Spec.map (Spec.preimage m.left) = m.left := Spec.map_preimage _
  refine ⟨⟨(Spec.preimage m.left).hom, fun a => ?_⟩, ?_⟩
  · have h := congrArg (fun k => k.left) hm
    simp only [Over.comp_left] at h
    change m.left ≫ Spec.map (CommRingCat.ofHom (algebraMap A Q)) =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) at h
    rw [← hψ, ← Spec.map_comp] at h
    exact congrArg (fun k => k.hom a) (Spec.map_injective h)
  · ext1
    rw [algTestMap_left]
    exact hψ

/-- A point `τ` of a scheme `T` mapping to two test spectra over `Spec A` gives `A`-algebra
maps to its residue field, through which the two maps factor. -/
theorem exists_residueField_algHom {P Q : Type u} [CommRing P] [CommRing Q] [Algebra A P]
    [Algebra A Q] {T : Over S} (g : T ⟶ algTest s P) (h : T ⟶ algTest s Q)
    (hgh : g ≫ algTestBase s P = h ≫ algTestBase s Q) (τ : T.left) :
    ∃ (R : Type u) (_ : Field R) (_ : Algebra A R) (φ : P →ₐ[A] R) (ψ : Q →ₐ[A] R)
      (e : algTest s R ⟶ T), e ≫ g = algTestMap s φ ∧ e ≫ h = algTestMap s ψ ∧
        ∀ p : P, p ∉ (show PrimeSpectrum P from g.left τ).asIdeal → φ p ≠ 0 := by
  let ι := T.left.fromSpecResidueField τ
  let : Algebra A (T.left.residueField τ) :=
    (Spec.preimage (ι ≫ (g ≫ algTestBase s P).left)).hom.toAlgebra
  have hα : Spec.map (CommRingCat.ofHom (algebraMap A (T.left.residueField τ))) =
      ι ≫ (g ≫ algTestBase s P).left :=
    Spec.map_preimage (ι ≫ (g ≫ algTestBase s P).left)
  let e : algTest s (T.left.residueField τ) ⟶ T := Over.homMk ι (by
    change ι ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap A (T.left.residueField τ))) ≫ s
    rw [hα, Category.assoc]
    exact congrArg (ι ≫ ·) (Over.w (g ≫ algTestBase s P)).symm)
  have he : e ≫ g ≫ algTestBase s P = algTestBase s (T.left.residueField τ) := by
    ext1
    exact hα.symm
  obtain ⟨φ, hφ⟩ := exists_algHom_eq s (e ≫ g) (by rw [Category.assoc, he])
  obtain ⟨ψ, hψ⟩ := exists_algHom_eq s (e ≫ h) (by rw [Category.assoc, ← hgh, he])
  refine ⟨T.left.residueField τ, inferInstance, inferInstance, φ, ψ, e, hφ.symm, hψ.symm, ?_⟩
  intro p hp hφp
  apply hp
  let pt : (algTest s (T.left.residueField τ)).left := IsLocalRing.closedPoint _
  have hτ : g.left τ = (algTestMap s φ).left pt := by
    rw [hφ, Over.comp_left, Scheme.Hom.comp_apply]
    congr 1
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  change p ∈ (show PrimeSpectrum P from g.left τ).asIdeal
  rw [hτ]
  change φ p ∈ (IsLocalRing.closedPoint (T.left.residueField τ)).asIdeal
  rw [hφp]
  exact zero_mem _

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Y.sections (Over.mk s))

/-- Every point of `X ×_Y Spec A` lies in the image of an étale chart by the spectrum of an
`A`-algebra. -/
theorem exists_algTest_chart (ζ' : Points (baseChange s f y)) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra A P) (ξ : X.sections (algTest s P))
      (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y) (u' : (algTest s P).left),
      IsEtale (zOf s f y ξ (algTestBase s P) hξ) ∧
        chartPointMap (zOf s f y ξ (algTestBase s P) hξ) u' = ζ' := by
  obtain ⟨U₀, a₀, -, ha₀, hs₀⟩ := X.exists_atlas
  let g : (schemeYoneda S).obj (Over.mk s) ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm y
  let c₀ := SchemePullbackChart.atlas f a₀ g
  have hc₀ : IsEtale c₀ := SchemePullbackChart.atlas_isEtale f a₀ g ha₀
  obtain ⟨u, rfl⟩ :=
    surjective_chartPointMap c₀ (SchemePullbackChart.atlas_isSurjective f a₀ g hs₀) ζ'
  let W := SchemePullbackChart.scheme f a₀ g
  let 𝒰 := W.left.affineOpenCover
  obtain ⟨u₀, hu₀⟩ := 𝒰.covers u
  let R₀ := 𝒰.X (𝒰.idx u)
  let V : Over S := Over.mk (𝒰.f (𝒰.idx u) ≫ W.hom)
  let j : V ⟶ W := Over.homMk (𝒰.f (𝒰.idx u)) rfl
  let b₀ := (schemeYoneda S).map j ≫ c₀
  have hb₀ : IsEtale b₀ :=
    (isEtale_map j (by change Etale (𝒰.f (𝒰.idx u)); infer_instance)).comp hc₀
  let t : V ⟶ Over.mk s := (schemeYoneda S).preimage (b₀ ≫ pullback.snd _ _)
  have ht : (schemeYoneda S).map t = b₀ ≫ pullback.snd _ _ := Functor.map_preimage _ _
  let : Algebra A R₀ := (Spec.preimage t.left).hom.toAlgebra
  have hα : Spec.map (CommRingCat.ofHom (algebraMap A R₀)) = t.left := Spec.map_preimage t.left
  let e : algTest s R₀ ⟶ V := Over.homMk (𝟙 (Spec R₀)) (by
    change 𝟙 _ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A R₀)) ≫ s
    rw [Category.id_comp, hα]
    exact (Over.w t).symm)
  have het : e ≫ t = algTestBase s R₀ := by
    ext1
    change 𝟙 _ ≫ t.left = Spec.map (CommRingCat.ofHom (algebraMap A R₀))
    rw [Category.id_comp, hα]
  let b := (schemeYoneda S).map e ≫ b₀
  have hb : IsEtale b :=
    (isEtale_map e (by change Etale (𝟙 (Spec R₀)); infer_instance)).comp hb₀
  have hbsnd : b ≫ pullback.snd _ _ = (schemeYoneda S).map (algTestBase s R₀) := by
    rw [Category.assoc, ← ht, ← Functor.map_comp, het]
  let ξ : X.sections (algTest s R₀) := uliftYonedaEquiv.{u + 1} (b ≫ pullback.fst _ _)
  have hξ : mapSections f _ ξ = Y.pullback (algTestBase s R₀) y := by
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    refine (uliftYonedaEquiv_symm_comp (F := X.presheaf) ξ (hom f)).symm.trans ?_
    rw [Equiv.symm_apply_apply, Category.assoc,
      pullback.condition, ← Category.assoc, hbsnd, map_comp_symm]
  have hbz : b = zOf s f y ξ (algTestBase s R₀) hξ := by
    apply pullback.hom_ext
    · rw [zOf_fst, Equiv.symm_apply_apply]
    · rw [zOf_snd, hbsnd]
  refine ⟨R₀, inferInstance, inferInstance, ξ, hξ, u₀, hbz ▸ hb, ?_⟩
  rw [← hbz, chartPointMap_comp, chartPointMap_comp]
  exact congrArg _ hu₀

/-- The image of a chart point in `|Spec A|`. -/
theorem map_snd_chartPointMap {P : Type u} [CommRing P] [Algebra A P]
    (ξ : X.sections (algTest s P)) (hξ : mapSections f _ ξ = Y.pullback (algTestBase s P) y)
    (u : (algTest s P).left) :
    Points.map (pullback.snd _ _ : baseChange s f y ⟶ _)
        (chartPointMap (zOf s f y ξ (algTestBase s P) hξ) u) =
      schemePoint (Over.mk s) ((algTestBase s P).left u) := by
  change Points.map _ (Points.map _ (schemePoint _ u)) = _
  rw [← Points.map_comp, zOf_snd]
  exact schemePoint_naturality _ _

/-- **Valuative existence.** For a separated, universally closed morphism `f`, a section `x`
over `Spec K` with `f(x) = y|_K` extends to a section over `Spec A` lying over `y`. -/
theorem exists_lift [IsDomain A] [ValuationRing A] {K : Type u} [Field K] [Algebra A K]
    [IsFractionRing A K] (hf : IsSeparatedMorphism f) (huc : IsUniversallyClosedMorphism f)
    (x : X.sections (algTest s K)) (hx : mapSections f _ x = Y.pullback (algTestBase s K) y) :
    ∃ a : X.sections (Over.mk s),
      X.pullback (algTestBase s K) a = x ∧ mapSections f _ a = y := by
  let := pointTopology (baseChange s f y)
  let := pointTopology ((schemeYoneda S).obj (Over.mk s))
  let zx := zOf s f y x (algTestBase s K) hx
  let ζ := chartPointMap zx (IsLocalRing.closedPoint K)
  let π := Points.map (pullback.snd _ _ : baseChange s f y ⟶ _)
  have hπ : IsClosedMap π := huc (Over.mk s) _
  -- The closed point of `Spec A` is the image of a point `ζ'` in the closure of `ζ`.
  have hclosed : IsClosed (schemePoint (Over.mk s) ⁻¹' (π '' closure {ζ})) :=
    (hπ _ isClosed_closure).preimage (continuous_schemePoint (Over.mk s))
  have hη : (algTestBase s K).left (IsLocalRing.closedPoint K) ∈
      schemePoint (Over.mk s) ⁻¹' (π '' closure {ζ}) :=
    ⟨ζ, subset_closure rfl, map_snd_chartPointMap s f y x hx _⟩
  have hm : IsLocalRing.closedPoint A ∈ schemePoint (Over.mk s) ⁻¹' (π '' closure {ζ}) := by
    refine hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη) ?_
    have hle : (show PrimeSpectrum A from (algTestBase s K).left (IsLocalRing.closedPoint K)) ≤
        IsLocalRing.closedPoint A := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal]
      exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    exact (PrimeSpectrum.le_iff_mem_closure _ _).mp hle
  obtain ⟨ζ', hζ'C, hζ'm⟩ := hm
  obtain ⟨P, _, _, ξ, hξ, u', hb, hu'⟩ := exists_algTest_chart s f y ζ'
  have hu'm : (algTestBase s P).left u' = IsLocalRing.closedPoint A := by
    have h := congrArg (schemePointsTo (Over.mk s))
      ((map_snd_chartPointMap s f y ξ hξ u').symm.trans ((congrArg π hu').trans hζ'm))
    exact (schemePointsTo_schemePoint _ _).symm.trans (h.trans (schemePointsTo_schemePoint _ _))
  let v : Ideal P := (show PrimeSpectrum P from u').asIdeal
  have : v.IsPrime := (show PrimeSpectrum P from u').isPrime
  have hv : (IsLocalRing.maximalIdeal A).map (algebraMap A P) ≤ v := by
    rw [Ideal.map_le_iff_le_comap]
    exact (congrArg PrimeSpectrum.asIdeal hu'm).ge
  refine exists_lift_of_chart s f y hf hx hξ hb v hv fun p hp => ?_
  -- The basic open `D(p) ∋ v` has open image containing `ζ'`, hence `ζ`.
  let O : Set (algTest s P).left := (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum P))
  have hO := isOpen_image_chartPointMap (zOf s f y ξ (algTestBase s P) hξ) hb
    (O := O) (PrimeSpectrum.basicOpen p).isOpen
  obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp hζ'C _ hO ⟨u', hp, hu'⟩
  rw [Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨w, hwO, hwζ⟩ := hzO
  obtain ⟨T, g, h, τ, he, hg, -⟩ := (chartPointMap_eq_iff_sameImage₂ _ _ w _).mp hwζ
  have hsec : X.pullback g ξ = X.pullback h x := by
    have h1 := congrArg (fun k => k ≫ pullback.fst _ _) he
    simp only [Category.assoc, zx, zOf_fst, map_comp_symm] at h1
    exact uliftYonedaEquiv.{u + 1}.symm.injective h1
  have hbase : g ≫ algTestBase s P = h ≫ algTestBase s K := by
    have h2 := congrArg (fun k => k ≫ pullback.snd _ _) he
    simp only [Category.assoc, zx, zOf_snd, ← Functor.map_comp] at h2
    exact (schemeYoneda S).map_injective h2
  obtain ⟨R, _, _, φ, ψ, e, hφ, hψ, hne⟩ := exists_residueField_algHom s g h hbase τ
  refine ⟨R, inferInstance, inferInstance, ψ, φ, ?_, hne p ?_⟩
  · rw [← hφ, ← hψ, pullback_comp, pullback_comp, hsec]
  · rw [hg]
    exact hwO

end ValuativeExistence

/-- **Stacks 67.42.3, (1) ⇒ (3).** A quasi-compact, separated, universally closed morphism of
algebraic spaces satisfies the existence part of the valuative criterion. -/
theorem spaceValuativeExistence : SpaceValuativeExistenceStatement.{u} := by
  intro S X Y f _ hf huc A _ _ _ K _ _ _ s x y hx
  exact ValuativeExistence.exists_lift s f y hf huc x hx

end Langlands.AlgebraicGeometry.AlgebraicSpace
