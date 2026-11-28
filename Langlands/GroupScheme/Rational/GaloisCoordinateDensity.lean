import Langlands.GroupScheme.AffineWeilEmbeddingCoordinateMorphism
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Rational.GeometricPointHom
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.AffineWeilConnectedReductive
import Langlands.GroupScheme.Torus.TorusUnirationalityProof
import Langlands.GroupScheme.Dynamic.TripleParabolicSlice

/-! # Density of Galois coordinate triples -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme


/-- Three coordinates of a group scheme, each right-translated by a constant point. -/
def tripleTranslateMap {S : Scheme.{u}} {W H : GroupScheme S}
    (p₀ p₁ p₂ : W ⟶ H) (z₀ z₁ z₂ : Over.mk (𝟙 S) ⟶ H.X) : W.X ⟶ H.X ⊗ (H.X ⊗ H.X) :=
  lift (p₀.hom.hom * H.constantPoint z₀ W.X)
    (lift (p₁.hom.hom * H.constantPoint z₁ W.X) (p₂.hom.hom * H.constantPoint z₂ W.X))

/-- Three distinct coordinates of a finite product, right-translated by constant points, form a
surjective map: it has a section. -/
theorem tripleTranslateMap_surjective {S : Scheme.{u}} {W H : GroupScheme S}
    {I : Type u} [Finite I] (A : I → GroupScheme S)
    (e : W ≅ GroupScheme.pi A) (e₀ : ∀ i, A i ≅ H)
    (p : I → (W ⟶ H)) (hp : ∀ i, p i = e.hom ≫ Pi.π A i ≫ (e₀ i).hom)
    {i₀ i₁ i₂ : I} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (z₀ z₁ z₂ : Over.mk (𝟙 S) ⟶ H.X) :
    Function.Surjective (tripleTranslateMap (p i₀) (p i₁) (p i₂) z₀ z₁ z₂).left := by
  classical
  let Y := H.X ⊗ (H.X ⊗ H.X)
  let c₀ : Y ⟶ H.X := fst _ _ * (H.constantPoint z₀ Y)⁻¹
  let c₁ : Y ⟶ H.X := (snd _ _ ≫ fst _ _) * (H.constantPoint z₁ Y)⁻¹
  let c₂ : Y ⟶ H.X := (snd _ _ ≫ snd _ _) * (H.constantPoint z₂ Y)⁻¹
  let v (i : I) : Y ⟶ H.X :=
    if i = i₀ then c₀ else if i = i₁ then c₁ else if i = i₂ then c₂ else 1
  let r : Y ⟶ W.X := (piPointsEquiv A Y).symm
    (fun i => v i ≫ (e₀ i).inv.hom.hom) ≫ e.inv.hom.hom
  have hr (i : I) : r ≫ (p i).hom.hom = v i := by
    have hpi : e.inv ≫ p i = Pi.π A i ≫ (e₀ i).hom := by
      rw [hp, Iso.inv_hom_id_assoc]
    dsimp only [r]
    rw [Category.assoc, ← Grp.comp_hom_hom, hpi, Grp.comp_hom_hom,
      ← Category.assoc, piPointsEquiv_symm_π, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hv₀ : v i₀ = c₀ := by simp [v]
  have hv₁ : v i₁ = c₁ := by simp [v, h01.symm]
  have hv₂ : v i₂ = c₂ := by simp [v, h02.symm, h12.symm]
  have hsection : r ≫ tripleTranslateMap (p i₀) (p i₁) (p i₂) z₀ z₁ z₂ = 𝟙 Y := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, tripleTranslateMap, lift_fst, MonObj.comp_mul, hr, hv₀,
        constantPoint_naturality, Category.id_comp]
      simp only [c₀, inv_mul_cancel_right]
    · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, tripleTranslateMap, lift_snd_assoc, lift_fst,
          MonObj.comp_mul, hr, hv₁, constantPoint_naturality, Category.id_comp]
        simp only [c₁, inv_mul_cancel_right]
      · rw [Category.assoc, Category.assoc, tripleTranslateMap, lift_snd_assoc, lift_snd,
          MonObj.comp_mul, hr, hv₂, constantPoint_naturality, Category.id_comp]
        simp only [c₂, inv_mul_cancel_right]
  intro x
  use r.left x
  have hx := congrArg (fun f : Y ⟶ Y => f.left x) hsection
  have hi : (𝟙 Y.left) x = x := rfl
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left, hi] using hx

namespace GaloisCoordinateDensity

variable (K M : Type u) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M]
  (G : GroupScheme (Spec (CommRingCat.of K)))

private abbrev b := algebraBaseMap K M
private abbrev geometricGroup := (baseChange (b K M)).obj G

variable [IsAffine (geometricGroup K M G).X.left]
  [LocallyOfFiniteType (geometricGroup K M G).X.hom]

private abbrev restriction := AffineWeil.groupScheme K M (geometricGroup K M G)

private abbrev coefficientMap (τ : M →ₐ[K] M) :=
  Spec.map (CommRingCat.ofHom τ.toRingHom)

private abbrev coefficientIso (τ : M →ₐ[K] M) :=
  descentBaseChangeIso (b K M) (coefficientMap K M τ)
    (AffineWeil.embeddingBaseMap_over K M M τ) G

/-- A coordinate of the geometric Weil restriction in the original geometric group. -/
private def coefficientProjection (τ : M →ₐ[K] M) :
    (baseChange (b K M)).obj (restriction K M G) ⟶ geometricGroup K M G :=
  EmbeddingProduct.evaluationComponent (b K M) (b K M) (coefficientMap K M τ)
    (AffineWeil.embeddingBaseMap_over K M M τ) (restriction K M G) (geometricGroup K M G)
    (AffineWeil.evaluation K M (geometricGroup K M G)) ≫ (coefficientIso K M G τ).hom

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientProjection_on_extended
    (q : rationalPoints (restriction K M G)) (τ : M →ₐ[K] M) :
    baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (coefficientProjection K M G τ).hom.hom) =
      ringTestMap K τ ≫ baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom) := by
  let a := coefficientMap K M τ
  let W := restriction K M G
  let H := geometricGroup K M G
  let v := geometricRationalPointHom (K := M) W q
  let e := AffineWeil.evaluation K M H
  let h := AffineWeil.embeddingBaseMap_over K M M τ
  let p := EmbeddingProduct.intermediateProjection (b K M) (b K M) a h W
  have hv₁ : v.left ≫ pullback.fst W.X.hom (b K M) = b K M ≫ q.left :=
    baseChangeSectionHom_fst (b K M) W q
  have hv₂ : v.left ≫ pullback.snd W.X.hom (b K M) = 𝟙 (Spec (CommRingCat.of M)) := Over.w v
  have hvp : v.left ≫ p = a ≫ v.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, EmbeddingProduct.intermediateProjection_fst, hv₁,
        Category.assoc, hv₁, ← Category.assoc, h]
    · calc
        _ = a := by
          rw [Category.assoc, EmbeddingProduct.intermediateProjection_snd, ← Category.assoc,
            hv₂]
          exact Category.id_comp a
        _ = _ := by
          rw [Category.assoc, hv₂]
          exact (Category.comp_id a).symm
  have hc : (coefficientProjection K M G τ).hom.hom.left ≫ pullback.fst G.X.hom (b K M) =
      p ≫ e.hom.hom.left ≫ pullback.fst G.X.hom (b K M) := by
    simp only [coefficientProjection, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      coefficientIso, descentBaseChangeIso_hom_fst]
    change _ ≫ pullback.fst H.X.hom a ≫ pullback.fst G.X.hom (b K M) = _
    rw [← Category.assoc, EmbeddingProduct.evaluationComponent_fst, Category.assoc]
  apply Over.OverMorphism.ext
  simp only [baseChangeBasePointsEquiv_left, Over.comp_left, ringTestMap_left]
  change (v.left ≫ (coefficientProjection K M G τ).hom.hom.left) ≫
      pullback.fst G.X.hom (b K M) =
    a ≫ (v.left ≫ e.hom.hom.left) ≫ pullback.fst G.X.hom (b K M)
  rw [Category.assoc, hc, ← Category.assoc v.left p, hvp]
  simp only [Category.assoc]

section Split

variable [IsGalois K M]

private abbrev factors := AffineWeil.embeddingFactor K M M (geometricGroup K M G)

private theorem embeddingEvaluation_bijective :
    Function.Bijective (embeddingEvaluation K M M) :=
  embeddingEvaluationStatement K M M (Normal.splits (inferInstance : Normal K M))

private def restrictionProductIso :
    (baseChange (b K M)).obj (restriction K M G) ≅ GroupScheme.pi (factors K M G) :=
  AffineWeil.embeddingProductIsoOfBijective K M M (embeddingEvaluation_bijective K M)
    (geometricGroup K M G)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
private theorem coefficientProjection_eq_pi (τ : M →ₐ[K] M) :
    coefficientProjection K M G τ =
      (restrictionProductIso K M G).hom ≫ Pi.π (factors K M G) τ ≫
        (coefficientIso K M G τ).hom := by
  have hτ := AffineWeil.embeddingProductIsoOfBijective_hom_π K M M
    (embeddingEvaluation_bijective K M) (geometricGroup K M G) τ
  exact (congrArg (fun f => f ≫ (coefficientIso K M G τ).hom) hτ.symm).trans
    (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_hasDenseRationalPoints [Infinite K]
    (hH : IsConnectedReductive (geometricGroup K M G)) :
    HasDenseRationalPoints K (restriction K M G).X := by
  have hW : IsConnectedReductive (restriction K M G) :=
    AffineWeil.isConnectedReductive_restriction K M _ hH
  exact IsUnirational.hasDenseRationalPoints
    (ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality _ hW)

end Split


section Triple

variable [IsGalois K M]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem tripleCoordinate_surjective
    {τ₀ τ₁ τ₂ : M →ₐ[K] M} (h01 : τ₀ ≠ τ₁) (h02 : τ₀ ≠ τ₂) (h12 : τ₁ ≠ τ₂)
    (z₀ z₁ z₂ : Over.mk (𝟙 (Spec (CommRingCat.of M))) ⟶ (geometricGroup K M G).X) :
    Function.Surjective (tripleTranslateMap (coefficientProjection K M G τ₀)
      (coefficientProjection K M G τ₁) (coefficientProjection K M G τ₂) z₀ z₁ z₂).left :=
  tripleTranslateMap_surjective (factors K M G) (restrictionProductIso K M G)
    (coefficientIso K M G) (coefficientProjection K M G) (coefficientProjection_eq_pi K M G)
    h01 h02 h12 z₀ z₁ z₂

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_component
    [IsAffine (geometricGroup K M G).X.left] [LocallyOfFiniteType (geometricGroup K M G).X.hom]
    (q : rationalPoints (restriction K M G)) (τ : M →ₐ[K] M) (y : ringTest K M ⟶ G.X) :
    baseChangeBasePointsEquiv (b K M) G
        (geometricRationalPointHom (K := M) (restriction K M G) q ≫
          ((coefficientProjection K M G τ).hom.hom *
            (geometricGroup K M G).constantPoint ((baseChangeBasePointsEquiv (b K M) G).symm y)
              ((baseChange (b K M)).obj (restriction K M G)).X)) =
      (ringTestMap K τ ≫ baseChangeBasePointsEquiv (b K M) G
          (geometricRationalPointHom (K := M) (restriction K M G) q ≫
            (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom)) * y := by
  have hconst : geometricRationalPointHom (K := M) (restriction K M G) q ≫
      (geometricGroup K M G).constantPoint ((baseChangeBasePointsEquiv (b K M) G).symm y)
        ((baseChange (b K M)).obj (restriction K M G)).X =
      (baseChangeBasePointsEquiv (b K M) G).symm y := by
    rw [constantPoint_naturality]
    exact Category.id_comp _
  rw [MonObj.comp_mul, map_mul, hconst, MulEquiv.apply_symm_apply,
    coefficientProjection_on_extended K M G q τ]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_value_fst
    (q : rationalPoints (restriction K M G)) (τ₀ τ₁ τ₂ : M →ₐ[K] M)
    (z₀ z₁ z₂ : Over.mk (𝟙 (Spec (CommRingCat.of M))) ⟶ (geometricGroup K M G).X) :
    (geometricRationalPointHom (K := M) (restriction K M G) q ≫
        tripleTranslateMap (coefficientProjection K M G τ₀)
          (coefficientProjection K M G τ₁) (coefficientProjection K M G τ₂) z₀ z₁ z₂) ≫
        fst _ _ =
      geometricRationalPointHom (K := M) (restriction K M G) q ≫
        ((coefficientProjection K M G τ₀).hom.hom *
          (geometricGroup K M G).constantPoint z₀
            ((baseChange (b K M)).obj (restriction K M G)).X) := by
  rw [Category.assoc, tripleTranslateMap, lift_fst]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_value_snd_fst
    (q : rationalPoints (restriction K M G)) (τ₀ τ₁ τ₂ : M →ₐ[K] M)
    (z₀ z₁ z₂ : Over.mk (𝟙 (Spec (CommRingCat.of M))) ⟶ (geometricGroup K M G).X) :
    (geometricRationalPointHom (K := M) (restriction K M G) q ≫
        tripleTranslateMap (coefficientProjection K M G τ₀)
          (coefficientProjection K M G τ₁) (coefficientProjection K M G τ₂) z₀ z₁ z₂) ≫
        snd _ _ ≫ fst _ _ =
      geometricRationalPointHom (K := M) (restriction K M G) q ≫
        ((coefficientProjection K M G τ₁).hom.hom *
          (geometricGroup K M G).constantPoint z₁
            ((baseChange (b K M)).obj (restriction K M G)).X) := by
  rw [Category.assoc, tripleTranslateMap, lift_snd_assoc, lift_fst]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_value_snd_snd
    (q : rationalPoints (restriction K M G)) (τ₀ τ₁ τ₂ : M →ₐ[K] M)
    (z₀ z₁ z₂ : Over.mk (𝟙 (Spec (CommRingCat.of M))) ⟶ (geometricGroup K M G).X) :
    (geometricRationalPointHom (K := M) (restriction K M G) q ≫
        tripleTranslateMap (coefficientProjection K M G τ₀)
          (coefficientProjection K M G τ₁) (coefficientProjection K M G τ₂) z₀ z₁ z₂) ≫
        snd _ _ ≫ snd _ _ =
      geometricRationalPointHom (K := M) (restriction K M G) q ≫
        ((coefficientProjection K M G τ₂).hom.hom *
          (geometricGroup K M G).constantPoint z₂
            ((baseChange (b K M)).obj (restriction K M G)).X) := by
  rw [Category.assoc, tripleTranslateMap, lift_snd_assoc, lift_snd]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_symm_component
    (q : rationalPoints (restriction K M G)) (τ : M →ₐ[K] M) (y : ringTest K M ⟶ G.X) :
    geometricRationalPointHom (K := M) (restriction K M G) q ≫
        ((coefficientProjection K M G τ).hom.hom *
          (geometricGroup K M G).constantPoint ((baseChangeBasePointsEquiv (b K M) G).symm y)
            ((baseChange (b K M)).obj (restriction K M G)).X) =
      (baseChangeBasePointsEquiv (b K M) G).symm
        ((ringTestMap K τ ≫ baseChangeBasePointsEquiv (b K M) G
          (geometricRationalPointHom (K := M) (restriction K M G) q ≫
            (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom)) * y) := by
  rw [← tripleCoordinate_component K M G q τ y, MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem tripleCoordinate_value
    (q : rationalPoints (restriction K M G)) (τ₀ τ₁ τ₂ : M →ₐ[K] M)
    (y₀ y₁ y₂ : ringTest K M ⟶ G.X) :
    geometricRationalPointHom (K := M) (restriction K M G) q ≫
        tripleTranslateMap (coefficientProjection K M G τ₀)
          (coefficientProjection K M G τ₁) (coefficientProjection K M G τ₂)
          ((baseChangeBasePointsEquiv (b K M) G).symm y₀)
          ((baseChangeBasePointsEquiv (b K M) G).symm y₁)
          ((baseChangeBasePointsEquiv (b K M) G).symm y₂) =
      lift ((baseChangeBasePointsEquiv (b K M) G).symm
          ((ringTestMap K τ₀ ≫ baseChangeBasePointsEquiv (b K M) G
            (geometricRationalPointHom (K := M) (restriction K M G) q ≫
              (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom)) * y₀))
        (lift ((baseChangeBasePointsEquiv (b K M) G).symm
          ((ringTestMap K τ₁ ≫ baseChangeBasePointsEquiv (b K M) G
            (geometricRationalPointHom (K := M) (restriction K M G) q ≫
              (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom)) * y₁))
          ((baseChangeBasePointsEquiv (b K M) G).symm
            ((ringTestMap K τ₂ ≫ baseChangeBasePointsEquiv (b K M) G
              (geometricRationalPointHom (K := M) (restriction K M G) q ≫
                (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom)) * y₂))) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [tripleCoordinate_value_fst, lift_fst, tripleCoordinate_symm_component]
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, tripleCoordinate_value_snd_fst, Category.assoc, lift_snd_assoc,
      lift_fst, tripleCoordinate_symm_component]
  · rw [Category.assoc, tripleCoordinate_value_snd_snd, Category.assoc, lift_snd_assoc,
      lift_snd, tripleCoordinate_symm_component]

end Triple

end GaloisCoordinateDensity


open GaloisCoordinateDensity in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 400000 in
/-- For a finite Galois extension `M/K` of an infinite field and three distinct
automorphisms `τ₀, τ₁, τ₂`, the triples `(τ₀(f) y₀, τ₁(f) y₁, τ₂(f) y₂)`, for `f` ranging over
the `M`-points of a connected reductive `K`-group `G` and fixed `M`-points `yᵢ`, are Zariski
dense in the cube of the scalar extension of `G` to `M`. -/
theorem galoisTripleCoordinateDensity
    (K M : Type u) [Field K] [Infinite K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsConnectedReductive G)
    (τ₀ τ₁ τ₂ : M ≃ₐ[K] M) (h01 : τ₀ ≠ τ₁) (h02 : τ₀ ≠ τ₂) (h12 : τ₁ ≠ τ₂)
    (y₀ y₁ y₂ : ringTest K M ⟶ G.X) :
    Dense (⋃ f : (ringTest K M ⟶ G.X),
      Set.range (lift ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
          ((ringTestMap K τ₀.toAlgHom ≫ f) * y₀))
        (lift ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
          ((ringTestMap K τ₁.toAlgHom ≫ f) * y₁))
          ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
            ((ringTestMap K τ₂.toAlgHom ≫ f) * y₂))) :
        Over.mk (𝟙 (Spec (CommRingCat.of M))) ⟶
          groupCube ((baseChange (algebraBaseMap K M)).obj G)).left) := by
  have hH : IsConnectedReductive (geometricGroup K M G) :=
    connectedReductiveFieldExtensionStatement K M G hG
  have : IsAffineHom (geometricGroup K M G).X.hom := hH.isAffineHom
  have : IsAffine (geometricGroup K M G).X.left :=
    isAffine_of_isAffineHom (geometricGroup K M G).X.hom
  have : LocallyOfFiniteType (geometricGroup K M G).X.hom := by
    have : Smooth (geometricGroup K M G).X.hom := hH.smooth
    infer_instance
  have hne {σ σ' : M ≃ₐ[K] M} (h : σ ≠ σ') : σ.toAlgHom ≠ σ'.toAlgHom := by
    intro h'
    exact h (AlgEquiv.ext fun x => DFunLike.congr_fun h' x)
  have hsurj := tripleCoordinate_surjective K M G (hne h01) (hne h02) (hne h12)
    ((baseChangeBasePointsEquiv (b K M) G).symm y₀)
    ((baseChangeBasePointsEquiv (b K M) G).symm y₁)
    ((baseChangeBasePointsEquiv (b K M) G).symm y₂)
  have hdenseW := restriction_hasDenseRationalPoints K M G hH
  refine (hsurj.denseRange.dense_image (Scheme.Hom.continuous _)
    (dense_geometricRationalPointHom (K := M) (restriction K M G) hdenseW)).mono ?_
  rintro x ⟨w, hw, rfl⟩
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hw
  obtain ⟨a, rfl⟩ := hq
  refine Set.mem_iUnion.mpr ⟨baseChangeBasePointsEquiv (b K M) G
    (geometricRationalPointHom (K := M) (restriction K M G) q ≫
      (AffineWeil.evaluation K M (geometricGroup K M G)).hom.hom), ⟨a, ?_⟩⟩
  rw [← tripleCoordinate_value K M G q τ₀.toAlgHom τ₁.toAlgHom τ₂.toAlgHom y₀ y₁ y₂,
    Over.comp_left, Scheme.Hom.comp_apply]

end Langlands.GroupScheme
