import Langlands.Geometry.Analytic.AffineAnalytificationParametricEvaluation
import Langlands.Geometry.Analytic.SchemeAnalytificationSemilinearPoints
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing
import Langlands.Geometry.EtaleGaloisAction
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Joint continuity of scalar automorphisms on points of a scheme base change -/

noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Analytic.SchemeAnalytification

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open AffineSchemeAnalytification AffineAnalytification Filter Topology
open scoped TensorProduct
open Langlands.Geometry.EtaleGaloisAction (baseChange baseChangeMap)

variable {k : Type u} [Field k]

section Algebraic

variable {K : Type u} [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

private abbrev baseProjection : baseChange k K f ⟶ X := pullback.fst f (Spec.algebraMap k K)

/-- The structure map on the actual scheme base change. -/
abbrev baseChangedStructure : baseChange k K f ⟶ Spec (CommRingCat.of K) :=
  pullback.snd f (Spec.algebraMap k K)

private abbrev baseChangedChart (U : X.affineOpens) : (baseChange k K f).affineOpens := by
  let : IsAffineHom (baseProjection (K := K) f) := MorphismProperty.pullback_fst _ _
    (show IsAffineHom (Spec.algebraMap k K) from inferInstance)
  exact ⟨baseProjection (K := K) f ⁻¹ᵁ (U : X.Opens), U.2.preimage (baseProjection (K := K) f)⟩

private abbrev chartProjection (U : X.affineOpens) :
    (baseChangedChart (K := K) f U : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  morphismRestrict (baseProjection (K := K) f) (U : X.Opens)

private theorem isPullback_chartProjection (U : X.affineOpens) :
    IsPullback (chartProjection (K := K) f U)
      (structureMap (baseChangedStructure (K := K) f) (baseChangedChart f U))
      (structureMap f U) (Spec.algebraMap k K) :=
  (isPullback_morphismRestrict (baseProjection (K := K) f) (U : X.Opens)).paste_vert
    (IsPullback.of_hasPullback f (Spec.algebraMap k K))

private def chartScalar (U : X.affineOpens) (c : K) :
    Γ((baseChangedChart (K := K) f U : Scheme.{u}), ⊤) :=
  algebraMap K
    (CoordinateRing (structureMap (baseChangedStructure (K := K) f) (baseChangedChart f U))) c

private theorem chart_sections_generate (U : X.affineOpens)
    (a : CoordinateRing (structureMap (baseChangedStructure (K := K) f) (baseChangedChart f U))) :
    ∃ (n : ℕ) (c : Fin n → K) (b : Fin n → CoordinateRing (structureMap f U)),
      a = ∑ i, chartScalar f U (c i) * (chartProjection (K := K) f U).appTop (b i) := by
  let U' := baseChangedChart (K := K) f U
  let A := CoordinateRing (structureMap f U)
  let B := CoordinateRing (structureMap (baseChangedStructure (K := K) f) U')
  let i : CommRingCat.of A ⟶ CommRingCat.of B := (chartProjection (K := K) f U).appTop
  let j : CommRingCat.of K ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap K B)
  let h := isPushout_appTop_of_isPullback (isPullback_chartProjection (K := K) f U)
  have H : IsPushout (CommRingCat.ofHom (algebraMap k A))
      (CommRingCat.ofHom (algebraMap k K)) i j := by
    refine h.of_iso' (Scheme.ΓSpecIso _).symm (Iso.refl _) (Scheme.ΓSpecIso _).symm
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).symm
    · exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K))).symm
    · exact (Category.id_comp i).trans (Category.comp_id i).symm
    · exact (Category.comp_id _).symm
  let C := CommRingCat.pushoutCoconeIsColimit k K A
  let e : CommRingCat.of (K ⊗[k] A) ≅ CommRingCat.of B :=
    C.coconePointUniqueUpToIso H.flip.isColimit
  have hl : ∀ x : K, e.hom (x ⊗ₜ[k] (1 : A)) = j x := by
    intro x
    exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of B => g x)
      (C.comp_coconePointUniqueUpToIso_hom H.flip.isColimit WalkingSpan.left)
  have hr : ∀ x : A, e.hom ((1 : K) ⊗ₜ[k] x) = i x := by
    intro x
    exact congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of B => g x)
      (C.comp_coconePointUniqueUpToIso_hom H.flip.isColimit WalkingSpan.right)
  obtain ⟨z, hz⟩ := e.commRingCatIsoToRingEquiv.surjective (show B from a)
  obtain ⟨n, c, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  use n, c, b
  change a = ∑ l, j (c l) * i (b l)
  rw [← hz]
  change e.hom (∑ l, c l ⊗ₜ[k] b l) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← hl, ← hr, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem baseChangeMap_fst (σ : K ≃ₐ[k] K) :
    baseChangeMap f σ ≫ baseProjection f = baseProjection f := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The scheme automorphism of a field base change is semilinear on its structure map. -/
theorem baseChangeMap_over (σ : K ≃ₐ[k] K) :
    baseChangeMap f σ ≫ baseChangedStructure f =
      twistedStructureMap (baseChangedStructure f) σ.toRingEquiv :=
  pullback.lift_snd _ _ _

private theorem baseChangedChart_stable (U : X.affineOpens) (σ : K ≃ₐ[k] K) :
    (baseChangedChart (K := K) f U : (baseChange k K f).Opens) ≤
      baseChangeMap f σ ⁻¹ᵁ (baseChangedChart (K := K) f U : (baseChange k K f).Opens) := by
  change _ ≤ baseChangeMap f σ ⁻¹ᵁ (baseProjection f ⁻¹ᵁ (U : X.Opens))
  rw [← Scheme.Hom.comp_preimage, baseChangeMap_fst]

private abbrev chartAut (U : X.affineOpens) (σ : K ≃ₐ[k] K) :=
  (baseChangeMap f σ).resLE _ _ (baseChangedChart_stable f U σ)

private theorem chartAut_comp_projection (U : X.affineOpens) (σ : K ≃ₐ[k] K) :
    chartAut f U σ ≫ chartProjection f U = chartProjection f U := by
  rw [← cancel_mono (U : X.Opens).ι]
  simp only [Category.assoc, chartProjection, morphismRestrict_ι]
  rw [Scheme.Hom.resLE_comp_ι_assoc, baseChangeMap_fst]

private theorem chartAut_over (U : X.affineOpens) (σ : K ≃ₐ[k] K) :
    chartAut f U σ ≫ structureMap (baseChangedStructure f) (baseChangedChart f U) =
      twistedStructureMap (structureMap (baseChangedStructure f) (baseChangedChart f U))
        σ.toRingEquiv := by
  change chartAut f U σ ≫ _ ≫ baseChangedStructure f = (_ ≫ baseChangedStructure f) ≫ _
  rw [Scheme.Hom.resLE_comp_ι_assoc, baseChangeMap_over, Category.assoc]

private theorem chartAut_scalar (U : X.affineOpens) (σ : K ≃ₐ[k] K) (c : K) :
    (chartAut f U σ).appTop (chartScalar f U c) = chartScalar f U (σ c) := by
  let s := structureMap (baseChangedStructure (K := K) f) (baseChangedChart f U)
  let e := Scheme.ΓSpecIso (CommRingCat.of K)
  have w := chartAut_over f U σ
  have eq : s.appTop ≫ (chartAut f U σ).appTop =
      (semilinearSpecMap σ.toRingEquiv).appTop ≫ s.appTop := by
    rw [← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop]
  have eq' := congrArg (e.inv ≫ ·) eq
  let m : CommRingCat.of K ⟶ CommRingCat.of K := CommRingCat.ofHom σ.toRingEquiv.toRingHom
  change e.inv ≫ s.appTop ≫ (chartAut f U σ).appTop =
    e.inv ≫ (Spec.map m).appTop ≫ s.appTop at eq'
  rw [← Category.assoc e.inv (Spec.map m).appTop, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc] at eq'
  exact congrArg (fun g : CommRingCat.of K ⟶ Γ(_, ⊤) => g c) eq'

private theorem chartAut_section (U : X.affineOpens) (σ : K ≃ₐ[k] K)
    (b : CoordinateRing (structureMap f U)) :
    (chartAut f U σ).appTop ((chartProjection f U).appTop b) = (chartProjection f U).appTop b :=
  congrArg (fun g => g.appTop b) (chartAut_comp_projection f U σ)

end Algebraic

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType (baseChangedStructure (K := K) f)]

local notation "s" => baseChangedStructure (K := K) f

/-- The point map of the scheme base-change automorphism determined by an isometric
automorphism of the scalar field. -/
abbrev baseChangePointMap (σ : K ≃ₐ[k] K) (hσ : ∀ c, ‖σ c‖ = ‖c‖) :
    C(Space K s, Space K s) :=
  semilinearAnalytification K s s σ.toRingEquiv hσ (baseChangeMap f σ) (baseChangeMap_over f σ)

variable {T : Type v} [TopologicalSpace T] (σ : T → K ≃ₐ[k] K)
  (hnorm : ∀ t c, ‖σ t c‖ = ‖c‖) (hcont : ∀ c : K, Continuous (fun t => σ t c))

local notation "U′" => baseChangedChart (K := K) f

private abbrev localMapAt (t : T) (U : X.affineOpens) :
    C(LocalSpace K s (U′ U), LocalSpace K s (U′ U)) :=
  semilinearMorphismLocalMap K s s (σ t).toRingEquiv (hnorm t) (baseChangeMap f (σ t))
    (baseChangeMap_over f (σ t)) (baseChangedChart_stable f U (σ t))

include hcont in
private theorem continuous_localMapAt_eval (U : X.affineOpens)
    (a : CoordinateRing (structureMap s (U′ U))) :
    Continuous (fun p : T × LocalSpace K s (U′ U) =>
      pointSeminorm K (chartPresentation K s (U′ U)) (localMapAt K f σ hnorm p.1 U p.2) a) := by
  obtain ⟨n, c, b, hsum⟩ := chart_sections_generate f U a
  let d : Fin n → CoordinateRing (structureMap s (U′ U)) := fun i => (chartProjection f U).appTop (b i)
  let r : Fin n → T → K := fun i t => σ t (c i)
  have h := continuous_pointSeminorm_sum K (chartPresentation K s (U′ U))
    Finset.univ d r (fun i _ => hcont (c i))
  convert h using 1
  funext p
  rw [semilinearMorphismLocalMap_eval, hsum]
  change pointSeminorm K (chartPresentation K s (U′ U)) p.2
    ((chartAut f U (σ p.1)).appTop (∑ i, chartScalar f U (c i) * (chartProjection f U).appTop (b i))) = _
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, chartAut_scalar, chartAut_section]
  rfl

include hcont in
private theorem continuous_localMapAt (U : X.affineOpens) :
    Continuous (fun p : T × LocalSpace K s (U′ U) => localMapAt K f σ hnorm p.1 U p.2) :=
  (SeminormComparison.isEmbedding_pointSeminorm K (chartPresentation K s (U′ U))).continuous_iff.2
    (continuous_pi fun a => continuous_localMapAt_eval K f σ hnorm hcont U a)

include hcont in
private theorem continuous_baseChangePointMap :
    Continuous (fun p : T × Space K s => baseChangePointMap K f (σ p.1) (hnorm p.1) p.2) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨t, z⟩
  obtain ⟨U, hU, hzU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := baseProjection f (center K s z)) (U := ⊤) trivial
  let A : X.affineOpens := ⟨U, hU⟩
  obtain ⟨y, rfl⟩ : z ∈ Set.range (ι K s (U′ A)) := by
    rw [← OpenGluing.range_ι]
    exact hzU
  let e := Prod.map (@id T) (ι K s (U′ A))
  have he : IsOpenEmbedding e := IsOpenEmbedding.id.prodMap (OpenGluing.isOpenEmbedding_ι K s (U′ A))
  let g : T × Space K s → Space K s := fun p => baseChangePointMap K f (σ p.1) (hnorm p.1) p.2
  change Tendsto g (𝓝 (e (t, y))) (𝓝 (g (e (t, y))))
  rw [← he.map_nhds_eq, tendsto_map'_iff]
  have hg : g ∘ e = fun p => ι K s (U′ A) (localMapAt K f σ hnorm p.1 A p.2) := by
    funext p
    exact semilinearAnalytification_ι K s s (σ p.1).toRingEquiv (hnorm p.1) (baseChangeMap f (σ p.1))
      (baseChangeMap_over f (σ p.1)) (baseChangedChart_stable f A (σ p.1)) p.2
  rw [hg]
  rw [show g (e (t, y)) = _ from congrFun hg (t, y)]
  exact ((ι K s (U′ A)).continuous.comp (continuous_localMapAt K f σ hnorm hcont A)).continuousAt

/-- The point maps of the actual scheme automorphisms vary jointly continuously
in the automorphism parameter and the analytic point when each scalar orbit is continuous. -/
def baseChangePointEvaluation : C(T × Space K s, Space K s) :=
  ⟨fun p => baseChangePointMap K f (σ p.1) (hnorm p.1) p.2,
    continuous_baseChangePointMap K f σ hnorm hcont⟩

end Normed

end Langlands.Analytic.SchemeAnalytification
