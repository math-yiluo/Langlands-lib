import Langlands.Geometry.Analytic.AffineAnalytificationSemilinearPoints
import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof

/-! # Semilinear maps on points of scheme analytifications -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.AlgebraicGeometry
open AffineSchemeAnalytification

variable {K : Type u} [Field K]

/-- The map of the ground-field spectrum induced by a field automorphism. -/
abbrev semilinearSpecMap (σ : K ≃+* K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

@[simp] theorem semilinearSpecMap_one : semilinearSpecMap (1 : K ≃+* K) = 𝟙 _ := by
  change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 _
  exact Spec.map_id _

/-- The maps of spectra compose in the order determined by the pullback of sections. -/
theorem semilinearSpecMap_mul (σ τ : K ≃+* K) :
    semilinearSpecMap σ ≫ semilinearSpecMap τ = semilinearSpecMap (σ * τ) := by
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

instance (σ : K ≃+* K) : IsIso (semilinearSpecMap σ) :=
  (Scheme.Spec.mapIso σ.toCommRingCatIso.op).isIso_hom

/-- Compose a structure map with the automorphism of the ground-field spectrum. -/
abbrev twistedStructureMap {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (σ : K ≃+* K) :=
  f ≫ semilinearSpecMap σ

instance {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (σ : K ≃+* K) : LocallyOfFiniteType (twistedStructureMap f σ) :=
  inferInstanceAs (LocallyOfFiniteType (f ≫ semilinearSpecMap σ))

private theorem scalar_twist {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (σ : K ≃+* K) (c : K) :
    (algebraMap K (CoordinateRing (twistedStructureMap f σ)) c : Γ(X, ⊤)) =
      (algebraMap K (CoordinateRing f) (σ c) : Γ(X, ⊤)) := by
  let R := CommRingCat.of K
  let t : R ⟶ R := CommRingCat.ofHom σ.toRingHom
  have e : (Scheme.ΓSpecIso R).inv ≫ (f ≫ Spec.map t).appTop =
      t ≫ (Scheme.ΓSpecIso R).inv ≫ f.appTop := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact congrArg (fun g : R ⟶ Γ(X, ⊤) => g c) e

section Normed

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (s : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType s]
  (σ : K ≃+* K) (hσ : ∀ c, ‖σ c‖ = ‖c‖)

open AffineAnalytification in
private def retwistChart (U : X.affineOpens) :
    C(LocalSpace K f U, LocalSpace K (twistedStructureMap f σ) U) :=
  semilinearBaseMap K (chartPresentation K (twistedStructureMap f σ) U) (chartPresentation K f U)
    σ.toRingHom hσ (RingHom.id _) (fun c => by
      change (algebraMap K (CoordinateRing (structureMap (twistedStructureMap f σ) U)) c :
        Γ((U : X.Opens), ⊤)) = _
      have he : structureMap (twistedStructureMap f σ) U = twistedStructureMap (structureMap f U) σ :=
        (Category.assoc _ _ _).symm
      rw [he]
      exact scalar_twist (structureMap f U) σ c)

open AffineAnalytification in
private theorem retwistChart_eval (U : X.affineOpens) (y : LocalSpace K f U)
    (a : CoordinateRing (structureMap (twistedStructureMap f σ) U)) :
    pointSeminorm K (chartPresentation K (twistedStructureMap f σ) U)
      (retwistChart K f σ hσ U y) a = pointSeminorm K (chartPresentation K f U) y a :=
  pointSeminorm_semilinearBaseMap K _ _ _ _ _ _ y a

open AffineAnalytification in
private theorem retwistChart_localMap {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    (y : LocalSpace K f V) :
    retwistChart K f σ hσ U (localMap K f h y) =
      localMap K (twistedStructureMap f σ) h (retwistChart K f σ hσ V y) := by
  apply SeminormComparison.pointSeminorm_injective K (chartPresentation K (twistedStructureMap f σ) U)
  ext a
  let a₀ : CoordinateRing (structureMap f U) := a
  let fσ := twistedStructureMap f σ
  calc
    _ = pointSeminorm K (chartPresentation K f U) (localMap K f h y) a₀ :=
      retwistChart_eval K f σ hσ U _ a
    _ = pointSeminorm K (chartPresentation K f V) y (restriction f h a₀) :=
      pointSeminorm_baseMap K _ _ (restriction f h) y a₀
    _ = pointSeminorm K (chartPresentation K fσ V) (retwistChart K f σ hσ V y)
        (restriction fσ h a) := (retwistChart_eval K f σ hσ V y (restriction fσ h a)).symm
    _ = _ := (pointSeminorm_baseMap K _ _ (restriction fσ h) (retwistChart K f σ hσ V y) a).symm

/-- Changing the scalar map by an isometric automorphism leaves the underlying
seminorms intact on the affine charts of the glued analytic point space. -/
def retwistPoints : C(Space K f, Space K (twistedStructureMap f σ)) :=
  desc K f (fun U => (ι K (twistedStructureMap f σ) U).comp (retwistChart K f σ hσ U))
    (fun h y => by
      simp only [ContinuousMap.comp_apply, retwistChart_localMap, ι_localMap])

/-- A semilinear scheme morphism induces a continuous map of the glued analytifications. -/
def semilinearAnalytification (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ) :
    C(Space K f, Space K s) :=
  (MorphismExistence.analytification K (twistedStructureMap f σ) s g hg).comp
    (retwistPoints K f σ hσ)

/-- Affine chart map for a semilinear morphism of schemes. -/
def semilinearMorphismLocalMap (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ)
    {U : X.affineOpens} {V : Y.affineOpens} (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) :
    C(LocalSpace K f U, LocalSpace K s V) :=
  (morphismLocalMap K (twistedStructureMap f σ) s g hg h).comp (retwistChart K f σ hσ U)

/-- The global semilinear map restricts to the actual affine chart maps. -/
theorem semilinearAnalytification_ι (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ)
    {U : X.affineOpens} {V : Y.affineOpens} (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (y : LocalSpace K f U) :
    semilinearAnalytification K f s σ hσ g hg (ι K f U y) =
      ι K s V (semilinearMorphismLocalMap K f s σ hσ g hg h y) := by
  change MorphismExistence.analytification K (twistedStructureMap f σ) s g hg
      (ι K (twistedStructureMap f σ) U (retwistChart K f σ hσ U y)) = _
  exact MorphismExistence.isAnalytificationMap_analytification K (twistedStructureMap f σ) s g hg
    U V h (retwistChart K f σ hσ U y)

open AffineAnalytification in
/-- The value of a section at the image point is obtained by pulling back the section
along the actual scheme chart morphism. -/
theorem semilinearMorphismLocalMap_eval (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ)
    {U : X.affineOpens} {V : Y.affineOpens} (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
    (y : LocalSpace K f U) (a : CoordinateRing (structureMap s V)) :
    pointSeminorm K (chartPresentation K s V) (semilinearMorphismLocalMap K f s σ hσ g hg h y) a =
      pointSeminorm K (chartPresentation K f U) y ((g.resLE (V : Y.Opens) (U : X.Opens) h).appTop a) := by
  rw [semilinearMorphismLocalMap, ContinuousMap.comp_apply, morphismLocalMap, pointSeminorm_baseMap,
    retwistChart_eval, openCoordinateMap_apply]

private theorem retwistPoints_center (z : Space K f) :
    center K (twistedStructureMap f σ) (retwistPoints K f σ hσ z) = center K f z := by
  obtain ⟨U, y, rfl⟩ := exists_ι K f z
  change localCenter K (twistedStructureMap f σ) U (retwistChart K f σ hσ U y) = localCenter K f U y
  rw [localCenter_apply, localCenter_apply]
  apply congrArg (affineOpenMap U)
  apply PrimeSpectrum.ext
  ext a
  change (AffineAnalytification.pointSeminorm K (chartPresentation K (twistedStructureMap f σ) U)
      (retwistChart K f σ hσ U y) a = 0) ↔
    (AffineAnalytification.pointSeminorm K (chartPresentation K f U) y a = 0)
  exact Iff.of_eq (congrArg (· = 0) (retwistChart_eval K f σ hσ U y
    (show CoordinateRing (structureMap (twistedStructureMap f σ) U) from a)))

/-- Semilinear analytification sends a point above a scheme point to a point above its image. -/
theorem semilinearAnalytification_center (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ)
    (z : Space K f) : center K s (semilinearAnalytification K f s σ hσ g hg z) = g (center K f z) := by
  rw [semilinearAnalytification, ContinuousMap.comp_apply]
  have hc := MorphismCompatibility.center_map K (twistedStructureMap f σ) s
    (OpenGluing.range_ι K (twistedStructureMap f σ)) g hg _
    (MorphismExistence.isAnalytificationMap_analytification K (twistedStructureMap f σ) s g hg)
    (retwistPoints K f σ hσ z)
  exact hc.trans (congrArg g (retwistPoints_center K f σ hσ z))

open AffineAnalytification in
/-- When the automorphism of the field is the identity, semilinear analytification recovers
ordinary scheme analytification. -/
theorem semilinearAnalytification_one (g : X ⟶ Y) (hg : g ≫ s = f) :
    semilinearAnalytification K f s (1 : K ≃+* K) (fun _ => rfl) g
      (by simpa only [twistedStructureMap, semilinearSpecMap_one, Category.comp_id] using hg) =
      MorphismExistence.analytification K f s g hg := by
  ext z
  obtain ⟨U, V, h, y, rfl⟩ := MorphismCompatibility.exists_subordinate_chart K f
    (OpenGluing.range_ι K f) g z
  let h₁ : g ≫ s = twistedStructureMap f (1 : K ≃+* K) := by
    simpa only [twistedStructureMap, semilinearSpecMap_one, Category.comp_id] using hg
  have hm := semilinearAnalytification_ι K f s (1 : K ≃+* K) (fun _ => rfl) g h₁ h y
  refine hm.trans (Eq.trans ?_ (MorphismExistence.isAnalytificationMap_analytification K f s g hg
    U V h y).symm)
  apply congrArg (ι K s V)
  apply SeminormComparison.pointSeminorm_injective K (chartPresentation K s V)
  ext a
  rw [semilinearMorphismLocalMap_eval, morphismLocalMap, pointSeminorm_baseMap,
    openCoordinateMap_apply]

/-- The point map depends only on the specified base automorphism and scheme arrow. -/
theorem semilinearAnalytification_congr {σ τ : K ≃+* K}
    {hσ : ∀ c, ‖σ c‖ = ‖c‖} {hτ : ∀ c, ‖τ c‖ = ‖c‖}
    {g j : X ⟶ Y} {hg : g ≫ s = twistedStructureMap f σ}
    {hj : j ≫ s = twistedStructureMap f τ} (eσ : σ = τ) (e : g = j) :
    semilinearAnalytification K f s σ hσ g hg = semilinearAnalytification K f s τ hτ j hj := by
  subst τ
  subst j
  rfl

variable {Z : Scheme.{u}} (t : Z ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType t]
  (τ : K ≃+* K) (hτ : ∀ c, ‖τ c‖ = ‖c‖)
  (g : X ⟶ Y) (hg : g ≫ s = twistedStructureMap f σ)
  (j : Y ⟶ Z) (hj : j ≫ t = twistedStructureMap s τ)

omit [IsUltrametricDist K] [CompleteSpace K] [LocallyOfFiniteType f]
  [LocallyOfFiniteType s] [LocallyOfFiniteType t] in
include hg hj in
/-- The composite scheme map lies over the composite of the two specified spectrum maps. -/
theorem semilinear_comp_over : (g ≫ j) ≫ t = twistedStructureMap f (σ * τ) := by
  rw [Category.assoc, hj]
  change g ≫ s ≫ semilinearSpecMap τ = _
  rw [← Category.assoc, hg]
  change (f ≫ semilinearSpecMap σ) ≫ semilinearSpecMap τ = _
  rw [Category.assoc, semilinearSpecMap_mul]

open AffineAnalytification in
/-- The semilinear analytic point maps commute with composition. -/
theorem semilinearAnalytification_comp :
    (semilinearAnalytification K s t τ hτ j hj).comp (semilinearAnalytification K f s σ hσ g hg) =
      semilinearAnalytification K f t (σ * τ) (fun c => (hσ (τ c)).trans (hτ c)) (g ≫ j)
        (semilinear_comp_over K f s σ t τ g hg j hj) := by
  ext z
  obtain ⟨W, hW, hzW, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := j (g (center K f z))) (U := ⊤) trivial
  obtain ⟨V, hV, hzV, hVW⟩ := exists_isAffineOpen_mem_and_subset
    (x := g (center K f z)) (U := j ⁻¹ᵁ W) hzW
  obtain ⟨U, hU, hzU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (x := center K f z) (U := g ⁻¹ᵁ V) hzV
  let U₀ : X.affineOpens := ⟨U, hU⟩
  let V₀ : Y.affineOpens := ⟨V, hV⟩
  let W₀ : Z.affineOpens := ⟨W, hW⟩
  have hUV₀ : (U₀ : X.Opens) ≤ g ⁻¹ᵁ (V₀ : Y.Opens) := hUV
  have hVW₀ : (V₀ : Y.Opens) ≤ j ⁻¹ᵁ (W₀ : Z.Opens) := hVW
  have hUW₀ : (U₀ : X.Opens) ≤ (g ≫ j) ⁻¹ᵁ (W₀ : Z.Opens) :=
    fun _ hx => hVW (hUV hx)
  obtain ⟨y, rfl⟩ : z ∈ Set.range (ι K f U₀) := by
    rw [← OpenGluing.range_ι]
    exact hzU
  rw [ContinuousMap.comp_apply, semilinearAnalytification_ι K f s σ hσ g hg hUV₀,
    semilinearAnalytification_ι K s t τ hτ j hj hVW₀,
    semilinearAnalytification_ι K f t _ _ _ _ hUW₀]
  apply congrArg (ι K t W₀)
  apply SeminormComparison.pointSeminorm_injective K (chartPresentation K t W₀)
  ext a
  rw [semilinearMorphismLocalMap_eval, semilinearMorphismLocalMap_eval, semilinearMorphismLocalMap_eval]
  have he : g.resLE (V₀ : Y.Opens) (U₀ : X.Opens) hUV₀ ≫
      j.resLE (W₀ : Z.Opens) (V₀ : Y.Opens) hVW₀ =
      (g ≫ j).resLE (W₀ : Z.Opens) (U₀ : X.Opens) hUW₀ :=
    Scheme.Hom.resLE_comp_resLE g hUV₀ j hVW₀
  rw [← he, Scheme.Hom.comp_appTop]
  rfl

/-- A commuting square of scheme maps with linear horizontal maps and the same
semilinear base automorphism on its vertical maps analytifies to a commuting point square. -/
theorem semilinearAnalytification_naturality (a : X ⟶ Y) (ha : a ≫ s = f)
    (gX : X ⟶ X) (hX : gX ≫ f = twistedStructureMap f σ)
    (gY : Y ⟶ Y) (hY : gY ≫ s = twistedStructureMap s σ) (h : a ≫ gY = gX ≫ a) :
    (semilinearAnalytification K s s σ hσ gY hY).comp
        (MorphismExistence.analytification K f s a ha) =
      (MorphismExistence.analytification K f s a ha).comp
        (semilinearAnalytification K f f σ hσ gX hX) := by
  let ha₁ : a ≫ s = twistedStructureMap f (1 : K ≃+* K) := by
    simpa only [twistedStructureMap, semilinearSpecMap_one, Category.comp_id] using ha
  have e := semilinearAnalytification_one K f s a ha
  rw [← e, semilinearAnalytification_comp K f s 1 (fun _ => rfl) s σ hσ a ha₁ gY hY,
    semilinearAnalytification_comp K f f σ hσ s 1 (fun _ => rfl) gX hX a ha₁]
  exact semilinearAnalytification_congr K f s ((one_mul σ).trans (mul_one σ).symm) h

end Normed

end Langlands.Analytic.SchemeAnalytification
