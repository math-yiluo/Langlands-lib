import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Affine chart maps into `Proj`

For a graded ring `A`, a scheme `T`, a ring map `e : A →+* Γ(T, ⊤)` and a homogeneous
element `t` of positive degree with `e t` a unit, `chartMap` is the morphism
`T ⟶ Proj A` through the affine chart `D₊(t) = Spec A_(t)` sending `a / t ^ n` to
`e a * (e t)⁻¹ ^ n`. These chart maps are natural in `T`, do not depend on the chosen
chart, and are unchanged when `e` is rescaled by a unit according to degree.
-/

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

section awayLift

variable {R : Type*} [CommRing R]

/-- The ring map from the degree-zero part of `A_t` determined by `e` once `e t` is a unit. -/
def awayLift (e : A →+* R) (t : A) (hu : IsUnit (e t)) : Away 𝒜 t →+* R :=
  (Localization.awayLift e t hu).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

lemma awayLift_mk (e : A →+* R) {t : A} (hu : IsUnit (e t)) {d : ℕ} (ht : t ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift 𝒜 e t hu (Away.mk 𝒜 ht n a ha) = e a * ((hu.unit⁻¹ : Rˣ) : R) ^ n := by
  rw [awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  exact Localization.awayLift_mk e t a _ hu.mul_val_inv n

lemma awayLift_mk_eq_iff (e : A →+* R) {t : A} (hu : IsUnit (e t)) {d : ℕ} (ht : t ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) (r : R) :
    awayLift 𝒜 e t hu (Away.mk 𝒜 ht n a ha) = r ↔ e a = r * e t ^ n := by
  rw [awayLift_mk]
  constructor
  · rintro rfl
    rw [mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  · intro h
    rw [h, mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow, mul_one]

lemma awayLift_comp {R' : Type*} [CommRing R'] (g : R →+* R') (e : A →+* R) (t : A)
    (hu : IsUnit (e t)) :
    g.comp (awayLift 𝒜 e t hu) = awayLift 𝒜 (g.comp e) t (hu.map g) := by
  rw [awayLift, awayLift, ← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  ext a
  simp [Localization.awayLift, IsLocalization.Away.lift]

/-- Rescaling `e` by a unit according to degree does not change `awayLift`. -/
lemma awayLift_eq_of_scale (e e' : A →+* R) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hu : IsUnit (e t)) (hu' : IsUnit (e' t)) (c : R)
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → e' a = c ^ n * e a) :
    awayLift 𝒜 e' t hu' = awayLift 𝒜 e t hu := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht x
  rw [awayLift_mk_eq_iff, h _ a ha, h _ t ht, awayLift_mk, smul_eq_mul, mul_pow, ← pow_mul]
  have key : e a = e a * ((hu.unit⁻¹ : Rˣ) : R) ^ n * e t ^ n := by
    rw [mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
  calc c ^ (n * d) * e a
      = c ^ (n * d) * (e a * ((hu.unit⁻¹ : Rˣ) : R) ^ n * e t ^ n) := by rw [← key]
    _ = _ := by ring

/-- Compatibility of `awayLift` with the localization map `A_(t) → A_(t g)`. -/
lemma awayLift_comp_awayMap (e : A →+* R) {t g x : A} {d d' : ℕ} (ht : t ∈ 𝒜 d)
    (hg : g ∈ 𝒜 d') (hx : x = t * g) (hu : IsUnit (e t)) (hux : IsUnit (e x)) :
    (awayLift 𝒜 e x hux).comp (awayMap 𝒜 hg hx) = awayLift 𝒜 e t hu := by
  ext y
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht y
  rw [RingHom.comp_apply, awayMap_mk, awayLift_mk_eq_iff, awayLift_mk, map_mul, map_pow, hx,
    map_mul, mul_pow]
  calc e a * e g ^ n
      = e a * ((hu.unit⁻¹ : Rˣ) : R) ^ n * (e t ^ n * e g ^ n) := by
        rw [← mul_assoc, mul_assoc (e a), ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
    _ = _ := by ring

/-- `awayLift` determines `e` on homogeneous elements of degree a multiple of `deg t`,
when the values at `t` agree. -/
lemma eq_of_awayLift_eq (e e' : A →+* R) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hu : IsUnit (e t))
    (hu' : IsUnit (e' t)) (het : e t = e' t) (H : awayLift 𝒜 e t hu = awayLift 𝒜 e' t hu')
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) : e a = e' a := by
  have h1 := (awayLift_mk_eq_iff 𝒜 e hu ht n a ha _).mp rfl
  have h2 := (awayLift_mk_eq_iff 𝒜 e' hu' ht n a ha _).mp rfl
  rw [h1, h2, H, het]

/-- On the degree-zero part, `awayLift` restricts to `e`. -/
lemma awayLift_fromZeroRingHom (e : A →+* R) {t : A} (hu : IsUnit (e t)) (a : 𝒜 0) :
    awayLift 𝒜 e t hu (fromZeroRingHom 𝒜 (Submonoid.powers t) a) = e a := by
  rw [awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change Localization.awayLift e t hu (Localization.mk (a : A) 1) = e a
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.lift_eq _ _

end awayLift

section chartMap

variable {T : Scheme.{u}}

/-- The morphism `T ⟶ Proj A` through the affine chart `D₊(t)` determined by
`e : A →+* Γ(T, ⊤)` when `e t` is a unit. -/
def chartMap (e : A →+* Γ(T, ⊤)) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (hu : IsUnit (e t)) : T ⟶ Proj 𝒜 :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayLift 𝒜 e t hu)) ≫ Proj.awayι 𝒜 t ht hd

/-- The chart map does not depend on the degree witness. -/
lemma chartMap_congr (e : A →+* Γ(T, ⊤)) {t : A} {d d' : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (ht' : t ∈ 𝒜 d') (hd' : 0 < d') (hu : IsUnit (e t)) :
    chartMap 𝒜 e ht hd hu = chartMap 𝒜 e ht' hd' hu :=
  rfl

/-- Equal ring maps give equal chart maps. -/
lemma chartMap_ringHom_congr {e e' : A →+* Γ(T, ⊤)} (h : e = e') {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (hu : IsUnit (e t)) :
    chartMap 𝒜 e ht hd hu = chartMap 𝒜 e' ht hd (h ▸ hu) := by
  subst h
  rfl

/-- Chart maps are natural in the source scheme. -/
lemma comp_chartMap {T' : Scheme.{u}} (g : T' ⟶ T) (e : A →+* Γ(T, ⊤)) {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (e t)) :
    g ≫ chartMap 𝒜 e ht hd hu =
      chartMap 𝒜 (g.appTop.hom.comp e) ht hd (hu.map g.appTop.hom) := by
  rw [chartMap, chartMap, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
    ← awayLift_comp]
  rfl

/-- Rescaling `e` by a unit according to degree does not change the chart map. -/
lemma chartMap_eq_of_scale (e e' : A →+* Γ(T, ⊤)) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (hu : IsUnit (e t)) (hu' : IsUnit (e' t)) (c : Γ(T, ⊤))
    (h : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → e' a = c ^ n * e a) :
    chartMap 𝒜 e' ht hd hu' = chartMap 𝒜 e ht hd hu := by
  rw [chartMap, chartMap, awayLift_eq_of_scale 𝒜 e e' ht hu hu' c h]

/-- Passing to a smaller chart `D₊(t g) ⊆ D₊(t)` does not change the chart map. -/
lemma chartMap_eq_chartMap_mul (e : A →+* Γ(T, ⊤)) {t g x : A} {d d' : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (hg : g ∈ 𝒜 d') (hx : x = t * g) (hu : IsUnit (e t)) (hux : IsUnit (e x)) :
    chartMap 𝒜 e ht hd hu =
      chartMap 𝒜 e (hx ▸ SetLike.mul_mem_graded ht hg) (hd.trans_le (d.le_add_right d')) hux := by
  rw [chartMap, chartMap, ← Proj.SpecMap_awayMap_awayι 𝒜 ht hd hg hx,
    ← awayLift_comp_awayMap 𝒜 e ht hg hx hu hux, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]

/-- The chart map does not depend on the chart, as long as `e` is a unit on both. -/
lemma chartMap_eq (e : A →+* Γ(T, ⊤)) {t t' : A} {d d' : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (ht' : t' ∈ 𝒜 d') (hd' : 0 < d') (hu : IsUnit (e t)) (hu' : IsUnit (e t')) :
    chartMap 𝒜 e ht hd hu = chartMap 𝒜 e ht' hd' hu' := by
  have hux : IsUnit (e (t * t')) := by rw [map_mul]; exact hu.mul hu'
  rw [chartMap_eq_chartMap_mul 𝒜 e ht hd ht' rfl hu hux,
    chartMap_eq_chartMap_mul 𝒜 e ht' hd' ht (mul_comm t t') hu' hux]
  exact chartMap_congr 𝒜 e _ _ _ _ hux

/-- A chart map determines its ring map on the degree-zero part of `A_t`. -/
lemma awayLift_eq_of_chartMap_eq (e e' : A →+* Γ(T, ⊤)) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (hu : IsUnit (e t)) (hu' : IsUnit (e' t))
    (H : chartMap 𝒜 e ht hd hu = chartMap 𝒜 e' ht hd hu') :
    awayLift 𝒜 e t hu = awayLift 𝒜 e' t hu' := by
  rw [chartMap, chartMap, ← Category.assoc, ← Category.assoc, cancel_mono] at H
  have key : ∀ f : CommRingCat.of (Away 𝒜 t) ⟶ Γ(T, ⊤),
      (T.toSpecΓ ≫ Spec.map f).appTop = (Scheme.ΓSpecIso _).hom ≫ f := by
    intro f
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have H' := congrArg Scheme.Hom.appTop H
  rw [key, key, cancel_epi] at H'
  exact congrArg CommRingCat.Hom.hom H'

/-- The composite of a chart map with the projection to `Spec A₀`. -/
lemma chartMap_toSpecZero (e : A →+* Γ(T, ⊤)) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (hu : IsUnit (e t)) :
    chartMap 𝒜 e ht hd hu ≫ Proj.toSpecZero 𝒜 =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        ((awayLift 𝒜 e t hu).comp (fromZeroRingHom 𝒜 (Submonoid.powers t)))) := by
  rw [chartMap, Category.assoc, Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The preimage of a basic open `D₊(t')` under a chart map is the basic open of `e t'`. -/
lemma chartMap_preimage_basicOpen (e : A →+* Γ(T, ⊤)) {t t' : A} {d d' : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (ht' : t' ∈ 𝒜 d') (hd' : 0 < d') (hu : IsUnit (e t)) :
    chartMap 𝒜 e ht hd hu ⁻¹ᵁ Proj.basicOpen 𝒜 t' = T.basicOpen (e t') := by
  rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 ht hd ht' hd', SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen]
  change T.basicOpen (awayLift 𝒜 e t hu (Away.isLocalizationElem ht ht')) = _
  rw [awayLift_mk, Scheme.basicOpen_mul, map_pow, Scheme.basicOpen_pow _ _ hd,
    Scheme.basicOpen_of_isUnit _ ((hu.unit⁻¹).isUnit.pow _), inf_top_eq]

end chartMap

end Langlands.AlgebraicGeometry.LinearSystem
