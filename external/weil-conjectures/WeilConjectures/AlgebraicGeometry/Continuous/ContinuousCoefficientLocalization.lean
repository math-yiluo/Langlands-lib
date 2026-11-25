/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Localization of continuous integral coefficients -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Scheme

/-- Sheafified localization of integral functions is the rational function sheaf.

Source: Bhatt--Scholze, Lemma 6.8.2(2), and paragraph before Definition 6.8.6
(blueprint: lem-weil-pbc-continuous-coefficient-localization).

Proof: Include integral functions into field-valued functions pointwise. The constant
uniformizer is invertible in the latter ring, with its continuous constant inverse.
The localization universal property extends this map to fractions on each object;
uniqueness gives naturality, so sheafification extends it to a ring-sheaf map.
This map is injective before sheafification: a fraction mapping to zero has numerator
zero pointwise, since the uniformizer is nonzero in the field. For a rational section g,
the opens where g lies in the inverse nth uniformizer multiple of the integer ring
cover the test object, by the DVR decomposition of a nonzero field element as a unit
times an integral power of the uniformizer. These sets are open, because the integer
ring and all its nonzero scalar multiples are open in the valuation topology. Each is
a pro-etale object; affine quasi-compactness shows that the open cover is a covering
in the site's topology. On the nth open the section is the fraction with numerator
uniformizer^n times g. These fractions agree on overlaps by injectivity. Gluing and
the sheafification universal property give the inverse ring-sheaf map. On integral
numerators the original map is precisely the pointwise inclusion, as normalized here. -/
theorem continuousCoefficientLocalization (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    ∃ b : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E,
      integralCoefficientLocalizationNormalized l E X b.hom := by
  classical
  let := coefficientExtensionNormedField l E
  let A := Padic.coefficientExtensionIntegers l E
  let T := ULift.{u + 1, u} A
  let K := ULift.{u + 1, u} E
  let p := Padic.coefficientExtensionUniformizer l E
  let t : T := ULift.up p
  have hs := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  rcases hs with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen_exists, hassoc, hfactor⟩
  have hO : ∀ x : E, x ∈ A ↔ ‖x‖ ≤ 1 := hO
  have hm : ∀ x : A, x ∈ Padic.coefficientExtensionMaximalIdeal l E ↔
      ‖(x : E)‖ < 1 := hm
  have hgen : Ideal.span ({p} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    hgen_exists.choose_spec
  have hm0 : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ := hm0
  have hp0 : (p : E) ≠ 0 := by
    intro hz
    apply hm0
    rw [← hgen, show p = 0 from Subtype.ext hz, Ideal.span_singleton_zero]
  have hplt : ‖(p : E)‖ < 1 := by
    apply (hm p).mp
    rw [← hgen]
    exact Ideal.subset_span (Set.mem_singleton p)
  let inc (U : X.ProEtᵒᵖ) : C(U.unop.left, T) →+* C(U.unop.left, K) :=
    ((integralRationalCoefficientMap l E X).hom.app U).hom
  have hunit (U : X.ProEtᵒᵖ) : IsUnit (inc U (ContinuousMap.const U.unop.left t)) := by
    refine ⟨⟨ContinuousMap.const U.unop.left (ULift.up (p : E)),
      ContinuousMap.const U.unop.left (ULift.up (p : E)⁻¹), ?_, ?_⟩, rfl⟩
    · ext x
      exact mul_inv_cancel₀ hp0
    · ext x
      exact inv_mul_cancel₀ hp0
  let φ (U : X.ProEtᵒᵖ) : Localization.Away (ContinuousMap.const U.unop.left t) →+*
      C(U.unop.left, K) :=
    IsLocalization.Away.lift (ContinuousMap.const U.unop.left t) (hunit U)
  have hφ (U : X.ProEtᵒᵖ) (s : C(U.unop.left, T)) :
      φ U (algebraMap _ _ s) = inc U s := IsLocalization.Away.lift_eq _ _ _
  let f : localizedContinuousMapPresheaf X T t ⟶ (rationalCoefficientSheaf l X E).obj :=
    { app := fun U ↦ CommRingCat.ofHom (φ U)
      naturality := by
        intro U V g
        apply CommRingCat.hom_ext
        change (φ V).comp (localizedContinuousMapRestriction X T t g) =
          (continuousMapRestrictionRingHom K g.unop.left).comp (φ U)
        apply IsLocalization.ringHom_ext (Submonoid.powers (ContinuousMap.const U.unop.left t))
        apply RingHom.ext
        intro s
        change φ V (localizedContinuousMapRestriction X T t g (algebraMap _ _ s)) =
          continuousMapRestrictionRingHom K g.unop.left (φ U (algebraMap _ _ s))
        simp only [localizedContinuousMapRestriction, IsLocalization.Away.map,
          IsLocalization.map_eq, hφ]
        rfl }
  have hinj : Presheaf.IsLocallyInjective (ProEt.topology X) f := by
    apply Presheaf.isLocallyInjective_of_injective
    intro U
    apply (injective_iff_map_eq_zero (φ U)).mpr
    intro z hz
    let a := (IsLocalization.Away.sec (ContinuousMap.const U.unop.left t) z).1
    let n := (IsLocalization.Away.sec (ContinuousMap.const U.unop.left t) z).2
    have he : z * algebraMap _ _ (ContinuousMap.const U.unop.left t ^ n) =
        algebraMap _ _ a := IsLocalization.Away.sec_spec _ z
    have ha : a = 0 := by
      have hi := congrArg (φ U) he
      rw [map_mul, hz, zero_mul, hφ] at hi
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      apply Subtype.ext
      exact congrArg (fun s : C(U.unop.left, K) ↦ (s x).down) hi.symm
    rw [ha, map_zero] at he
    have hv : IsUnit ((algebraMap C(U.unop.left, T)
        (Localization.Away (ContinuousMap.const U.unop.left t)))
          (ContinuousMap.const U.unop.left t) ^ n) :=
      (IsLocalization.map_units (Localization.Away (ContinuousMap.const U.unop.left t))
        (⟨ContinuousMap.const U.unop.left t, 1, by simp⟩ :
          Submonoid.powers (ContinuousMap.const U.unop.left t))).pow n
    exact hv.mul_left_inj.mp (by simpa only [map_pow, zero_mul] using he)
  have hsurj : Presheaf.IsLocallySurjective (ProEt.topology X) f := by
    refine ⟨?_⟩
    intro U s
    change C(U.left, K) at s
    let O (n : ULift.{u} ℕ) : U.left.Opens :=
      ⟨{x | ‖(p : E) ^ n.down * (s x).down‖ < 1},
        isOpen_lt (continuous_const.mul (continuous_uliftDown.comp s.continuous)).norm
          continuous_const⟩
    apply ProEt.mem_topology_of_openImmersion _ (fun n ↦ (O n).ι)
    · intro x
      have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hplt).mul_const (s x).down
      have hh : ∃ n : ℕ, ‖(p : E) ^ n * (s x).down‖ < 1 := by
        have ht' := ht.norm
        simp only [zero_mul, norm_zero] at ht'
        exact (ht'.eventually (gt_mem_nhds zero_lt_one)).exists
      obtain ⟨n, hn⟩ := hh
      exact ⟨ULift.up n, ⟨⟨x, hn⟩, rfl⟩⟩
    · intro nn
      let V : X.ProEtᵒᵖ := Opposite.op (ProEt.ofOpenImmersion U (O nn).ι)
      let n := nn.down
      let a : C(V.unop.left, T) :=
        ⟨fun x ↦ ULift.up ⟨(p : E) ^ n * (s x.val).down,
          (hO _).mpr x.property.le⟩,
          continuous_uliftUp.comp (Continuous.subtype_mk
            (continuous_const.mul ((continuous_uliftDown.comp s.continuous).comp
              continuous_subtype_val)) _)⟩
      let z : Localization.Away (ContinuousMap.const V.unop.left t) :=
        IsLocalization.mk' _ a (⟨ContinuousMap.const V.unop.left t ^ n,
          n, rfl⟩ : Submonoid.powers (ContinuousMap.const V.unop.left t))
      have hzval : φ V z = continuousMapRestrictionRingHom K (O nn).ι s := by
        apply ContinuousMap.ext
        intro x
        apply ULift.ext
        have hz := IsLocalization.mk'_spec
          (R := C(V.unop.left, T))
          (S := Localization.Away (ContinuousMap.const V.unop.left t)) a
          (⟨ContinuousMap.const V.unop.left t ^ n, n, rfl⟩ :
            Submonoid.powers (ContinuousMap.const V.unop.left t))
        have hzmap := congrArg (φ V) hz
        rw [map_mul] at hzmap
        change φ V z * φ V (algebraMap _ _
          (ContinuousMap.const V.unop.left t ^ n)) = φ V (algebraMap _ _ a) at hzmap
        rw [hφ V _, hφ V a] at hzmap
        have hz' := congrArg (fun w : C(V.unop.left, K) ↦ (w x).down) hzmap
        change (φ V z x).down * (p : E) ^ n = (p : E) ^ n * (s x.val).down at hz'
        exact (mul_right_cancel₀ (pow_ne_zero n hp0))
          (hz'.trans (mul_comm _ _))
      exact ⟨z, hzval⟩
  let b : integralCoefficientLocalization l X E ⟶ rationalCoefficientSheaf l X E :=
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      (localizedContinuousMapPresheaf X T t) (rationalCoefficientSheaf l X E)).symm f
  have hb : toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t) ≫ b.hom = f :=
    by
      change ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
        (localizedContinuousMapPresheaf X T t) (rationalCoefficientSheaf l X E)) b = f
      exact Equiv.apply_symm_apply _ f
  have hbiso : IsIso b := by
    apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    constructor
    · change Presheaf.IsLocallyInjective _ b.hom
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t)), hb]
      exact hinj
    · change Presheaf.IsLocallySurjective _ b.hom
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (ProEt.topology X) (localizedContinuousMapPresheaf X T t)), hb]
      exact hsurj
  let := hbiso
  refine ⟨asIso b, ?_⟩
  intro U s x
  have hb' := congrArg (fun g ↦ g.app U (algebraMap C(U.unop.left, T)
    (Localization.Away (ContinuousMap.const U.unop.left t)) s)) hb
  change b.hom.app U _ = φ U (algebraMap C(U.unop.left, T)
    (Localization.Away (ContinuousMap.const U.unop.left t)) s) at hb'
  exact congrArg (fun w : C(U.unop.left, K) ↦ (w x).down) (hb'.trans (hφ U s))

end AlgebraicGeometry.Scheme
