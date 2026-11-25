/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!

# Functoriality of the affine blow-up

For a ring homomorphism `φ : A →+* B` and ideals `I : Ideal A`, `J : Ideal B` with
`I.map φ = J`, we construct the graded ring homomorphism between the Rees algebras and the
induced morphism `AffineBlowup J ⟶ AffineBlowup I` of blow-ups, and establish its identity
and composition laws, its compatibility with the structure morphisms, and the chart-wise
pullback squares.

## Main definitions

- `AlgebraicGeometry.reesGrading.hom` — the graded ring homomorphism
  `reesGrading I →+*ᵍ reesGrading J`.
- `AlgebraicGeometry.AffineBlowup.hom` — the induced morphism of blow-ups.

## Main results

- `AlgebraicGeometry.AffineBlowup.hom_id` / `AlgebraicGeometry.AffineBlowup.hom_comp` —
  functoriality (blueprint: `lemma:nagata-affine-blowup-restrict-cocycle`, in composition
  form).
- `AlgebraicGeometry.AffineBlowup.hom_toSpec` — compatibility with the structure morphisms.
- `AlgebraicGeometry.AffineBlowup.isPullback_chart_hom` — the chart squares are pullbacks.

-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization Polynomial

namespace AlgebraicGeometry

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-- The image of an element of the Rees algebra of `I` under coefficientwise application of
`φ` lies in the Rees algebra of `I.map φ`. -/
lemma map_mem_reesAlgebra (φ : A →+* B) (h : I.map φ = J) (F : reesAlgebra I) :
    (F : A[X]).map φ ∈ reesAlgebra J := by
  rw [mem_reesAlgebra_iff]
  intro i
  rw [Polynomial.coeff_map, ← h, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem φ ((mem_reesAlgebra_iff I (F : A[X])).mp F.2 i)

/-- The graded ring homomorphism `reesGrading I →+*ᵍ reesGrading J` induced by a ring
homomorphism `φ : A →+* B` with `I.map φ = J`, given by coefficientwise application of `φ`.
(blueprint: `def:nagata-rees-localization-map`, generalized to arbitrary ring maps) -/
noncomputable def reesGrading.hom (φ : A →+* B) (h : I.map φ = J) :
    reesGrading I →+*ᵍ reesGrading J where
  toRingHom :=
    ((Polynomial.mapRingHom φ).comp (reesAlgebra I).subtype).codRestrict
      (reesAlgebra J) (map_mem_reesAlgebra φ h)
  map_mem {i x} hx := (mem_reesGrading_iff J).mpr fun k hk => by
    change ((x : A[X]).map φ).coeff k = 0
    rw [Polynomial.coeff_map, (mem_reesGrading_iff I).mp hx k hk, map_zero]

@[simp]
lemma reesGrading.coe_hom_apply (φ : A →+* B) (h : I.map φ = J) (F : reesAlgebra I) :
    (reesGrading.hom φ h F : B[X]) = (F : A[X]).map φ :=
  rfl

@[simp]
lemma reesGrading.hom_reesMonomial (φ : A →+* B) (h : I.map φ = J) {n : ℕ} (a : A)
    (ha : a ∈ I ^ n) :
    reesGrading.hom φ h (reesMonomial I a ha) =
      reesMonomial J (n := n) (φ a)
        (by rw [← h, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ ha) :=
  Subtype.ext <| by simp [Polynomial.map_monomial]

@[simp]
lemma reesGrading.hom_reesX (φ : A →+* B) (h : I.map φ = J) (a : A) (ha : a ∈ I) :
    reesGrading.hom φ h (reesX I a ha) =
      reesX J (φ a) (by rw [← h]; exact Ideal.mem_map_of_mem φ ha) :=
  reesGrading.hom_reesMonomial φ h a (by rwa [pow_one])

lemma reesGrading.hom_id : reesGrading.hom (RingHom.id A) (Ideal.map_id I) = .id (reesGrading I) :=
  GradedRingHom.ext fun F => Subtype.ext <| by simp

lemma reesGrading.hom_congr {φ φ' : A →+* B} (e : φ = φ') (h : I.map φ = J) :
    reesGrading.hom φ h = reesGrading.hom φ' (e ▸ h) := by
  subst e; rfl

lemma reesGrading.hom_comp (φ : A →+* B) (ψ : B →+* C) (h : I.map φ = J) (h' : J.map ψ = K) :
    (reesGrading.hom ψ h').comp (reesGrading.hom φ h) =
      reesGrading.hom (ψ.comp φ) (by rw [← Ideal.map_map, h, h']) :=
  GradedRingHom.ext fun F => Subtype.ext <| by simp [Polynomial.map_map]

/-- The irrelevant-ideal condition needed to apply `Proj.map` to `reesGrading.hom φ h`. -/
lemma reesGrading.irrelevant_le_map_hom (φ : A →+* B) (h : I.map φ = J) :
    HomogeneousIdeal.irrelevant (reesGrading J) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGrading.hom φ h) := by
  have key : ∀ i : ℕ, 0 < i → ∀ b : B, b ∈ (I ^ i).map φ → ∀ hb : b ∈ J ^ i,
      reesMonomial J b hb ∈
        ((HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGrading.hom φ h)).toIdeal := by
    intro i hi b hb'
    have hJi : ∀ {y : B}, y ∈ (I ^ i).map φ → y ∈ J ^ i := fun {y} hy => by
      rwa [Ideal.map_pow, h] at hy
    rw [Ideal.map] at hb'
    induction hb' using Submodule.span_induction with
    | mem b hbmem =>
      obtain ⟨a, ha, rfl⟩ := hbmem
      have ha' : a ∈ I ^ i := ha
      intro hb
      have e : reesMonomial J (φ a) hb = reesGrading.hom φ h (reesMonomial I a ha') :=
        (reesGrading.hom_reesMonomial φ h a ha').symm
      rw [HomogeneousIdeal.toIdeal_map, e]
      exact Ideal.mem_map_of_mem _
        (HomogeneousIdeal.mem_irrelevant_of_mem _ hi (reesMonomial_mem I a ha'))
    | zero =>
      intro hb
      have e : reesMonomial J (0 : B) hb = 0 := Subtype.ext (by simp)
      rw [e]
      exact zero_mem _
    | add u v hu hv ihu ihv =>
      intro hb
      have huJ : u ∈ J ^ i := hJi hu
      have hvJ : v ∈ J ^ i := hJi hv
      have e : reesMonomial J (u + v) hb = reesMonomial J u huJ + reesMonomial J v hvJ :=
        Subtype.ext (by simp [map_add])
      rw [e]
      exact add_mem (ihu huJ) (ihv hvJ)
    | smul c u hu ih =>
      intro hb
      have huJ : u ∈ J ^ i := hJi hu
      have e : reesMonomial J (c • u) hb =
          reesMonomial J (n := 0) c (by rw [pow_zero, Ideal.one_eq_top]; trivial) *
            reesMonomial J u huJ :=
        Subtype.ext (by simp [smul_eq_mul])
      rw [e]
      exact Ideal.mul_mem_left _ _ (ih huJ)
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi F hF
  obtain ⟨b, hb, rfl⟩ := (mem_reesGrading_iff_exists J).mp hF
  exact key i hi b (by rw [Ideal.map_pow, h]; exact hb) hb

/-- Functoriality of the affine blow-up: a ring homomorphism `φ : A →+* B` with
`I.map φ = J` induces a morphism `AffineBlowup J ⟶ AffineBlowup I`.
(blueprint: `def:nagata-affine-blowup-restriction-map`, generalized) -/
noncomputable def AffineBlowup.hom (φ : A →+* B) (h : I.map φ = J) :
    AffineBlowup J ⟶ AffineBlowup I :=
  Proj.map (reesGrading.hom φ h) (reesGrading.irrelevant_le_map_hom φ h)

lemma AffineBlowup.hom_id : AffineBlowup.hom (RingHom.id A) (Ideal.map_id I) = 𝟙 (AffineBlowup I) :=
  (Proj.map_congr reesGrading.hom_id (reesGrading.irrelevant_le_map_hom _ (Ideal.map_id I))
    (by simp)).trans Proj.map_id

lemma AffineBlowup.hom_congr {φ φ' : A →+* B} (e : φ = φ') (h : I.map φ = J) :
    AffineBlowup.hom φ h = AffineBlowup.hom φ' (e ▸ h) := by
  subst e; rfl

/-- Composition law for `AffineBlowup.hom`.
(blueprint: `lemma:nagata-affine-blowup-restrict-cocycle`) -/
lemma AffineBlowup.hom_comp (φ : A →+* B) (ψ : B →+* C) (h : I.map φ = J) (h' : J.map ψ = K) :
    AffineBlowup.hom (ψ.comp φ) (by rw [← Ideal.map_map, h, h']) =
      AffineBlowup.hom ψ h' ≫ AffineBlowup.hom φ h :=
  (Proj.map_congr (reesGrading.hom_comp φ ψ h h').symm
    (reesGrading.irrelevant_le_map_hom (ψ.comp φ) (by rw [← Ideal.map_map, h, h']))
    (HomogeneousIdeal.irrelevant_le_map_comp (reesGrading.irrelevant_le_map_hom φ h)
      (reesGrading.irrelevant_le_map_hom ψ h'))).trans
    (Proj.map_comp (reesGrading.hom φ h) (reesGrading.hom ψ h')
      (reesGrading.irrelevant_le_map_hom φ h)
      (reesGrading.irrelevant_le_map_hom ψ h'))

/-- The degree-zero square: the degree-zero component of `reesGrading.hom φ h` intertwines the
canonical identifications of the degree-zero subrings with the base rings.
(blueprint: `definition-admissible-blow-up--1`) -/
lemma gradeZeroRingHom_comp_reesGradingZero (φ : A →+* B) (h : I.map φ = J) :
    (reesGrading.hom φ h).gradeZeroRingHom.comp (reesGradingZero I).toRingHom =
      (reesGradingZero J).toRingHom.comp φ :=
  RingHom.ext fun a => Subtype.ext <| Subtype.ext <| by simp

/-- The blow-up square over `Spec` commutes.
(blueprint: `prop:nagata-affine-blowup-restrict`, compatibility part) -/
@[reassoc]
lemma AffineBlowup.hom_toSpec (φ : A →+* B) (h : I.map φ = J) :
    AffineBlowup.hom φ h ≫ AffineBlowup.toSpec I =
      AffineBlowup.toSpec J ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold AffineBlowup.hom AffineBlowup.toSpec
  rw [← Category.assoc, Proj.map_toSpecZero (reesGrading.hom φ h)
      (reesGrading.irrelevant_le_map_hom φ h),
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    gradeZeroRingHom_comp_reesGradingZero φ h]

/-- Chart compatibility: composed with `AffineBlowup.hom`, the chart at
`reesGrading.hom φ h x` is `Spec` of `HomogeneousLocalization.Away.map` followed by the
chart at `x`. -/
@[reassoc]
lemma AffineBlowup.chart_hom (φ : A →+* B) (h : I.map φ = J) (x : reesAlgebra I)
    (hx : x ∈ reesGrading I 1) :
    AffineBlowup.chart J (reesGrading.hom φ h x) ((reesGrading.hom φ h).map_mem hx) ≫
        AffineBlowup.hom φ h =
      Spec.map
          (CommRingCat.ofHom (HomogeneousLocalization.Away.map (reesGrading.hom φ h) x)) ≫
        AffineBlowup.chart I x hx :=
  Proj.awayι_comp_map (reesGrading.hom φ h) (reesGrading.irrelevant_le_map_hom φ h)
    one_pos x hx

/-- The chart squares of `AffineBlowup.hom` are pullbacks. -/
lemma AffineBlowup.isPullback_chart_hom (φ : A →+* B) (h : I.map φ = J) (x : reesAlgebra I)
    (hx : x ∈ reesGrading I 1) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (reesGrading.hom φ h) x)))
      (AffineBlowup.chart J (reesGrading.hom φ h x) ((reesGrading.hom φ h).map_mem hx))
      (AffineBlowup.chart I x hx)
      (AffineBlowup.hom φ h) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (AffineBlowup.chart_hom φ h x hx) ?_
  rw [AffineBlowup.opensRange_chart, AffineBlowup.opensRange_chart]
  exact Proj.map_preimage_basicOpen (reesGrading.hom φ h) (reesGrading.irrelevant_le_map_hom φ h) x

/-- `HomogeneousLocalization.Away.map` intertwines the canonical `A`- and `B`-algebra maps
of the chart rings. -/
lemma awayMap_awayAlgebraMap (φ : A →+* B) (h : I.map φ = J) (x : reesAlgebra I) :
    (HomogeneousLocalization.Away.map (reesGrading.hom φ h) x).comp
        (AffineBlowup.awayAlgebraMap I x) =
      (AffineBlowup.awayAlgebraMap J (reesGrading.hom φ h x)).comp φ := by
  unfold AffineBlowup.awayAlgebraMap
  rw [← RingHom.comp_assoc, HomogeneousLocalization.Away.map_comp_fromZeroRingHom,
    RingHom.comp_assoc, gradeZeroRingHom_comp_reesGradingZero φ h, ← RingHom.comp_assoc]

/-- The algebra structure on the chart ring of `AffineBlowup J` given by
`HomogeneousLocalization.Away.map` along `reesGrading.hom φ h`. -/
noncomputable instance AffineBlowup.awayMapAlgebra (φ : A →+* B) (h : I.map φ = J)
    (x : reesAlgebra I) :
    Algebra (HomogeneousLocalization.Away (reesGrading I) x)
      (HomogeneousLocalization.Away (reesGrading J) (reesGrading.hom φ h x)) :=
  (HomogeneousLocalization.Away.map (reesGrading.hom φ h) x).toAlgebra

@[simp]
lemma AffineBlowup.algebraMap_away_eq (φ : A →+* B) (h : I.map φ = J) (x : reesAlgebra I) :
    algebraMap (HomogeneousLocalization.Away (reesGrading I) x)
        (HomogeneousLocalization.Away (reesGrading J) (reesGrading.hom φ h x)) =
      HomogeneousLocalization.Away.map (reesGrading.hom φ h) x :=
  rfl

end AlgebraicGeometry
