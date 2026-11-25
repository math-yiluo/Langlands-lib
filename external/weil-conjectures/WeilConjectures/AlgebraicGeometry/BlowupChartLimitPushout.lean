/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TangentConeInitialForms
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Pushout squares of charts of blow-ups

For a commutative ring `A` and `x y : A`, let `blowupChart x y = A[T]/(xT - y)` be the chart of
the blow-up of `Spec A` along `(x, y)`. We record two pushout squares of commutative rings:

* base change of a localized chart: for a ring map `f : A → R` and `u_A ∈ A[T]/(xT - y)` with
  image `u ∈ R[T]/(f(x) T - f(y))`, the localization `(R[T]/(f(x)T - f(y)))[1/u]` is the pushout
  of `(A[T]/(xT - y))[1/u_A]` along `f`
  (`AlgebraicGeometry.isPushout_blowupChart_away`);
* the chart as a base change of the affine plane: for a ring map `g : R₀[X₀, X₁] → A`, the chart
  `A[T]/(g(X₀)T - g(X₁))` is the pushout of `A` along the map `R₀[X₀, X₁] → R₀[X₀, X₁]`,
  `X₀ ↦ X₀`, `X₁ ↦ X₀X₁` (the chart of the blow-up of the plane at the origin), the second
  variable going to `T` (`AlgebraicGeometry.isPushout_blowupChart_plane`).

## Main definitions

- `AlgebraicGeometry.blowupChartMap`: the map of charts induced by a ring map.
- `AlgebraicGeometry.planeChartMap`: the map `R₀[X₀, X₁] → R₀[X₀, X₁]`, `X₁ ↦ X₀X₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

section ChartMap

/-- The structure map `A → A[T]/(xT - y)` sends `r` to the class of the constant `r`. -/
lemma blowupChart_algebraMap_apply {A : Type u} [CommRing A] (x y r : A) :
    algebraMap A (blowupChart x y) r = Ideal.Quotient.mk _ (C r) :=
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A') {x y : A} {x' y' : A'}
  (hx : f x = x') (hy : f y = y')

/-- The ring map `A[T]/(xT - y) → A'[T]/(x'T - y')` induced by a ring map `f : A → A'` with
`f x = x'` and `f y = y'`. -/
noncomputable def blowupChartMap : blowupChart x y →+* blowupChart x' y' :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (Polynomial.mapRingHom f)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨q.map f, by simp [hx, hy]⟩)

/-- `blowupChartMap` on the class of a polynomial `p` is the class of `p.map f`. -/
@[simp]
lemma blowupChartMap_mk (p : A[X]) :
    blowupChartMap f hx hy (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (p.map f) :=
  rfl

/-- `blowupChartMap f` is compatible with the structure maps `A → A[T]/(xT - y)` and
`A' → A'[T]/(x'T - y')`. -/
lemma blowupChartMap_comp_algebraMap :
    (blowupChartMap f hx hy).comp (algebraMap A (blowupChart x y)) =
      (algebraMap A' (blowupChart x' y')).comp f := by
  ext a
  change blowupChartMap f hx hy (Ideal.Quotient.mk _ (C a)) = Ideal.Quotient.mk _ (C (f a))
  simp

end ChartMap

section Away

variable {A R : CommRingCat.{u}} (f : A ⟶ R) {x y : A} {x' y' : R} (hx : f.hom x = x')
  (hy : f.hom y = y') (uA : blowupChart x y)

/-- The universal property of `(R[T]/(x'T - y'))[1/u]` as the pushout of
`(A[T]/(xT - y))[1/u_A]` along `f : A → R`: existence. -/
lemma exists_blowupChart_away_desc {T : Type u} [CommRing T]
    (a : Localization.Away uA →+* T) (b : R →+* T)
    (hab : ∀ r : A, a (algebraMap (blowupChart x y) (Localization.Away uA)
      (algebraMap A (blowupChart x y) r)) = b (f.hom r)) :
    ∃ m : Localization.Away (blowupChartMap f.hom hx hy uA) →+* T,
      m.comp (Localization.awayMap (blowupChartMap f.hom hx hy) uA) = a ∧
      m.comp ((algebraMap (blowupChart x' y')
        (Localization.Away (blowupChartMap f.hom hx hy uA))).comp
          (algebraMap R (blowupChart x' y'))) = b := by
  set F := blowupChartMap f.hom hx hy
  let tA : Localization.Away uA := algebraMap (blowupChart x y) _ (Ideal.Quotient.mk _ X)
  let G : blowupChart x' y' →+* T := Ideal.Quotient.lift _ (Polynomial.eval₂RingHom b (a tA)) (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    have h0 : a (algebraMap (blowupChart x y) _ (algebraMap A (blowupChart x y) x)) * a tA -
        a (algebraMap (blowupChart x y) _ (algebraMap A (blowupChart x y) y)) = 0 := by
      have hz : Ideal.Quotient.mk (Ideal.span {C x * X - C y}) (C x * X - C y) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      have := congr(a (algebraMap (blowupChart x y) (Localization.Away uA) $hz))
      rw [map_sub, map_mul, map_sub, map_mul, map_sub, map_mul] at this
      simpa [tA, blowupChart_algebraMap_apply] using this
    rw [hab, hab, hx, hy] at h0
    simp [h0])
  have hGF : G.comp F = a.comp (algebraMap _ _) := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, F, blowupChartMap_mk, Polynomial.map_C, G,
        Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [← hab r, ← Ideal.Quotient.mk_algebraMap]
      rfl
    · simp [F, G, tA]
  have hu : IsUnit (G (F uA)) := by
    rw [← RingHom.comp_apply, hGF, RingHom.comp_apply]
    exact (IsLocalization.Away.algebraMap_isUnit uA).map a
  refine ⟨IsLocalization.Away.lift (F uA) hu, ?_, ?_⟩
  · apply IsLocalization.ringHom_ext (Submonoid.powers uA)
    rw [RingHom.comp_assoc, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, hGF]
  · rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
    ext r
    simp [G, ← Ideal.Quotient.mk_algebraMap]

/-- The universal property of `(R[T]/(x'T - y'))[1/u]` as the pushout of
`(A[T]/(xT - y))[1/u_A]` along `f : A → R`: uniqueness. -/
lemma blowupChart_away_hom_ext {T : Type u} [CommRing T]
    {m m' : Localization.Away (blowupChartMap f.hom hx hy uA) →+* T}
    (h₁ : m.comp (Localization.awayMap (blowupChartMap f.hom hx hy) uA) =
      m'.comp (Localization.awayMap (blowupChartMap f.hom hx hy) uA))
    (h₂ : m.comp ((algebraMap (blowupChart x' y') _).comp (algebraMap R (blowupChart x' y'))) =
      m'.comp ((algebraMap (blowupChart x' y') _).comp (algebraMap R (blowupChart x' y')))) :
    m = m' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (blowupChartMap f.hom hx hy uA))
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro r
    have := congr($h₂ r)
    simpa [← Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply R
      (blowupChart x' y') (Localization.Away (blowupChartMap f.hom hx hy uA))] using this
  · have := congr($h₁ (algebraMap (blowupChart x y) (Localization.Away uA) (Ideal.Quotient.mk _ X)))
    simpa [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq] using this


/-- **Base change of a localized chart of a blow-up.** For a ring map `f : A → R`, `x y : A`
with images `x' y'`, and `u_A` in the chart `A[T]/(xT - y)` with image `u` in
`R[T]/(x'T - y')`, the square
`A → (A[T]/(xT - y))[1/u_A]`, `A → R`, `R → (R[T]/(x'T - y'))[1/u]` is a pushout of rings. -/
theorem isPushout_blowupChart_away :
    IsPushout (CommRingCat.ofHom ((algebraMap (blowupChart x y) (Localization.Away uA)).comp
        (algebraMap A (blowupChart x y)))) f
      (CommRingCat.ofHom (Localization.awayMap (blowupChartMap f.hom hx hy) uA))
      (CommRingCat.ofHom ((algebraMap (blowupChart x' y')
        (Localization.Away (blowupChartMap f.hom hx hy uA))).comp
          (algebraMap R (blowupChart x' y')))) := by
  have hcond (s : PushoutCocone (CommRingCat.ofHom ((algebraMap (blowupChart x y)
      (Localization.Away uA)).comp (algebraMap A (blowupChart x y)))) f) (r : A) :
      s.inl.hom (algebraMap (blowupChart x y) (Localization.Away uA)
        (algebraMap A (blowupChart x y) r)) = s.inr.hom (f.hom r) := by
    simpa using congr($(s.condition).hom r)
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk ?_
    (fun s ↦ CommRingCat.ofHom (exists_blowupChart_away_desc f hx hy uA s.inl.hom s.inr.hom
      (hcond s)).choose) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · ext r
    have := congr($(blowupChartMap_comp_algebraMap f.hom hx hy) r)
    simp only [RingHom.comp_apply] at this
    simp [Localization.awayMap, IsLocalization.Away.map, this]
  · ext1
    exact (exists_blowupChart_away_desc f hx hy uA s.inl.hom s.inr.hom (hcond s)).choose_spec.1
  · ext1
    exact (exists_blowupChart_away_desc f hx hy uA s.inl.hom s.inr.hom (hcond s)).choose_spec.2
  · ext1
    have h := (exists_blowupChart_away_desc f hx hy uA s.inl.hom s.inr.hom (hcond s)).choose_spec
    apply blowupChart_away_hom_ext f hx hy uA
    · rw [CommRingCat.hom_ofHom, h.1]
      exact congr($(h₁).hom)
    · rw [CommRingCat.hom_ofHom, h.2]
      exact congr($(h₂).hom)

end Away

section Plane

variable {R₀ : Type u} [CommRing R₀]

/-- The map `R₀[X₀, X₁] → R₀[X₀, X₁]`, `X₀ ↦ X₀`, `X₁ ↦ X₀X₁`: the chart of the blow-up of the
affine plane at the origin, its second variable being `X₁/X₀`. -/
noncomputable def planeChartMap : MvPolynomial (Fin 2) R₀ →+* MvPolynomial (Fin 2) R₀ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1]

variable {A : CommRingCat.{u}} (g : CommRingCat.of (MvPolynomial (Fin 2) R₀) ⟶ A) (x y : A)

/-- The map `R₀[X₀, X₁] → A[T]/(g(X₀)T - g(X₁))`, `X₀ ↦ g(X₀)`, `X₁ ↦ T`, for a ring map
`g : R₀[X₀, X₁] → A`. -/
noncomputable def planeToBlowupChart : MvPolynomial (Fin 2) R₀ →+* blowupChart x y :=
  MvPolynomial.eval₂Hom ((algebraMap A _).comp (g.hom.comp MvPolynomial.C))
    ![algebraMap A _ x, Ideal.Quotient.mk _ Polynomial.X]

/-- **The chart of a blow-up as a base change of the chart of the plane.** For a ring map
`g : R₀[X₀, X₁] → A` with `x = g(X₀)`, `y = g(X₁)`, the chart `A[T]/(xT - y)` is the pushout of
`A` along `planeChartMap : X₁ ↦ X₀X₁`, the variable `X₁` going to `T`. -/
theorem isPushout_blowupChart_plane (hx : g.hom (MvPolynomial.X 0) = x)
    (hy : g.hom (MvPolynomial.X 1) = y) :
    IsPushout g (CommRingCat.ofHom planeChartMap)
      (CommRingCat.ofHom (algebraMap A (blowupChart x y)))
      (CommRingCat.ofHom (planeToBlowupChart g x y)) := by
  have hrel : Ideal.Quotient.mk (Ideal.span {C x * X - C y}) (C y) =
      Ideal.Quotient.mk _ (C x) * Ideal.Quotient.mk _ X := by
    rw [← map_mul, eq_comm, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hcond (s : PushoutCocone g (CommRingCat.ofHom (planeChartMap (R₀ := R₀))))
      (p : MvPolynomial (Fin 2) R₀) : s.inl.hom (g.hom p) = s.inr.hom (planeChartMap p) := by
    simpa using congr($(s.condition).hom p)
  -- the universal map out of the chart
  let desc (s : PushoutCocone g (CommRingCat.ofHom (planeChartMap (R₀ := R₀)))) :
      blowupChart x y →+* s.pt :=
    Ideal.Quotient.lift _ (Polynomial.eval₂RingHom s.inl.hom (s.inr.hom (MvPolynomial.X 1))) (by
      intro p hp
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      have h0 : s.inl.hom x * s.inr.hom (MvPolynomial.X 1) - s.inl.hom y = 0 := by
        simp [← hx, ← hy, hcond, planeChartMap]
      simp [h0])
  have hext {T : CommRingCat.{u}} (m m' : CommRingCat.of (blowupChart x y) ⟶ T)
      (h₁ : CommRingCat.ofHom (algebraMap A (blowupChart x y)) ≫ m =
        CommRingCat.ofHom (algebraMap A (blowupChart x y)) ≫ m')
      (h₂ : CommRingCat.ofHom (planeToBlowupChart g x y) ≫ m =
        CommRingCat.ofHom (planeToBlowupChart g x y) ≫ m') : m = m' := by
    ext1
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simpa [blowupChart_algebraMap_apply] using congr($(h₁).hom r)
    · simpa [planeToBlowupChart] using congr($(h₂).hom (MvPolynomial.X 1))
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk ?_ (fun s ↦ CommRingCat.ofHom (desc s))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · ext1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [planeChartMap, planeToBlowupChart]
    · intro i
      fin_cases i
      · simp [planeChartMap, planeToBlowupChart, hx]
      · simp [planeChartMap, planeToBlowupChart, blowupChart_algebraMap_apply, hy, hrel]
  · ext r
    simp [desc, blowupChart_algebraMap_apply]
  · ext1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [desc, planeToBlowupChart, blowupChart_algebraMap_apply, hcond, planeChartMap]
    · intro i
      fin_cases i
      · simp [desc, planeToBlowupChart, blowupChart_algebraMap_apply, hcond, planeChartMap, ← hx]
      · simp [desc, planeToBlowupChart]
  · apply hext
    · rw [h₁]
      ext r
      simp [desc, blowupChart_algebraMap_apply]
    · rw [h₂]
      ext1
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [desc, planeToBlowupChart, blowupChart_algebraMap_apply, hcond, planeChartMap]
      · intro i
        fin_cases i
        · simp [desc, planeToBlowupChart, blowupChart_algebraMap_apply, hcond, planeChartMap, ← hx]
        · simp [desc, planeToBlowupChart]

end Plane

end AlgebraicGeometry
