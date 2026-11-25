/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.ChartIdeal

/-!
# Generation of the chart ideals for the finite-degree approximation

Numerators of chart-ideal generators generate `I_E^d · J` chart by chart
(`AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators`).
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section ChartMembership

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The image of a factored element under a ring homomorphism, commuted into the shape
of a power times a factor. Keeping the rings abstract makes this cheap to instantiate
at the section rings of blow-up charts. -/
private lemma ringHom_pow_mul_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {x y z : R} (d : ℕ) (h : y * x ^ d = z) :
    (f x) ^ d * f y = f z := by
  rw [← h, map_mul, map_pow, mul_comm]

/-- **Membership criterion for the pullback of `I_Eᵈ · J'` along an open-immersion
probe**, generic in the probe ring: an element factoring as `yPᵈ · yQ` with `yP` in the
pulled-back exceptional ideal and `yQ` in the pulled-back `J'` lies in the pullback of
the product. -/
lemma Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ)
    {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup) [IsOpenImmersion c]
    {x yP yQ : Γ(Spec S, ⊤)}
    (hP : yP ∈ ((I.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hQ : yQ ∈ (J'.comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hx : yP ^ d * yQ = x) :
    x ∈ ((((I.comap I.blowupMap) ^ d) * J').comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe I J' d c, ← hx]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hP d) hQ

/-- If the chart fraction `m/bᵈ` of a section `m ∈ I(V)ᵈ` lies in the chart model of
`J`, then the chart image of `m` lies in the ideal of sections of the pullback of
`I_Eᵈ · J` on the `b`-chart. This is the membership input both for the pushforward
candidate and for the final generation argument. -/
lemma Scheme.IdealSheafData.blowupChartSection_mem_of_chartFrac_mem
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (V : X.affineOpens)
    {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) {d : ℕ}
    {m : Γ(X, V.1)} (hm : m ∈ (I.ideal V) ^ d)
    (hfrac : AffineBlowup.chartFrac (I.ideal V) hb hm ∈ I.chartIdeal J V hb) :
    (I.blowupChartSection V hb).hom m ∈
      ((((I.comap I.blowupMap) ^ d) * J).comap (I.blowupChart V hb)).ideal
        ⟨⊤, isAffineOpen_top _⟩ :=
  Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe I J d (I.blowupChart V hb)
    ((I.ideal_comap_comap_blowupChart_self V hb).ge (Ideal.subset_span rfl))
    ((I.mem_chartIdeal_iff J V hb).mp hfrac)
    (ringHom_pow_mul_eq
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) b hb)))).inv.hom d
      (AffineBlowup.chartFrac_mul_awayAlgebraMap_pow (I.ideal V) hb hm))

end ChartMembership

section Generation

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- Transport of a generating set along an isomorphism of `CommRingCat`. -/
private lemma span_eq_of_map_iso_span {R S : CommRingCat.{u}} (E : R ≅ S)
    {P : Ideal R} {G : Set S} (h : Ideal.span G = P.map E.hom.hom) :
    P = Ideal.span (E.inv.hom '' G) := by
  have h1 := congrArg (Ideal.map E.inv.hom) h
  rw [Ideal.map_span, Ideal.map_map, ← CommRingCat.hom_comp, E.hom_inv_id,
    CommRingCat.hom_id, Ideal.map_id] at h1
  exact h1.symm

/-- **The generation step of Stacks Tag 0803**, ring-level form: if every generator
`μ` of an ideal spanned by `e '' G` satisfies `μ · f(b)ᵈ = f(m)` for some `m` in an
ideal `K` of the base ring, then `(g b)ᵈ · span (e '' G)` is contained in the
extension of `K` along the composite `g` of `f` and `e`. -/
private lemma span_pow_mul_span_le_map_explicit
    {A B C : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (K : Ideal A)
    (f : A →+* B)
    (e : B →+* C)
    (g : A →+* C)
    (hcomp : ∀ x : A, e (f x) = g x)
    (b : A) (d : ℕ) (G : Set B)
    (hgen : ∀ μ ∈ G, ∃ m ∈ K,
      μ * f b ^ d = f m) :
    Ideal.span {g b} ^ d * Ideal.span (e '' G) ≤ Ideal.map g K := by
  rw [Ideal.span_singleton_pow, Ideal.span_mul_span]
  refine Ideal.span_le.2 ?_
  intro z hz
  rcases Set.mem_mul.mp hz with ⟨x, hx, y, hy, hxy⟩
  have hx' : x = g b ^ d := by
    simpa only [Set.mem_singleton_iff] using hx
  subst x
  rcases hy with ⟨μ, hμ, hy⟩
  subst y
  rcases hgen μ hμ with ⟨m, hmK, hm⟩
  have heq : g b ^ d * e μ = g m := by
    calc
      g b ^ d * e μ
          = e (f b) ^ d * e μ := by
              rw [← hcomp b]
      _ = e (f b ^ d) * e μ := by
              rw [map_pow]
      _ = e (f b ^ d * μ) := by
              rw [map_mul]
      _ = e (μ * f b ^ d) := by
              rw [mul_comm (f b ^ d) μ]
      _ = e (f m) := by
              rw [hm]
      _ = g m := hcomp m
  rw [← hxy, heq]
  exact Ideal.mem_map_of_mem g hmK

/-- **The chartwise generation inequality** (Step 4 of the blueprint proof of Stacks
Tag 0803): if every generator of the chart model of `J` on the `b`-chart has a
numerator in `L(V)`, then the ideal of `I_Eᵈ · J` on the chart is contained in that of
the inverse image of `L`. -/
lemma Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (L : X.IdealSheafData)
    (V : X.affineOpens) {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) (d : ℕ)
    (G : Finset (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) b hb)))
    (hG : Ideal.span (G : Set _) = I.chartIdeal J V hb)
    (hgen : ∀ μ ∈ G, ∃ m' ∈ L.ideal V,
      μ * AffineBlowup.awayAlgebraMap
          (I.ideal V) (reesX (I.ideal V) b hb) b ^ d =
        AffineBlowup.awayAlgebraMap
          (I.ideal V) (reesX (I.ideal V) b hb) m') :
    (((I.comap I.blowupMap) ^ d) * J).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ ≤
      (L.comap I.blowupMap).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
  apply Scheme.IdealSheafData.ideal_le_of_comap_probe
    (I.blowupChart V hb)
  refine le_of_eq_of_le
    (Scheme.IdealSheafData.ideal_comap_pow_mul_comap_blowupChart
      I J d V hb) ?_
  refine le_of_le_of_eq ?_
    (Scheme.IdealSheafData.ideal_comap_comap_blowupChart
      I L V hb).symm
  refine le_of_eq_of_le
    (congrArg
      (fun Q ↦
        Ideal.span {(I.blowupChartSection V hb).hom b} ^ d * Q)
      (span_eq_of_map_iso_span
        (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away
              (reesGrading (I.ideal V))
              (reesX (I.ideal V) b hb))))
        hG)) ?_
  apply span_pow_mul_span_le_map_explicit
    (K := L.ideal V)
    (f :=
      AffineBlowup.awayAlgebraMap
        (I.ideal V) (reesX (I.ideal V) b hb))
    (e :=
      (Scheme.ΓSpecIso
        (CommRingCat.of
          (HomogeneousLocalization.Away
            (reesGrading (I.ideal V))
            (reesX (I.ideal V) b hb)))).inv.hom)
    (g := (I.blowupChartSection V hb).hom)
    (b := b)
    (d := d)
    (G := (G : Set _))
  · intro x
    rfl
  · intro μ hμ
    exact hgen μ hμ

end Generation

end AlgebraicGeometry
