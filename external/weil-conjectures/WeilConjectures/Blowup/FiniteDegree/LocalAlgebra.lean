/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Algebra

/-!
# Local algebra for the finite-degree approximation on the blow-up

Algebraic lemmas on chart fractions, and the combinators over `Finset`s used by the
finite-degree approximation.
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section LocalAlgebra

open HomogeneousLocalization Polynomial

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- Every element of the chart ring of the affine blow-up is a chart fraction
`g/aⁿ` for some degree `n` and some `g ∈ I₀ ^ n`. -/
lemma AffineBlowup.chartFrac_surjective {a : A} (ha : a ∈ I₀)
    (x : HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)) :
    ∃ (n : ℕ) (g : A) (hg : g ∈ I₀ ^ n), AffineBlowup.chartFrac I₀ ha hg = x := by
  obtain ⟨n, s, hsmem, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrading I₀) (reesX_mem I₀ a ha) x
  have hs' : s ∈ reesGrading I₀ n := by simpa using hsmem
  obtain ⟨g, hg, hrepr⟩ := (mem_reesGrading_iff_exists I₀).mp hs'
  subst hrepr
  exact ⟨n, g, hg, rfl⟩

/-- Congruence for polynomial monomials with different indices. -/
private lemma monomial_congr {i j : ℕ} {c d : A} (hij : i = j) (hcd : c = d) :
    (Polynomial.monomial i) c = (Polynomial.monomial j) d := by
  subst hij; subst hcd; rfl

/-- Clearing a power of `a` from the numerator of a chart fraction on the `b`-chart:
`(aᵏ·x)/bᵏ⁺ⁿ = (a/b)ᵏ · (x/bⁿ)`, where `a/b` is the localization element of the chart
comparison. -/
lemma AffineBlowup.chartFrac_pow_mul {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ hb hax =
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ k *
        AffineBlowup.chartFrac I₀ hb hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul, pow_one]
  exact monomial_congr (by ring) (by ring)

/-- Cancelling a power of `a` on its own chart: `(aᵏ·x)/aᵏ⁺ⁿ = x/aⁿ`. -/
lemma AffineBlowup.chartFrac_self_pow_mul {a : A} (ha : a ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ ha hax = AffineBlowup.chartFrac I₀ ha hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul]
  exact monomial_congr (by ring) (by ring)

/-- **The denominator-clearing lemma on two charts of the same Rees algebra**
(the algebraic core of Stacks Tag 0803), ring-level form: let `Ja`, `Jb` be ideals of
the `a`- and `b`-charts which agree in the common localization `B_{b·a}`. If the chart
fraction `g/aᵉ` lies in `Ja`, then multiplying `g/bᵉ` by any large enough power of the
localization element `a/b` lands in `Jb`. -/
lemma AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem
    {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    (Ja : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)))
    (Jb : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb)))
    (hab : Ja.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      Jb.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e) (hμ : AffineBlowup.chartFrac I₀ ha hg ∈ Ja) :
    ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ N' *
        AffineBlowup.chartFrac I₀ hb hg ∈ Jb := by
  set ρb := HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
    (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha) with hρb
  set t := HomogeneousLocalization.Away.isLocalizationElem
    (reesX_mem I₀ b hb) (reesX_mem I₀ a ha) with ht
  -- the image of `g/bᵉ` lies in the extension of `Jb` to the overlap
  have hmem : ρb (AffineBlowup.chartFrac I₀ hb hg) ∈ Jb.map ρb := by
    rw [hρb, AffineBlowup.awayMap_chartFrac I₀ hb ha hg, ← hab]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hμ)
  -- the overlap ring is the localization of the `b`-chart at `a/b`
  let : Algebra
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) := ρb.toAlgebra
  have hloc : IsLocalization.Away t (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb * reesX I₀ a ha)) :=
    HomogeneousLocalization.Away.isLocalization_mul (reesX_mem I₀ b hb)
      (reesX_mem I₀ a ha) rfl one_ne_zero
  have halg : algebraMap
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) = ρb :=
    RingHom.algebraMap_toAlgebra ρb
  obtain ⟨N, hN⟩ := Ideal.exists_pow_mul_mem_of_algebraMap_mem_map t
    (K := Jb) (x := AffineBlowup.chartFrac I₀ hb hg) (by rw [halg]; exact hmem)
  refine ⟨N, fun N' hN' ↦ ?_⟩
  rw [← pow_sub_mul_pow t hN', mul_assoc]
  exact Ideal.mul_mem_left _ _ hN

end LocalAlgebra

section Combinators

/-- **Uniform threshold over a doubly-indexed finite family**: pointwise eventual
properties over a finite set and dependent finite sets admit a single threshold. The
index types are abstract, so all `Finset.sup` bookkeeping happens over variables and
never touches the large chart-ring types. -/
private lemma exists_uniform_ge₂ {α : Type u} (T : Finset α)
    {γ : ∀ a, a ∈ T → Type u}
    (Gf : ∀ (a : α) (ha : a ∈ T), Finset (γ a ha))
    {P : ∀ (a : α) (ha : a ∈ T) (c : γ a ha), c ∈ Gf a ha → ℕ → Prop}
    (h : ∀ a ha c hc, ∃ d₀ : ℕ, ∀ d ≥ d₀, P a ha c hc d) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ a ha c hc, P a ha c hc d := by
  classical
  choose f hf using h
  refine ⟨T.attach.sup fun a ↦ (Gf a.1 a.2).attach.sup fun c ↦ f a.1 a.2 c.1 c.2,
    fun d hd a ha c hc ↦ hf a ha c hc d (le_trans (le_trans
      (Finset.le_sup (f := fun c' ↦ f a ha c'.1 c'.2) (Finset.mem_attach _ ⟨c, hc⟩))
      (Finset.le_sup (f := fun a' : { x // x ∈ T } ↦
        (Gf a'.1 a'.2).attach.sup fun c' ↦ f a'.1 a'.2 c'.1 c'.2)
        (Finset.mem_attach _ ⟨a, ha⟩))) hd)⟩

/-- **Collection of a doubly-indexed family into a finite set**, with both the
enumeration and the membership property. The index types are abstract, so the
`Finset.biUnion`/`attach` bookkeeping happens over variables. -/
private lemma exists_finset_forall_mem {α β : Type u} (T : Finset α)
    {γ : ∀ a, a ∈ T → Type u}
    (Gf : ∀ (a : α) (ha : a ∈ T), Finset (γ a ha))
    (mf : ∀ (a : α) (ha : a ∈ T) (c : γ a ha), c ∈ Gf a ha → β) :
    ∃ M : Finset β,
      (∀ x ∈ M, ∃ (a : α) (ha : a ∈ T) (c : γ a ha) (hc : c ∈ Gf a ha),
        x = mf a ha c hc) ∧
      ∀ (a : α) (ha : a ∈ T) (c : γ a ha) (hc : c ∈ Gf a ha), mf a ha c hc ∈ M := by
  classical
  refine ⟨T.attach.biUnion fun a ↦ (Gf a.1 a.2).attach.image fun c ↦ mf a.1 a.2 c.1 c.2,
    ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨a, -, hx⟩ := hx
    rw [Finset.mem_image] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact ⟨a.1, a.2, c.1, c.2, rfl⟩
  · intro a ha c hc
    rw [Finset.mem_biUnion]
    exact ⟨⟨a, ha⟩, Finset.mem_attach _ _, Finset.mem_image.mpr
      ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩⟩

/-- Transport of an ideal membership along an equality of `CommRingCat` morphisms.
Applying this generic lemma is cheap where a `▸`-rewrite on the chart section rings
would have to abstract over the large chart types. -/
private lemma mem_of_ringHom_eq {R S : CommRingCat.{u}} {f g : R ⟶ S} (h : f = g)
    {x : R} {P : Ideal S} (hx : g.hom x ∈ P) : f.hom x ∈ P := by
  rw [h]
  exact hx

end Combinators

end AlgebraicGeometry
