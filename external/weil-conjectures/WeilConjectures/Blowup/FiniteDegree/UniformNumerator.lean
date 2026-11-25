/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Algebra
import all WeilConjectures.Blowup.FiniteDegree.LocalAlgebra

/-!
# Uniform numerators for the finite-degree approximation on the blow-up

Each chart-ideal generator of an ideal sheaf on the blow-up is cleared into a numerator whose
fractions lie in the chart ideals of every chart (`AffineBlowup.exists_uniform_numerator`).
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section UniformNumerator

open HomogeneousLocalization

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- **The uniform numerator construction** (Steps 2–3 of the blueprint proof of Stacks
Tag 0803, ring-level form): given a finite generating set `s` of `I₀`, a family of
chart ideals `Jc` agreeing on overlaps, and a chart fraction `g/aᵉ` lying in the chart
ideal of the `a`-chart, there is a threshold `d₀` such that for every `d ≥ d₀` there is
a numerator `m ∈ I₀ᵈ` with `m/aᵈ = g/aᵉ` on the `a`-chart whose fraction `m/bᵈ` lies in
the chart ideal of every `b`-chart, `b ∈ s`. -/
lemma AffineBlowup.exists_uniform_numerator
    (s : Finset A) (hs : Ideal.span (s : Set A) = I₀)
    (Jc : ∀ (b : A) (hb : b ∈ I₀), Ideal (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hJc : ∀ (a b : A) (ha : a ∈ I₀) (hb : b ∈ I₀),
      (Jc a ha).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      (Jc b hb).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {a : A} (has : a ∈ s) {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e)
    (hμ : AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg ∈
      Jc a (hs ▸ Ideal.subset_span has)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : A) (hm : m ∈ I₀ ^ d),
      AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) m =
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg *
          AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) a ^ d ∧
      ∀ (b : A) (hbs : b ∈ s), AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hm ∈
        Jc b (hs ▸ Ideal.subset_span hbs) := by
  classical
  have ha' : a ∈ I₀ := hs ▸ Ideal.subset_span has
  -- clearing exponents for each chart in the generating set
  have hclear : ∀ (b : A) (hbs : b ∈ s), ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem
          (reesX_mem I₀ b (hs ▸ Ideal.subset_span hbs)) (reesX_mem I₀ a ha') ^ N' *
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hg ∈
      Jc b (hs ▸ Ideal.subset_span hbs) := fun b hbs ↦
    AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem I₀ ha'
      (hs ▸ Ideal.subset_span hbs) (Jc a ha') (Jc b (hs ▸ Ideal.subset_span hbs))
      (hJc a b ha' (hs ▸ Ideal.subset_span hbs)) hg hμ
  choose N hN using hclear
  refine ⟨(s.attach.sup fun b ↦ N b.1 b.2) + e, fun d hd ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + e := ⟨d - e, by omega⟩
  have hkN : ∀ (b : A) (hbs : b ∈ s), N b hbs ≤ k := by
    intro b hbs
    have h1 : N b hbs ≤ s.attach.sup fun b ↦ N b.1 b.2 :=
      Finset.le_sup (f := fun b : { x // x ∈ s } ↦ N b.1 b.2)
        (Finset.mem_attach _ ⟨b, hbs⟩)
    omega
  have hm : a ^ k * g ∈ I₀ ^ (k + e) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ha' k) hg
  refine ⟨a ^ k * g, hm, ?_, ?_⟩
  · rw [← AffineBlowup.chartFrac_mul_awayAlgebraMap_pow I₀ ha' hm,
      AffineBlowup.chartFrac_self_pow_mul I₀ ha' hg hm]
  · intro b hbs
    rw [AffineBlowup.chartFrac_pow_mul I₀ ha' (hs ▸ Ideal.subset_span hbs) hg hm]
    exact hN b hbs k (hkN b hbs)

/-- **The uniform numerator finset** (Steps 2–4 of the blueprint proof of Stacks
Tag 0803, ring-level form): given a finite generating set `s` of `I₀` and a compatible
family of chart ideals `Jc` with finite generating sets `G`, there is a threshold `d₀`
such that for every `d ≥ d₀` there is a finite set `M ⊆ I₀ᵈ` of numerators whose chart
fractions `m/bᵈ` lie in every chart ideal, and which clear every generator of every
chart ideal: `μ · (b/1)ᵈ = m/1` on the `b`-chart. All indexing over the generating
sets happens here, over an abstract ring, keeping the `Finset` bookkeeping away from
the section rings of schemes. -/
lemma AffineBlowup.exists_uniform_numerator_finset
    (s : Finset A) (hs : Ideal.span (s : Set A) = I₀)
    (Jc : ∀ (b : A) (hb : b ∈ I₀), Ideal (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hJc : ∀ (a b : A) (ha : a ∈ I₀) (hb : b ∈ I₀),
      (Jc a ha).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      (Jc b hb).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    (G : ∀ (b : A) (hb : b ∈ I₀), Finset (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hG : ∀ (b : A) (hb : b ∈ I₀), Ideal.span (G b hb : Set _) = Jc b hb) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ M : Finset A,
      (∀ m ∈ M, ∃ hm : m ∈ I₀ ^ d, ∀ (b : A) (hbs : b ∈ s),
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hm ∈
          Jc b (hs ▸ Ideal.subset_span hbs)) ∧
      ∀ (b : A) (hbs : b ∈ s), ∀ μ ∈ G b (hs ▸ Ideal.subset_span hbs),
        ∃ m ∈ M,
          μ * AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) b
              ^ d =
            AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) m := by
  classical
  -- numerator thresholds for every chart generator
  have hnum : ∀ (b : A) (hbs : b ∈ s)
      (μ : HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b (hs ▸ Ideal.subset_span hbs)))
      (_ : μ ∈ G b (hs ▸ Ideal.subset_span hbs)),
      ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : A) (hm : m ∈ I₀ ^ d),
        AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) m =
          μ * AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) b
            ^ d ∧
        ∀ (b' : A) (hbs' : b' ∈ s),
          AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs') hm ∈
            Jc b' (hs ▸ Ideal.subset_span hbs') := by
    intro b hbs μ hμG
    obtain ⟨e, g, hg, rfl⟩ := AffineBlowup.chartFrac_surjective I₀
      (hs ▸ Ideal.subset_span hbs) μ
    exact AffineBlowup.exists_uniform_numerator I₀ s hs Jc hJc hbs hg
      ((hG b (hs ▸ Ideal.subset_span hbs)) ▸ Ideal.subset_span hμG)
  -- one uniform threshold, by the abstract double-sup combinator
  obtain ⟨d₀, hd₀⟩ := exists_uniform_ge₂ s
    (fun b hbs ↦ G b (hs ▸ Ideal.subset_span hbs)) hnum
  refine ⟨d₀, fun d hd ↦ ?_⟩
  -- the numerators at degree `d`, collected into a finite set
  choose mf hmI hrest using hd₀ d hd
  obtain ⟨M, hM₁, hM₂⟩ := exists_finset_forall_mem s
    (fun b hbs ↦ G b (hs ▸ Ideal.subset_span hbs)) mf
  refine ⟨M, ?_, ?_⟩
  · intro m hmM
    obtain ⟨b, hbs, μ, hμG, rfl⟩ := hM₁ m hmM
    exact ⟨hmI b hbs μ hμG, (hrest b hbs μ hμG).2⟩
  · intro b hbs μ hμG
    exact ⟨mf b hbs μ hμG, hM₂ b hbs μ hμG, (hrest b hbs μ hμG).1.symm⟩

end UniformNumerator

end AlgebraicGeometry
