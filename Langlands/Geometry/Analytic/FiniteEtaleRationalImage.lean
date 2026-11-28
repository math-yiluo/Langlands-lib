import Langlands.Geometry.Analytic.FiniteEtaleWeightedCoefficients
import Langlands.Geometry.Analytic.RecognizedDomainSaturationSite
import Langlands.Geometry.Analytic.SmallAffinoidSpectrum

/-! # Images of rational domains under finite étale affinoid maps -/

noncomputable section

universe u v

namespace Langlands.Analytic

open MvPolynomial PresentedAffinoidAlgebra Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem exists_rationalChart_coeff_locus {σ : Type*}
    (P : MvPolynomial σ A) (hP : Ideal.span (range P.coeff) = ⊤)
    (w : σ → ℝ) (hw : ∀ j, 0 < w j) (d : σ →₀ ℕ) :
    ∃ C : RationalChart K A, ∀ x : BanachSpectrum A, x ∈ C.locus ↔
      ∀ k, x (P.coeff k) * monomialWeight w k ≤ x (P.coeff d) * monomialWeight w d := by
  classical
  let e := (Fintype.equivFin P.support).symm
  choose q hq using fun k : σ →₀ ℕ => presentationMap_surjective K A (P.coeff k)
  have hspan : Ideal.span (range fun i => P.coeff (e i).val) = ⊤ := by
    apply top_unique
    rw [← hP]
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    by_cases hk : k ∈ P.support
    · obtain ⟨i, hi⟩ := e.surjective ⟨k, hk⟩
      apply Ideal.subset_span
      exact ⟨i, congrArg (fun j : P.support => P.coeff j.val) hi⟩
    · rw [notMem_support_iff.mp hk]
      exact Ideal.zero_mem _
  let C : RationalChart K A :=
    { arity := Fintype.card P.support
      radii := ⟨fun i => monomialWeight w d / monomialWeight w (e i).val,
        fun i => div_pos (monomialWeight_pos hw d) (monomialWeight_pos hw (e i).val)⟩
      denominator := q d
      numerators := fun i => q (e i).val
      generates := by
        change Ideal.span (insert (presentationMap K A (q d))
          (range fun i => presentationMap K A (q (e i).val))) = ⊤
        simp only [hq]
        apply top_unique
        rw [← hspan]
        exact Ideal.span_mono (subset_insert _ _) }
  refine ⟨C, fun x => ?_⟩
  change (∀ i, x (presentationMap K A (q (e i).val)) ≤
    (monomialWeight w d / monomialWeight w (e i).val) * x (presentationMap K A (q d))) ↔ _
  simp only [hq]
  have hbound (k : σ →₀ ℕ) :
      x (P.coeff k) ≤ (monomialWeight w d / monomialWeight w k) * x (P.coeff d) ↔
        x (P.coeff k) * monomialWeight w k ≤ x (P.coeff d) * monomialWeight w d := by
    rw [div_mul_eq_mul_div₀, le_div_iff₀ (monomialWeight_pos hw k), mul_comm (monomialWeight w d)]
  simp_rw [hbound]
  refine ⟨fun h k => ?_, fun h i => h (e i).val⟩
  by_cases hk : k ∈ P.support
  · obtain ⟨i, hi⟩ := e.surjective ⟨k, hk⟩
    have hki : (e i).val = k := congrArg Subtype.val hi
    simpa only [hki] using h i
  · rw [notMem_support_iff.mp hk, map_zero, zero_mul]
    exact mul_nonneg (apply_nonneg x.toMulRingSeminorm _) (monomialWeight_pos hw d).le

omit [CompleteSpace K] in
private theorem mem_support_of_maximalWeightedCoeff {σ : Type*}
    (P : MvPolynomial σ A) (hP : Ideal.span (range P.coeff) = ⊤)
    {w : σ → ℝ} (hw : ∀ j, 0 < w j) (x : BanachSpectrum A) (d : σ →₀ ℕ)
    (hd : ∀ k, x (P.coeff k) * monomialWeight w k ≤ x (P.coeff d) * monomialWeight w d) :
    d ∈ P.support := by
  by_contra hs
  have hle : Ideal.span (range P.coeff) ≤ x.kernel := by
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hk := hd k
    rw [notMem_support_iff.mp hs, map_zero, zero_mul] at hk
    exact le_antisymm (nonpos_of_mul_nonpos_left hk (monomialWeight_pos hw k))
      (apply_nonneg x.toMulRingSeminorm _)
  have h1 : (1 : A) ∈ x.kernel := hle (by rw [hP]; exact Submodule.mem_top)
  change x (1 : A) = 0 at h1
  rw [map_one] at h1
  exact one_ne_zero h1

/-- A rational domain has image a finite union of rational domains under a finite
Banach map that is algebraically finite étale. -/
theorem exists_rationalChart_cover_image (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale) (D : RationalChart K B) :
    ∃ (m : ℕ) (C : Fin m → RationalChart K A),
      (⋃ i, (C i).locus) = BanachSpectrum.comap f.toBoundedRingHom '' D.locus := by
  classical
  let b : Fin (D.arity + 1) → B := Fin.cons (α := fun _ => B)
    (presentationMap K B D.denominator)
    (fun i => presentationMap K B (D.numerators i))
  have hb : Ideal.span (range b) = ⊤ := by
    have hgen : Ideal.span (insert (presentationMap K B D.denominator)
        (range fun i => presentationMap K B (D.numerators i))) = ⊤ := D.generates
    simpa only [b, Fin.range_cons] using hgen
  let w : Fin (D.arity + 1) → ℝ := Fin.cons 1 (fun i => (D.radii i)⁻¹)
  have hw (i) : 0 < w i := Fin.cases one_pos (fun j => inv_pos.mpr (D.radii.positive j)) i
  have hD (y : BanachSpectrum B) : y ∈ D.locus ↔
      ∀ j, y (b j) * w j ≤ y (b 0) * w 0 := by
    have hsucc (j : Fin D.arity) :
        y (b j.succ) * w j.succ ≤ y (b 0) * w 0 ↔
          y (presentationMap K B (D.numerators j)) ≤
            D.radii j * y (presentationMap K B D.denominator) := by
      change y (presentationMap K B (D.numerators j)) * (D.radii j)⁻¹ ≤
        y (presentationMap K B D.denominator) * 1 ↔ _
      rw [mul_one, ← div_eq_mul_inv, div_le_iff₀ (D.radii.positive j), mul_comm (D.radii j)]
    exact ⟨fun h j => Fin.cases le_rfl (fun i => (hsucc i).2 (h i)) j,
      fun h i => (hsucc i).1 (h i.succ)⟩
  obtain ⟨P, hP, hcoeff⟩ := BanachSpectrum.exists_weightedCoeff_iff f hf he b hb w hw
  choose C hC using fun d => exists_rationalChart_coeff_locus P hP w hw d
  let I := P.support.filter fun d => 0 < d 0
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => C (e i).val, ?_⟩
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨i, hi⟩
    have hd := (Finset.mem_filter.mp (e i).property).2
    obtain ⟨y, hxy, hy⟩ := (hcoeff x).2 ⟨(e i).val, hd, (hC _ x).1 hi⟩
    exact ⟨y, (hD y).2 hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨d, hd0, hd⟩ := (hcoeff x).1 ⟨y, hxy, (hD y).1 hy⟩
    have hs := mem_support_of_maximalWeightedCoeff P hP hw x d hd
    obtain ⟨i, hi⟩ := e.surjective ⟨d, Finset.mem_filter.mpr ⟨hs, hd0⟩⟩
    refine ⟨i, (hC _ x).2 ?_⟩
    rw [show (e i).val = d from congrArg Subtype.val hi]
    exact hd

/-- In the saturated atlas of the base, the image of a rational domain under a
finite Banach, algebraically finite étale map is an analytic domain. -/
theorem isOriginalChartDomain_image_rational [Small.{v} (BanachSpectrum A)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (D : RationalChart K B) :
    (SmallAffinoidSpectrum.saturated.{u, v} A).presentation.atlas.IsOriginalChartDomain
      (SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A ''
        (BanachSpectrum.comap f.toBoundedRingHom '' D.locus)) := by
  obtain ⟨m, C, hC⟩ := exists_rationalChart_cover_image f hf he D
  let S := SmallAffinoidSpectrum.saturated.{u, v} A
  let a := (SmallAffinoidSpectrum.presentation.{u, v} A).atlas
  let U (i : Fin m) : IndexedAffinoidAtlas.LocalDomain a := ⟨PUnit.unit, (C i).toDomain⟩
  let c (i : Fin m) : S.presentation.atlas.Index := ⟨(U i).locus, ⟨U i, rfl⟩⟩
  let e : BanachSpectrum A ≃ₜ S.presentation.space :=
    SmallAffinoidSpectrum.spectrumHomeomorph.{u, v} A
  have hrange (i : Fin m) : range (S.presentation.atlas.chart (c i)) = e '' (C i).locus :=
    a.range_saturatedChart (c i)
  have : T2Space S.presentation.space := e.symm.isEmbedding.t2Space
  apply S.presentation.atlas.isOriginalChartDomain_of_finite_chart_cover _ c
  simp_rw [hrange]
  change (⋃ i, e '' (C i).locus) = e '' (BanachSpectrum.comap f.toBoundedRingHom '' D.locus)
  exact (image_iUnion (f := e) (s := fun i => (C i).locus)).symm.trans
    (congrArg (image e) hC)

end Langlands.Analytic
