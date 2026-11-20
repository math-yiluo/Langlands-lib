import Langlands.Geometry.Analytic.AffinoidPushoutSpectralTests
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof

/-! # Spectral convergence of factorizations through affinoid domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum Filter

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K} {T : Type v}
  {l : Filter T} {φ : T → BoundedAlgHom K A B} {ψ : BoundedAlgHom K A B}

/-- A spectrum point is bounded by the source norm after pullback along a
bounded map. -/
theorem spectrum_apply_map_le (f : BoundedAlgHom K A B) (x : BanachSpectrum B) (a : A) :
    x (f a) ≤ ‖a‖ :=
  (BanachSpectrum.comap f.toBoundedRingHom x).le_norm a

/-- The nonarchimedean inequality for differences at a spectrum point. -/
theorem spectrum_sub_le_max (x : BanachSpectrum B) (a b : B) :
    x (a - b) ≤ max (x a) (x b) := by
  have h := x.isNonarchimedean (K := K) a (-b)
  rw [← sub_eq_add_neg] at h
  simpa only [map_neg_eq_map] using h

/-- Postcomposition with a bounded map preserves spectral convergence. -/
theorem SpectralConvergesOn.postcomp {C : PresentedAffinoidAlgebra K} {a : A}
    (h : SpectralConvergesOn l φ ψ a) (β : BoundedAlgHom K B C) :
    SpectralConvergesOn l (fun t => β.comp (φ t)) (β.comp ψ) a := by
  intro ε hε
  filter_upwards [h ε hε] with t ht
  intro x
  have hx := ht (BanachSpectrum.comap β.toBoundedRingHom x)
  change x (β (φ t a) - β (ψ a)) ≤ ε
  rw [← map_sub]
  exact hx

namespace RationalChart

/-- Pointwise stability of a weighted rational locus: a spectrum point at which
two bounded maps have small displacement on the rational data is sent into the
locus by the first map when it is sent there by the second. -/
theorem comap_mem_locus_of_spectral_close (d : RationalChart K A) {ε : ℝ}
    (hε : ∀ y ∈ d.locus, ε ≤ y d.denominatorClass)
    (f g : BoundedAlgHom K A B) (x : BanachSpectrum B)
    (hb : x (f d.denominatorClass - g d.denominatorClass) < ε)
    (hn : ∀ j, x (f (d.numeratorClass j) - g (d.numeratorClass j)) ≤ d.radii j * ε)
    (hx : BanachSpectrum.comap g.toBoundedRingHom x ∈ d.locus) :
    BanachSpectrum.comap f.toBoundedRingHom x ∈ d.locus := by
  have hden : ε ≤ x (g d.denominatorClass) := hε _ hx
  have hsmall : x.toMulRingSeminorm (f d.denominatorClass - g d.denominatorClass) <
      x.toMulRingSeminorm (g d.denominatorClass) :=
    hb.trans_le hden
  have heq : x (f d.denominatorClass) = x (g d.denominatorClass) := by
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K)).add_eq_right_of_lt
        (map_neg_eq_map x.toMulRingSeminorm) hsmall
  intro j
  change x (f (d.numeratorClass j)) ≤ d.radii j * x (f d.denominatorClass)
  rw [heq]
  have hxj : x (g (d.numeratorClass j)) ≤ d.radii j * x (g d.denominatorClass) := hx j
  have hnum := x.isNonarchimedean (K := K)
    (f (d.numeratorClass j) - g (d.numeratorClass j)) (g (d.numeratorClass j))
  rw [sub_add_cancel] at hnum
  exact hnum.trans (max_le ((hn j).trans
    (mul_le_mul_of_nonneg_left hden (d.radii.positive j).le)) hxj)

/-- The pointwise stability is symmetric in the two maps. -/
theorem comap_mem_locus_iff_of_spectral_close (d : RationalChart K A) {ε : ℝ}
    (hε : ∀ y ∈ d.locus, ε ≤ y d.denominatorClass)
    (f g : BoundedAlgHom K A B) (x : BanachSpectrum B)
    (hb : x (f d.denominatorClass - g d.denominatorClass) < ε)
    (hn : ∀ j, x (f (d.numeratorClass j) - g (d.numeratorClass j)) ≤ d.radii j * ε) :
    BanachSpectrum.comap f.toBoundedRingHom x ∈ d.locus ↔
      BanachSpectrum.comap g.toBoundedRingHom x ∈ d.locus := by
  refine ⟨comap_mem_locus_of_spectral_close d hε g f x ?_ ?_,
    comap_mem_locus_of_spectral_close d hε f g x hb hn⟩
  · rw [← neg_sub, map_neg_eq_map]
    exact hb
  · intro j
    rw [← neg_sub, map_neg_eq_map]
    exact hn j

/-- Spectral convergence on the base keeps the inverse image of a weighted
rational locus eventually unchanged, uniformly on the target spectrum. -/
theorem eventually_comap_mem_locus_iff (d : RationalChart K A)
    (h : ∀ a, SpectralConvergesOn l φ ψ a) :
    ∀ᶠ t in l, ∀ x : BanachSpectrum B,
      (BanachSpectrum.comap (φ t).toBoundedRingHom x ∈ d.locus ↔
        BanachSpectrum.comap ψ.toBoundedRingHom x ∈ d.locus) := by
  obtain ⟨ε, hε, hbound⟩ := d.exists_pos_le_denominator
  filter_upwards [h d.denominatorClass (ε / 2) (half_pos hε),
    Filter.eventually_all.mpr (fun j => h (d.numeratorClass j) (d.radii j * ε)
      (mul_pos (d.radii.positive j) hε))] with t hb hn x
  exact comap_mem_locus_iff_of_spectral_close d hbound (φ t) ψ x
    ((hb x).trans_lt (half_lt_self hε)) (fun j => hn j x)

/-- Spectral convergence passes to factorizations through a weighted rational
domain containing the image of the limit map. -/
theorem spectralConvergesOn_of_factor (d : RationalChart K A)
    (h : ∀ a, SpectralConvergesOn l φ ψ a)
    (hψ : HasImageIn K ψ d.locus)
    {φd : T → BoundedAlgHom K d.algebra B}
    (hφd : ∀ᶠ t in l, (φd t).comp d.baseMap = φ t)
    {ψd : BoundedAlgHom K d.algebra B} (hψd : ψd.comp d.baseMap = ψ)
    (c : d.algebra) : SpectralConvergesOn l φd ψd c := by
  have hbase : ∀ a : A, SpectralConvergesOn l φd ψd (d.baseMap a) := by
    intro a ε hε
    filter_upwards [h a ε hε, hφd] with t ht hφt
    have e1 : φd t (d.baseMap a) = φ t a := by rw [← hφt]; rfl
    have e2 : ψd (d.baseMap a) = ψ a := by rw [← hψd]; rfl
    rw [e1, e2]
    exact ht
  apply spectralConvergesOn_of_coordinates _ c
  intro i
  change Fin (A.arity + d.arity) at i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have heq : d.baseMap (coordinate K A i) =
        coordinate K d.algebra (Fin.castAdd d.arity i) :=
      RationalPresentation.baseMap_coordinate K A d.radii d.denominator d.numerators i
    rw [← heq]
    exact hbase _
  · change SpectralConvergesOn l φd ψd (d.fractionCoordinate j)
    obtain ⟨ε₀, hε₀, hbound⟩ := d.exists_pos_le_denominator
    intro ε hε
    set b := d.denominatorClass
    set f := d.numeratorClass j
    let M : ℝ := ‖b‖ + ‖f‖ + 1
    have hM : 0 < M := by positivity
    let δ : ℝ := min (ε₀ / 2) (ε * ε₀ ^ 2 / M)
    have hδ : 0 < δ := lt_min (half_pos hε₀) (by positivity)
    have hδε₀ : δ < ε₀ := (min_le_left _ _).trans_lt (half_lt_self hε₀)
    have hδM : δ * M ≤ ε * ε₀ ^ 2 := by
      calc δ * M ≤ (ε * ε₀ ^ 2 / M) * M :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = ε * ε₀ ^ 2 := div_mul_cancel₀ _ hM.ne'
    filter_upwards [hbase b δ hδ, hbase f δ hδ, hφd] with t htb htf hφt
    intro x
    have hu : IsUnit (φd t (d.baseMap b)) := d.isUnit_map_denominator (φd t)
    have hu₀ : IsUnit (ψd (d.baseMap b)) := d.isUnit_map_denominator ψd
    rw [d.map_fractionCoordinate_eq_inverse_mul (φd t),
      d.map_fractionCoordinate_eq_inverse_mul ψd]
    set u := φd t (d.baseMap b)
    set u₀ := ψd (d.baseMap b)
    set w := φd t (d.baseMap f)
    set w₀ := ψd (d.baseMap f)
    -- lower bounds for the two denominators at `x`
    have hψx : ε₀ ≤ x u₀ := by
      have e2 : u₀ = ψ b := by
        change ψd (d.baseMap b) = ψ b
        rw [← hψd]; rfl
      rw [e2]
      exact hbound _ (hψ x)
    have hdiff : x (u - u₀) ≤ δ := htb x
    have hux : x u = x u₀ := by
      have hsmall : x.toMulRingSeminorm (u - u₀) < x.toMulRingSeminorm u₀ :=
        hdiff.trans_lt (hδε₀.trans_le hψx)
      simpa only [sub_add_cancel] using
        (x.isNonarchimedean (K := K)).add_eq_right_of_lt
          (map_neg_eq_map x.toMulRingSeminorm) hsmall
    have hu_pos : 0 < x u₀ := hε₀.trans_le hψx
    -- inverses of units at a spectrum point
    have hinv : ∀ v : B, IsUnit v → 0 < x v → x (Ring.inverse v) = (x v)⁻¹ := by
      intro v hv hxv
      have h1 : x (Ring.inverse v) * x v = 1 := by
        rw [← map_mul, Ring.inverse_mul_cancel v hv, map_one]
      field_simp
      linarith [h1]
    have hu_inv : x (Ring.inverse u) = (x u₀)⁻¹ := by
      rw [hinv u hu (hux ▸ hu_pos), hux]
    have hu₀_inv : x (Ring.inverse u₀) = (x u₀)⁻¹ := hinv u₀ hu₀ hu_pos
    -- algebraic identity
    have hid : Ring.inverse u * w - Ring.inverse u₀ * w₀ =
        Ring.inverse u * Ring.inverse u₀ * (u₀ * (w - w₀) - (u - u₀) * w₀) := by
      have h1 : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel u hu
      have h2 : Ring.inverse u₀ * u₀ = 1 := Ring.inverse_mul_cancel u₀ hu₀
      linear_combination (-(Ring.inverse u * w) * h2 + Ring.inverse u₀ * w₀ * h1)
    have hwdiff : x (w - w₀) ≤ δ := htf x
    have hu₀le : x u₀ ≤ ‖b‖ := by
      have e2 : u₀ = ψ b := by
        change ψd (d.baseMap b) = ψ b
        rw [← hψd]; rfl
      rw [e2]
      exact spectrum_apply_map_le ψ x b
    have hw₀le : x w₀ ≤ ‖f‖ := by
      have e2 : w₀ = ψ f := by
        change ψd (d.baseMap f) = ψ f
        rw [← hψd]; rfl
      rw [e2]
      exact spectrum_apply_map_le ψ x f
    have hnum : x (u₀ * (w - w₀) - (u - u₀) * w₀) ≤ δ * M := by
      refine (spectrum_sub_le_max (K := K) x _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        calc x u₀ * x (w - w₀) ≤ ‖b‖ * δ :=
              mul_le_mul hu₀le hwdiff (apply_nonneg _ _) (norm_nonneg _)
          _ ≤ M * δ := mul_le_mul_of_nonneg_right (by
              dsimp only [M]; linarith [norm_nonneg f]) hδ.le
          _ = δ * M := mul_comm _ _
      · rw [map_mul]
        calc x (u - u₀) * x w₀ ≤ δ * ‖f‖ :=
              mul_le_mul hdiff hw₀le (apply_nonneg _ _) hδ.le
          _ ≤ δ * M := mul_le_mul_of_nonneg_left (by
              dsimp only [M]; linarith [norm_nonneg b]) hδ.le
    rw [hid, map_mul, map_mul, hu_inv, hu₀_inv]
    have hε₀u : ε₀ ^ 2 ≤ x u₀ * x u₀ := by
      rw [sq]; exact mul_le_mul hψx hψx hε₀.le hu_pos.le
    calc (x u₀)⁻¹ * (x u₀)⁻¹ * x (u₀ * (w - w₀) - (u - u₀) * w₀)
        ≤ (x u₀)⁻¹ * (x u₀)⁻¹ * (ε * ε₀ ^ 2) :=
          mul_le_mul_of_nonneg_left (hnum.trans hδM) (by positivity)
      _ = ε * (ε₀ ^ 2 / (x u₀ * x u₀)) := by field_simp
      _ ≤ ε * 1 := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          rw [div_le_one (by positivity)]
          exact hε₀u
      _ = ε := mul_one ε

end RationalChart

namespace Domain

variable [CompleteSpace K]

/-- Spectral convergence on the base keeps the inverse image of every full
represented affinoid domain eventually unchanged, uniformly on the target
spectrum. The proof covers the domain by finitely many rational charts. -/
theorem eventually_comap_mem_locus_iff (D : Domain K A)
    (h : ∀ a, SpectralConvergesOn l φ ψ a) :
    ∀ᶠ t in l, ∀ x : BanachSpectrum B,
      (BanachSpectrum.comap (φ t).toBoundedRingHom x ∈ D.locus ↔
        BanachSpectrum.comap ψ.toBoundedRingHom x ∈ D.locus) := by
  obtain ⟨n, d, hd, hcov⟩ := Domain.finiteRationalCover K A D
  have hlocus : ∀ y, y ∈ D.locus ↔ ∃ i, y ∈ (d i).locus := fun y =>
    ⟨fun hy => hcov y hy, fun ⟨i, hi⟩ => (hd i).subset hi⟩
  filter_upwards [Filter.eventually_all.mpr
    (fun i => (d i).eventually_comap_mem_locus_iff h)] with t ht x
  rw [hlocus, hlocus]
  exact exists_congr fun i => ht i x

/-- If the limit map lands in a domain, the maps eventually land there too. -/
theorem eventually_hasImageIn (D : Domain K A)
    (h : ∀ a, SpectralConvergesOn l φ ψ a) (hψ : HasImageIn K ψ D.locus) :
    ∀ᶠ t in l, HasImageIn K (φ t) D.locus := by
  filter_upwards [D.eventually_comap_mem_locus_iff h] with t ht x
  exact (ht x).2 (hψ x)

/-- Spectral convergence passes to factorizations through any full
represented affinoid domain containing the image of the limit map. -/
theorem spectralConvergesOn_of_factor (D : Domain K A)
    (h : ∀ a, SpectralConvergesOn l φ ψ a) (hψ : HasImageIn K ψ D.locus)
    {φD : T → BoundedAlgHom K D.algebra B}
    (hφD : ∀ᶠ t in l, (φD t).comp D.baseMap = φ t)
    {ψD : BoundedAlgHom K D.algebra B} (hψD : ψD.comp D.baseMap = ψ)
    (c : D.algebra) : SpectralConvergesOn l φD ψD c := by
  classical
  obtain ⟨n, d, hd, hcov⟩ := Domain.finiteRationalCover K A D
  -- the rational pieces pulled back along the limit map
  let e : Fin n → RationalChart K B := fun i => RationalChart.pullback ψ (d i)
  let β : (i : Fin n) → BoundedAlgHom K B (e i).algebra := fun i => (e i).baseMap
  let π : (i : Fin n) → BoundedAlgHom K (d i).algebra (e i).algebra :=
    fun i => RationalChart.pullbackMap ψ (d i)
  have hπ : ∀ i, (π i).comp (d i).baseMap = (β i).comp ψ :=
    fun i => RationalChart.pullbackMap_comp_baseMap ψ (d i)
  let r : (i : Fin n) → BoundedAlgHom K D.algebra (d i).algebra :=
    fun i => (hd i).restriction
  have hr : ∀ i, (r i).comp D.baseMap = (d i).baseMap := fun i => (hd i).comp_baseMap
  -- the limit map, restricted to the pulled-back piece, lands in the piece
  have himg : ∀ i, HasImageIn K ((β i).comp ψ) (d i).locus := by
    intro i x'
    have hx' := (e i).represents.hasImageIn x'
    change BanachSpectrum.comap ψ.toBoundedRingHom
      (BanachSpectrum.comap (β i).toBoundedRingHom x') ∈ (d i).locus
    have hloc := RationalChart.pullback_locus ψ (d i)
    change BanachSpectrum.comap (β i).toBoundedRingHom x' ∈ (e i).locus at hx'
    rw [show (e i).locus = _ from hloc] at hx'
    exact hx'
  have hconv : ∀ i (a : A), SpectralConvergesOn l (fun t => (β i).comp (φ t))
      ((β i).comp ψ) a := fun i a => (h a).postcomp (β i)
  -- the moving maps eventually land in each piece
  have hev : ∀ i, ∀ᶠ t in l, HasImageIn K ((β i).comp (φ t)) (d i).locus := by
    intro i
    filter_upwards [(d i).eventually_comap_mem_locus_iff (hconv i)] with t ht x'
    exact (ht x').2 (himg i x')
  -- chosen factorizations through the pieces
  let φi : (i : Fin n) → T → BoundedAlgHom K (d i).algebra (e i).algebra := fun i t =>
    if hi : HasImageIn K ((β i).comp (φ t)) (d i).locus then
      ((d i).represents.2.2 _ _ hi).exists.choose
    else π i
  have hφi : ∀ i, ∀ᶠ t in l, (φi i t).comp (d i).baseMap = (β i).comp (φ t) := by
    intro i
    filter_upwards [hev i] with t ht
    simp only [φi, ht, ↓reduceDIte]
    exact ((d i).represents.2.2 _ _ ht).exists.choose_spec
  -- compatibility with the restriction from `D`
  have hψcompat : ∀ i, (β i).comp ψD = (π i).comp (r i) := by
    intro i
    have hD : HasImageIn K ((β i).comp ψ) D.locus :=
      fun x' => (hd i).subset (himg i x')
    apply (D.represents.2.2 _ _ hD).unique
    · rw [BoundedAlgHom.comp_assoc, hψD]
    · rw [BoundedAlgHom.comp_assoc, hr i, hπ i]
  have hφcompat : ∀ i, ∀ᶠ t in l, (β i).comp (φD t) = (φi i t).comp (r i) := by
    intro i
    filter_upwards [hev i, hφi i, hφD] with t ht hφt hφDt
    have hD : HasImageIn K ((β i).comp (φ t)) D.locus :=
      fun x' => (hd i).subset (ht x')
    apply (D.represents.2.2 _ _ hD).unique
    · rw [BoundedAlgHom.comp_assoc, hφDt]
    · rw [BoundedAlgHom.comp_assoc, hr i, hφt]
  -- convergence on each piece
  have hpiece : ∀ i, SpectralConvergesOn l (φi i) (π i) (r i c) := fun i =>
    (d i).spectralConvergesOn_of_factor (hconv i) (himg i) (hφi i) (hπ i) (r i c)
  intro ε hε
  filter_upwards [Filter.eventually_all.mpr (fun i => hpiece i ε hε),
    Filter.eventually_all.mpr hφcompat] with t ht hct x
  obtain ⟨i, hi⟩ := hcov _ (hψ x)
  have hxe : x ∈ (e i).locus := by
    rw [show (e i).locus = _ from RationalChart.pullback_locus ψ (d i)]
    exact hi
  have hrange := (e i).represents.2.1
  rw [← hrange] at hxe
  obtain ⟨x', rfl⟩ := hxe
  have key := ht i x'
  change BanachSpectrum.comap (β i).toBoundedRingHom x' (φD t c - ψD c) ≤ ε
  change x' (β i (φD t c - ψD c)) ≤ ε
  rw [map_sub]
  have e1 : β i (φD t c) = φi i t (r i c) := by
    change ((β i).comp (φD t)) c = _
    rw [hct i]; rfl
  have e2 : β i (ψD c) = π i (r i c) := by
    change ((β i).comp ψD) c = _
    rw [hψcompat i]; rfl
  rw [e1, e2]
  exact key

end Domain

end Langlands.Analytic.PresentedAffinoidAlgebra
