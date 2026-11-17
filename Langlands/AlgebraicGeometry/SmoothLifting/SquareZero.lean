import Langlands.AlgebraicGeometry.SmoothLifting.Cech

/-! # Lifting along a square-zero thickening, given a finite family of charts

The Čech argument: local lifts `xᵢ` on `C[1/gᵢ]`, corrections `zᵢₖ` extending
`xᵢ + gₖᴺ (xₖ - xᵢ)` from `C[1/(gᵢ gₖ)]` to `C[1/gᵢ]`, and the partition-of-unity combination
`yᵢ = xᵢ + ∑ₖ aₖ gₖᴹ (zᵢₖ - xᵢ)`, which agree on overlaps and glue.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- The chart representative of a lift on a localization `C[1/c]` with `g ∣ c`. -/
abbrev Chart.repL (hI : SqZero I) (ch : Chart f I x₀ s) {c : C} (h : ch.g ∣ c)
    (y : Spec (CommRingCat.of (Loc c)) ⟶ X) (hy : IsLift f I x₀ s (Loc c) y) (b : Γ(X, ch.U)) :
    Loc c :=
  (ch.rep (Loc c) hI (isUnit_loc_of_dvd h) y hy).hom b

theorem Chart.repL_rr (hI : SqZero I) (ch : Chart f I x₀ s) {d c c' : C} (hc : ch.g ∣ c)
    (hd : d ∣ c) (h : c ∣ c') (w : Spec (CommRingCat.of (Loc d)) ⟶ X)
    (hw : IsLift f I x₀ s (Loc d) w) (b : Γ(X, ch.U)) :
    ch.repL hI (hc.trans h) (rr (hd.trans h) w) (hw.rr _) b =
      res c (Loc c') (isUnit_loc_of_dvd h) (ch.repL hI hc (rr hd w) (hw.rr hd) b) := by
  rw [Chart.repL, ch.rep_congr hI _ _ ((hw.rr hd).rr h) (rr_rr hd h (hd.trans h) w).symm b]
  exact ch.rep_rr hI h _ _ (hw.rr hd) b

/-- Transport of a pair relation `zz = y + eᴺ (y' - y)` from `C[1/(c₁ e)]` to `C[1/c']`. -/
theorem Chart.push_pair (hI : SqZero I) (ch : Chart f I x₀ s) {c₁ e c' : C} (hc₁ : ch.g ∣ c₁)
    (h : c₁ * e ∣ c') {y zz : Spec (CommRingCat.of (Loc c₁)) ⟶ X}
    {y' : Spec (CommRingCat.of (Loc e)) ⟶ X} (hy : IsLift f I x₀ s (Loc c₁) y)
    (hzz : IsLift f I x₀ s (Loc c₁) zz) (hy' : IsLift f I x₀ s (Loc e) y') (N : ℕ)
    (hpair : ∀ b, ch.repL hI (hc₁.trans (dvd_mul_right c₁ e)) (rr (dvd_mul_right c₁ e) zz)
        (hzz.rr _) b =
      ch.repL hI (hc₁.trans (dvd_mul_right c₁ e)) (rr (dvd_mul_right c₁ e) y) (hy.rr _) b +
        algebraMap C (Loc (c₁ * e)) e ^ N *
          (ch.repL hI (hc₁.trans (dvd_mul_right c₁ e)) (rr (dvd_mul_left e c₁) y') (hy'.rr _) b -
            ch.repL hI (hc₁.trans (dvd_mul_right c₁ e)) (rr (dvd_mul_right c₁ e) y) (hy.rr _) b))
    (b : Γ(X, ch.U)) :
    ch.repL hI ((hc₁.trans (dvd_mul_right c₁ e)).trans h)
        (rr ((dvd_mul_right c₁ e).trans h) zz) (hzz.rr _) b =
      ch.repL hI ((hc₁.trans (dvd_mul_right c₁ e)).trans h)
          (rr ((dvd_mul_right c₁ e).trans h) y) (hy.rr _) b +
        algebraMap C (Loc c') e ^ N *
          (ch.repL hI ((hc₁.trans (dvd_mul_right c₁ e)).trans h)
              (rr ((dvd_mul_left e c₁).trans h) y') (hy'.rr _) b -
            ch.repL hI ((hc₁.trans (dvd_mul_right c₁ e)).trans h)
              (rr ((dvd_mul_right c₁ e).trans h) y) (hy.rr _) b) := by
  rw [ch.repL_rr hI (hc₁.trans (dvd_mul_right c₁ e)) (dvd_mul_right c₁ e) h zz hzz,
    ch.repL_rr hI (hc₁.trans (dvd_mul_right c₁ e)) (dvd_mul_right c₁ e) h y hy,
    ch.repL_rr hI (hc₁.trans (dvd_mul_right c₁ e)) (dvd_mul_left e c₁) h y' hy', hpair b]
  simp only [map_add, map_mul, map_sub, map_pow, AlgHom.commutes]

/-- **Square-zero lifting from charts.** -/
theorem exists_lift_of_charts [Smooth f] (hI : SqZero I)
    (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s)
    {n : ℕ} (ch : Fin n → Chart f I x₀ s)
    (hspan : Ideal.span (Set.range fun i => (ch i).g) = ⊤) :
    ∃ y : Spec C ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y = x₀ ∧ y ≫ f = s := by
  classical
  -- local lifts on `C[1/gᵢ]`
  choose x hx using fun i => (ch i).exists_lift hI h₀ (Loc (ch i).g) (isUnit_loc (ch i).g)
  -- extensions of `xᵢ + gₖᴺ (xₖ - xᵢ)` from `C[1/(gᵢ gₖ)]` to `C[1/gᵢ]`
  have hLE : ∀ i k, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ (zz : Spec (CommRingCat.of (Loc (ch i).g)) ⟶ X)
      (hzz : IsLift f I x₀ s (Loc (ch i).g) zz), ∀ b,
      (ch i).repL hI (dvd_mul_right _ (ch k).g) (rr (dvd_mul_right _ (ch k).g) zz) (hzz.rr _) b =
        (ch i).repL hI (dvd_mul_right _ (ch k).g) (rr (dvd_mul_right _ (ch k).g) (x i))
          ((hx i).rr _) b +
        algebraMap C (Loc ((ch i).g * (ch k).g)) (ch k).g ^ N *
          ((ch i).repL hI (dvd_mul_right _ (ch k).g) (rr (dvd_mul_left (ch k).g (ch i).g) (x k))
              ((hx k).rr _) b -
            (ch i).repL hI (dvd_mul_right _ (ch k).g) (rr (dvd_mul_right _ (ch k).g) (x i))
              ((hx i).rr _) b) :=
    fun i k => (ch i).exists_extension_loc hI (ch i).g (ch k).g (isUnit_loc _)
      (isUnit_loc_of_dvd (dvd_mul_right _ _)) (hx i) ((hx k).rr (dvd_mul_left (ch k).g (ch i).g))
      (res (ch i).g (Loc ((ch i).g * (ch k).g)) (isUnit_loc_of_dvd (dvd_mul_right _ _)))
  choose N₀ hN₀ using hLE
  let N := Finset.univ.sup fun p : Fin n × Fin n => N₀ p.1 p.2
  have hNle : ∀ i k, N₀ i k ≤ N := fun i k =>
    Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (i, k))
  choose z hz hzeq using fun i k => hN₀ i k N (hNle i k)
  -- the torsion relation on triple overlaps
  have hT : ∀ i j k, ∃ M₀ : ℕ, ∀ b : Γ(X, (ch i).U),
      algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ M₀ *
        (((ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_left (ch j).g (ch i).g) (x j))
              ((hx j).rr _) b +
            (ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_right (ch i).g (ch j).g) (z i k))
              ((hz i k).rr _) b -
            (ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_right (ch i).g (ch j).g) (x i))
              ((hx i).rr _) b) -
          ((ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_left (ch j).g (ch i).g) (z j k))
              ((hz j k).rr _) b +
            algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ N *
              ((ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_left (ch j).g (ch i).g) (x j))
                  ((hx j).rr _) b -
                (ch i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_right (ch i).g (ch j).g) (x i))
                  ((hx i).rr _) b))) = 0 := by
    intro i j k
    have dij : (ch i).g ∣ (ch i).g * (ch j).g := dvd_mul_right _ _
    have dji : (ch j).g ∣ (ch i).g * (ch j).g := dvd_mul_left _ _
    have d3 : (ch i).g * (ch j).g ∣ (ch i).g * (ch j).g * (ch k).g := dvd_mul_right _ _
    have dik3 : (ch i).g * (ch k).g ∣ (ch i).g * (ch j).g * (ch k).g := ⟨(ch j).g, by ring⟩
    have djk3 : (ch j).g * (ch k).g ∣ (ch i).g * (ch j).g * (ch k).g := ⟨(ch i).g, by ring⟩
    have ui : IsUnit (algebraMap C (Loc ((ch i).g * (ch j).g)) (ch i).g) := isUnit_loc_of_dvd dij
    have u3i : IsUnit (algebraMap C (Loc ((ch i).g * (ch j).g * (ch k).g)) (ch i).g) :=
      isUnit_loc_of_dvd (dij.trans d3)
    have u3j : IsUnit (algebraMap C (Loc ((ch i).g * (ch j).g * (ch k).g)) (ch j).g) :=
      isUnit_loc_of_dvd (dji.trans d3)
    have hWP : ∀ t, IsLift f I x₀ s (Loc ((ch i).g * (ch j).g))
        (![rr dji (x j), rr dij (z i k)] t) := by
      intro t; fin_cases t
      exacts [(hx j).rr dji, (hz i k).rr dij]
    have hQW : ∀ t, IsLift f I x₀ s (Loc ((ch i).g * (ch j).g))
        (![rr dji (z j k), rr dji (x j)] t) := by
      intro t; fin_cases t
      exacts [(hz j k).rr dji, (hx j).rr dji]
    have hL := (ch i).comb_isLift _ hI ui (rr dij (x i)) ((hx i).rr dij) _ hWP ![1, 1]
    have hRt := (ch i).comb_isLift _ hI ui (rr dij (x i)) ((hx i).rr dij) _ hQW
      ![1, algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ N]
    -- the pair relations on `C[1/(gᵢ gⱼ gₖ)]`
    have p3 := fun b => (ch i).push_pair hI (dvd_refl _) dik3 (hx i) (hz i k) (hx k) N
      (hzeq i k) b
    have hcombj : rr ((dvd_mul_right _ _).trans djk3) (z j k) =
        (ch j).comb _ hI u3j (rr ((dvd_mul_right _ _).trans djk3) (x j)) ((hx j).rr _)
          (fun _ : Unit => rr ((dvd_mul_left (ch k).g (ch j).g).trans djk3) (x k))
          (fun _ => (hx k).rr _)
          (fun _ => algebraMap C (Loc ((ch i).g * (ch j).g * (ch k).g)) (ch k).g ^ N) := by
      refine (ch j).eq_comb_of_rep hI u3j ((hz j k).rr _) _ _ _ _ _ fun b' => ?_
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
      exact (ch j).push_pair hI (dvd_refl _) djk3 (hx j) (hz j k) (hx k) N (hzeq j k) b'
    have hcombi := hcombj.trans ((ch j).comb_eq _ hI (ch i) u3j u3i _ _ _ _ _)
    have q3 : ∀ b, (ch i).repL hI (dij.trans d3) (rr ((dvd_mul_right _ _).trans djk3) (z j k))
        ((hz j k).rr _) b =
        (ch i).repL hI (dij.trans d3) (rr ((dvd_mul_right _ _).trans djk3) (x j)) ((hx j).rr _) b +
          algebraMap C (Loc ((ch i).g * (ch j).g * (ch k).g)) (ch k).g ^ N *
            ((ch i).repL hI (dij.trans d3) (rr ((dvd_mul_left (ch k).g (ch j).g).trans djk3) (x k))
                ((hx k).rr _) b -
              (ch i).repL hI (dij.trans d3) (rr ((dvd_mul_right _ _).trans djk3) (x j))
                ((hx j).rr _) b) := by
      intro b
      rw [Chart.repL, (ch i).rep_congr hI u3i ((hz j k).rr _)
        ((ch i).comb_isLift _ hI u3i _ _ _ _ _) hcombi b,
        (ch i).rep_comb_apply hI u3i _ _ _ _ _ _ b]
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    have hres : rr d3 ((ch i).comb _ hI ui (rr dij (x i)) ((hx i).rr dij) _ hWP ![1, 1]) =
        rr d3 ((ch i).comb _ hI ui (rr dij (x i)) ((hx i).rr dij) _ hQW
          ![1, algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ N]) := by
      apply (ch i).eq_of_rep hI u3i (hL.rr d3) (hRt.rr d3)
      intro b
      rw [(ch i).rep_rr hI d3 ui u3i hL b, (ch i).rep_rr hI d3 ui u3i hRt b,
        (ch i).rep_comb_apply hI ui _ _ _ _ _ hL b, (ch i).rep_comb_apply hI ui _ _ _ _ _ hRt b]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_mul, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]
      rw [← (ch i).repL_rr hI dij dij d3 (x i) (hx i) b,
        ← (ch i).repL_rr hI dij dji d3 (x j) (hx j) b,
        ← (ch i).repL_rr hI dij dij d3 (z i k) (hz i k) b,
        ← (ch i).repL_rr hI dij dji d3 (z j k) (hz j k) b]
      linear_combination p3 b - q3 b
    obtain ⟨M₀, hM₀⟩ := (ch i).exists_torsion_loc hI _ (ch k).g ui hL hRt _ hres
    refine ⟨M₀, fun b => ?_⟩
    have h := hM₀ b
    rw [(ch i).rep_comb_apply hI ui _ _ _ _ _ hL b,
      (ch i).rep_comb_apply hI ui _ _ _ _ _ hRt b] at h
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul] at h
    linear_combination h
  choose M₀ hM₀ using hT
  let M := Finset.univ.sup fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2
  have hMle : ∀ i j k, M₀ i j k ≤ M := fun i j k =>
    Finset.le_sup (f := fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2)
      (Finset.mem_univ (i, j, k))
  -- partition of unity
  have hspan' : Ideal.span (Set.range fun k => (ch k).g ^ (N + M)) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range fun i => (ch i).g) hspan (N + M)
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun).mp
    (hspan'.symm ▸ Submodule.mem_top : (1 : C) ∈ Ideal.span (Set.range fun k => (ch k).g ^ (N + M)))
  -- the corrected local lifts
  let Y : ∀ i, Spec (CommRingCat.of (Loc (ch i).g)) ⟶ X := fun i =>
    (ch i).comb (Loc (ch i).g) hI (isUnit_loc _) (x i) (hx i) (fun k => z i k) (fun k => hz i k)
      (fun k => algebraMap C (Loc (ch i).g) (a k * (ch k).g ^ M))
  have hY : ∀ i, IsLift f I x₀ s (Loc (ch i).g) (Y i) := fun i =>
    (ch i).comb_isLift _ hI _ _ _ _ _ _
  have hcompat : ∀ i j, rr (dvd_mul_right (ch i).g (ch j).g) (Y i) =
      rr (dvd_mul_left (ch j).g (ch i).g) (Y j) := by
    intro i j
    have dij : (ch i).g ∣ (ch i).g * (ch j).g := dvd_mul_right _ _
    have dji : (ch j).g ∣ (ch i).g * (ch j).g := dvd_mul_left _ _
    have ui : IsUnit (algebraMap C (Loc ((ch i).g * (ch j).g)) (ch i).g) := isUnit_loc_of_dvd dij
    have uj : IsUnit (algebraMap C (Loc ((ch i).g * (ch j).g)) (ch j).g) := isUnit_loc_of_dvd dji
    let A' : Fin n → Loc ((ch i).g * (ch j).g) := fun k =>
      algebraMap C (Loc ((ch i).g * (ch j).g)) (a k * (ch k).g ^ M)
    -- the restriction of `Y j` as a combination in chart `j`, then in chart `i`
    have hYj : rr dji (Y j) = (ch j).comb _ hI uj (rr dji (x j)) ((hx j).rr dji)
        (fun k => rr dji (z j k)) (fun k => (hz j k).rr dji) A' := by
      refine (ch j).eq_comb_of_rep hI uj ((hY j).rr dji) _ _ _ _ _ fun b => ?_
      rw [(ch j).rep_rr hI dji (isUnit_loc _) uj (hY j) b,
        (ch j).rep_comb_apply hI (isUnit_loc _) _ _ _ _ _ (hY j) b, map_add, map_sum]
      congr 1
      · exact ((ch j).rep_rr hI dji (isUnit_loc _) uj (hx j) b).symm
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, map_sub, AlgHom.commutes,
          ← (ch j).rep_rr hI dji (isUnit_loc _) uj (hz j k) b,
          ← (ch j).rep_rr hI dji (isUnit_loc _) uj (hx j) b]
    have hYj' := hYj.trans ((ch j).comb_eq _ hI (ch i) uj ui _ _ _ _ _)
    apply (ch i).eq_of_rep hI ui ((hY i).rr dij) ((hY j).rr dji)
    intro b
    rw [(ch i).rep_congr hI ui ((hY j).rr dji) ((ch i).comb_isLift _ hI ui _ _ _ _ _) hYj' b,
      (ch i).rep_rr hI dij (isUnit_loc _) ui (hY i) b,
      (ch i).rep_comb_apply hI (isUnit_loc _) _ _ _ _ _ (hY i) b,
      (ch i).rep_comb_apply hI ui _ _ _ _ _ _ b, map_add, map_sum]
    have hsum : ∀ k, res (ch i).g (Loc ((ch i).g * (ch j).g)) (isUnit_loc_of_dvd dij)
        (algebraMap C (Loc (ch i).g) (a k * (ch k).g ^ M) *
          (((ch i).rep _ hI (isUnit_loc _) (z i k) (hz i k)).hom b -
            ((ch i).rep _ hI (isUnit_loc _) (x i) (hx i)).hom b)) =
        A' k * ((ch i).repL hI dij (rr dij (z i k)) ((hz i k).rr dij) b -
          (ch i).repL hI dij (rr dij (x i)) ((hx i).rr dij) b) := fun k => by
      rw [map_mul, map_sub, AlgHom.commutes, Chart.repL, Chart.repL,
        (ch i).rep_rr hI dij (isUnit_loc _) ui (hz i k) b,
        (ch i).rep_rr hI dij (isUnit_loc _) ui (hx i) b]
    rw [Finset.sum_congr rfl fun k _ => hsum k,
      ← (ch i).rep_rr hI dij (isUnit_loc _) ui (hx i) b]
    -- the partition-of-unity identity
    have hamap : ∑ k, algebraMap C (Loc ((ch i).g * (ch j).g)) (a k) *
        algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ (N + M) = 1 := by
      have := congrArg (algebraMap C (Loc ((ch i).g * (ch j).g))) ha
      simpa only [map_sum, map_mul, map_pow, map_one] using this
    have key : ∀ k, A' k * ((ch i).repL hI dij (rr dij (z i k)) ((hz i k).rr dij) b -
          (ch i).repL hI dij (rr dij (x i)) ((hx i).rr dij) b) -
        A' k * ((ch i).repL hI dij (rr dji (z j k)) ((hz j k).rr dji) b -
          (ch i).repL hI dij (rr dji (x j)) ((hx j).rr dji) b) =
        algebraMap C (Loc ((ch i).g * (ch j).g)) (a k) *
          algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ (N + M) *
          ((ch i).repL hI dij (rr dji (x j)) ((hx j).rr dji) b -
            (ch i).repL hI dij (rr dij (x i)) ((hx i).rr dij) b) := by
      intro k
      have h := hM₀ i j k b
      have h' : algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ M *
          (((ch i).repL hI dij (rr dji (x j)) ((hx j).rr dji) b +
              (ch i).repL hI dij (rr dij (z i k)) ((hz i k).rr dij) b -
              (ch i).repL hI dij (rr dij (x i)) ((hx i).rr dij) b) -
            ((ch i).repL hI dij (rr dji (z j k)) ((hz j k).rr dji) b +
              algebraMap C (Loc ((ch i).g * (ch j).g)) (ch k).g ^ N *
                ((ch i).repL hI dij (rr dji (x j)) ((hx j).rr dji) b -
                  (ch i).repL hI dij (rr dij (x i)) ((hx i).rr dij) b))) = 0 := by
        rw [← Nat.sub_add_cancel (hMle i j k), pow_add, mul_assoc, h, mul_zero]
      simp only [A', map_mul, map_pow]
      linear_combination algebraMap C (Loc ((ch i).g * (ch j).g)) (a k) * h'
    rw [← sub_eq_zero]
    have hrw : ∀ (v w : Loc ((ch i).g * (ch j).g)) (P Q : Fin n → Loc ((ch i).g * (ch j).g)),
        v + ∑ k, A' k * (P k - v) - (w + ∑ k, A' k * (Q k - w)) =
          (v - w) + ∑ k, (A' k * (P k - v) - A' k * (Q k - w)) := by
      intro v w P Q
      rw [Finset.sum_sub_distrib]; ring
    rw [hrw, Finset.sum_congr rfl fun k _ => key k, ← Finset.sum_mul, hamap]
    ring
  obtain ⟨y, hy⟩ := exists_glue (fun i => (ch i).g) hspan Y hcompat
  exact ⟨y, isLift_of_cover (fun i => (ch i).g) hspan y fun i => by rw [hy i]; exact hY i⟩

/-- Every point of `Spec C` lies in the domain of some chart. -/
theorem exists_chart_at (hI : SqZero I)
    (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s) (q : Spec C) :
    ∃ ch : Chart f I x₀ s, ch.g ∉ q.asIdeal := by
  obtain ⟨p, rfl⟩ := specMap_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
    (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]; exact hI.le_nilradical) q
  have hfx : f (x₀ p) = s (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) p) := by
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (x₀ p))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x₀ p ∈ ((f ⁻¹ᵁ V : X.Opens) : Set X) from hxV) (f ⁻¹ᵁ V).2
  have hqV : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) p ∈
      ((s ⁻¹ᵁ V : (Spec C).Opens) : Set (Spec C)) := by
    show s _ ∈ V
    rw [← hfx]; exact hxV
  obtain ⟨_, ⟨_, ⟨g₁, rfl⟩, rfl⟩, hq₁, hsub₁⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqV (s ⁻¹ᵁ V).2
  obtain ⟨_, ⟨_, ⟨d, rfl⟩, rfl⟩, hp₂, hsub₂⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU (x₀ ⁻¹ᵁ U).2
  obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective d
  let ch : Chart f I x₀ s :=
    { V := V
      hV := hV
      U := U
      hU := hU
      hUV := fun x hx => hUV hx
      g := g₁ * g₂
      hs := fun p' hp' => hsub₁ fun h => hp' (p'.asIdeal.mul_mem_right _ h)
      hx := fun p' hp' => hsub₂ fun h => hp' (by
        rw [map_mul]; exact p'.asIdeal.mul_mem_left _ h) }
  refine ⟨ch, fun h => ?_⟩
  rcases Ideal.IsPrime.mem_or_mem (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) p).2 h with
    h | h
  · exact hq₁ h
  · exact hp₂ h

/-- A finite family of charts whose elements generate the unit ideal. -/
theorem exists_charts (hI : SqZero I)
    (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s) :
    ∃ (n : ℕ) (ch : Fin n → Chart f I x₀ s), Ideal.span (Set.range fun i => (ch i).g) = ⊤ := by
  classical
  choose ch hch using exists_chart_at hI h₀
  have hspan : Ideal.span (Set.range fun q => (ch q).g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hch (PrimeSpectrum.mk m hm.isPrime : PrimeSpectrum C) (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t, hts, htop⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  have hpre : ∀ c ∈ t, ∃ q, (ch q).g = c := fun c hc => hts hc
  choose qq hqq using hpre
  let e := t.equivFin.symm
  refine ⟨t.card, fun i => ch (qq (e i) (e i).2),
    eq_top_iff.mpr (htop.symm.le.trans (Ideal.span_mono ?_))⟩
  intro c hc
  refine ⟨e.symm ⟨c, hc⟩, (hqq _ _).trans ?_⟩
  rw [Equiv.apply_symm_apply]

end Langlands.AlgebraicGeometry.SmoothLifting

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- **Square-zero lifting.** -/
theorem exists_lift_sqZero [Smooth f] {C D : CommRingCat.{u}} (q : C ⟶ D)
    (hq : Function.Surjective q.hom) (hK : SqZero (RingHom.ker q.hom)) (x₀ : Spec D ⟶ X)
    (s : Spec C ⟶ S) (h : x₀ ≫ f = Spec.map q ≫ s) :
    ∃ x : Spec C ⟶ X, Spec.map q ≫ x = x₀ ∧ x ≫ f = s := by
  set I := RingHom.ker q.hom
  let e : C ⧸ I ≃+* D := RingHom.quotientKerEquivOfSurjective hq
  let eS : D ⟶ CommRingCat.of (C ⧸ I) := CommRingCat.ofHom e.symm.toRingHom
  let eH : CommRingCat.of (C ⧸ I) ⟶ D := CommRingCat.ofHom e.toRingHom
  have h1 : q ≫ eS = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext c; exact RingHom.quotientKerEquivOfSurjective_symm_apply hq c
  have h2 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ eH = q := by
    ext c; rfl
  have h3 : eS ≫ eH = 𝟙 D := by
    ext d; exact e.apply_symm_apply d
  have h₀ : (Spec.map eS ≫ x₀) ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s := by
    rw [Category.assoc, h, ← Category.assoc, ← Spec.map_comp, h1]
  obtain ⟨n, ch, hspan⟩ := exists_charts (f := f) (x₀ := Spec.map eS ≫ x₀) (s := s) hK h₀
  obtain ⟨x, hx1, hx2⟩ := exists_lift_of_charts hK h₀ ch hspan
  refine ⟨x, ?_, hx2⟩
  rw [← h2, Spec.map_comp, Category.assoc, hx1, ← Category.assoc, ← Spec.map_comp, h3,
    Spec.map_id, Category.id_comp]

end Langlands.AlgebraicGeometry.SmoothLifting
