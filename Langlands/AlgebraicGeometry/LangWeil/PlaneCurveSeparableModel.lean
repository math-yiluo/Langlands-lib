import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveCoordinateOperations

/-!
# Separable models of absolutely irreducible plane curves

Exchange of the coordinates and descent along one-coordinate Frobenius
contraction give a model separable in both coordinates, with controlled degrees.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- Exchange the two variables of a bivariate polynomial. -/
def planeCurveSwap (f : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  rename (Equiv.swap (0 : Fin 2) 1) f

theorem planeCurveSwap_involutive (f : MvPolynomial (Fin 2) R) :
    planeCurveSwap (planeCurveSwap f) = f := by
  simpa only [planeCurveSwap, renameEquiv_symm, renameEquiv_apply, Equiv.symm_swap] using
    (renameEquiv R (Equiv.swap (0 : Fin 2) 1)).symm_apply_apply f

theorem planeCurveSwap_injective :
    Function.Injective (planeCurveSwap : MvPolynomial (Fin 2) R → _) := by
  intro f g h
  have := congrArg planeCurveSwap h
  simpa only [planeCurveSwap_involutive] using this

theorem planeCurveSwap_ne_zero {f : MvPolynomial (Fin 2) R} (hf : f ≠ 0) :
    planeCurveSwap f ≠ 0 := by
  intro h
  apply hf
  apply planeCurveSwap_injective
  simpa only [planeCurveSwap, map_zero] using h

theorem planeCurveSwap_degree_first (f : MvPolynomial (Fin 2) R) :
    (planeCurveSwap f).degreeOf 0 = f.degreeOf 1 := by
  simpa only [planeCurveSwap, Equiv.swap_apply_right] using
    (degreeOf_rename_of_injective (p := f) (Equiv.swap (0 : Fin 2) 1).injective 1)

theorem planeCurveSwap_degree_second (f : MvPolynomial (Fin 2) R) :
    (planeCurveSwap f).degreeOf 1 = f.degreeOf 0 := by
  simpa only [planeCurveSwap, Equiv.swap_apply_left] using
    (degreeOf_rename_of_injective (p := f) (Equiv.swap (0 : Fin 2) 1).injective 0)

theorem planeCurveSwap_pderiv_first (f : MvPolynomial (Fin 2) R) :
    pderiv 0 (planeCurveSwap f) = planeCurveSwap (pderiv 1 f) := by
  simpa only [planeCurveSwap, Equiv.swap_apply_right] using
    (pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective 1 f)

theorem planeCurveSwap_pderiv_second (f : MvPolynomial (Fin 2) R) :
    pderiv 1 (planeCurveSwap f) = planeCurveSwap (pderiv 0 f) := by
  simpa only [planeCurveSwap, Equiv.swap_apply_left] using
    (pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective 0 f)

theorem planeCurveSwap_irreducible {F : Type u} [Field F]
    (f : MvPolynomial (Fin 2) F)
    (hf : Irreducible (map (algebraMap F (AlgebraicClosure F)) f)) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeCurveSwap f)) := by
  rw [planeCurveSwap, map_rename]
  exact (MulEquiv.irreducible_iff
    (renameEquiv (AlgebraicClosure F) (Equiv.swap (0 : Fin 2) 1))).mpr hf

theorem planeCurveSwap_zero_count (f : MvPolynomial (Fin 2) R) :
    Nat.card {v : Fin 2 → R // eval v (planeCurveSwap f) = 0} =
      Nat.card {v : Fin 2 → R // eval v f = 0} := by
  let e : (Fin 2 → R) ≃ (Fin 2 → R) :=
    { toFun := fun v => v ∘ Equiv.swap (0 : Fin 2) 1
      invFun := fun v => v ∘ Equiv.swap (0 : Fin 2) 1
      left_inv := fun v => by ext i; simp
      right_inv := fun v => by ext i; simp }
  apply Nat.card_congr (Equiv.subtypeEquiv e ?_)
  intro v
  change eval v (rename (Equiv.swap (0 : Fin 2) 1) f) = 0 ↔
    eval (v ∘ Equiv.swap (0 : Fin 2) 1) f = 0
  rw [eval_rename]

theorem planeCurveSwap_eval (f : MvPolynomial (Fin 2) R) (x y : R) :
    eval ![x, y] (planeCurveSwap f) = eval ![y, x] f := by
  rw [planeCurveSwap, eval_rename]
  have hv : (![x, y] ∘ Equiv.swap (0 : Fin 2) 1) = ![y, x] := by
    funext i
    fin_cases i <;> simp
  rw [hv]

variable {F : Type u} [Field F] [Finite F]

/-- One Frobenius contraction decreases the degree sum and controls both extrema. -/
theorem planeCurve_contractFirst_reduction (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hx : 0 < f.degreeOf 0) (hy : 0 < f.degreeOf 1) (hdx : pderiv 0 f = 0) :
    ∃ g : MvPolynomial (Fin 2) F,
      Irreducible (map (algebraMap F (AlgebraicClosure F)) g) ∧
      0 < g.degreeOf 0 ∧ 0 < g.degreeOf 1 ∧
      g.degreeOf 0 + g.degreeOf 1 < f.degreeOf 0 + f.degreeOf 1 ∧
      max (g.degreeOf 0) (g.degreeOf 1) ≤ max (f.degreeOf 0) (f.degreeOf 1) ∧
      min (g.degreeOf 0) (g.degreeOf 1) ≤ min (f.degreeOf 0) (f.degreeOf 1) ∧
      Nat.card {v : Fin 2 → F // eval v g = 0} =
        Nat.card {v : Fin 2 → F // eval v f = 0} := by
  obtain ⟨g, hgf⟩ := planeCurve_exists_contractFirst (ringChar F)
    (CharP.prime_ringChar F).ne_zero f hdx
  have ⟨hgx, hlt, hgy⟩ := planeCurve_contractFirst_degree hgf hx
  have hgirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) g) :=
    planeCurveExpandFirst_irreducible (ringChar F) (CharP.prime_ringChar F).ne_zero
      g (by rwa [hgf])
  refine ⟨g, hgirr, hgx, by omega, by omega, ?_, ?_, ?_⟩
  · exact max_le_max (Nat.le_of_lt hlt) hgy.le
  · exact min_le_min (Nat.le_of_lt hlt) hgy.le
  · have hc := planeCurveExpandFirst_zero_count g
    rw [hgf] at hc
    exact hc.symm

/-- If either partial derivative vanishes, a smaller positive-degree model exists. -/
theorem planeCurve_inseparable_reduction (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hx : 0 < f.degreeOf 0) (hy : 0 < f.degreeOf 1)
    (hbad : pderiv 0 f = 0 ∨ pderiv 1 f = 0) :
    ∃ g : MvPolynomial (Fin 2) F,
      Irreducible (map (algebraMap F (AlgebraicClosure F)) g) ∧
      0 < g.degreeOf 0 ∧ 0 < g.degreeOf 1 ∧
      g.degreeOf 0 + g.degreeOf 1 < f.degreeOf 0 + f.degreeOf 1 ∧
      max (g.degreeOf 0) (g.degreeOf 1) ≤ max (f.degreeOf 0) (f.degreeOf 1) ∧
      min (g.degreeOf 0) (g.degreeOf 1) ≤ min (f.degreeOf 0) (f.degreeOf 1) ∧
      Nat.card {v : Fin 2 → F // eval v g = 0} =
        Nat.card {v : Fin 2 → F // eval v f = 0} := by
  rcases hbad with hdx | hdy
  · exact planeCurve_contractFirst_reduction f hirr hx hy hdx
  · have hsx : 0 < (planeCurveSwap f).degreeOf 0 := by
      rwa [planeCurveSwap_degree_first]
    have hsy : 0 < (planeCurveSwap f).degreeOf 1 := by
      rwa [planeCurveSwap_degree_second]
    have hsd : pderiv 0 (planeCurveSwap f) = 0 := by
      rw [planeCurveSwap_pderiv_first, hdy]
      simp only [planeCurveSwap, map_zero]
    obtain ⟨g, hgi, hgx, hgy, hsum, hmax, hmin, hcount⟩ :=
      planeCurve_contractFirst_reduction (planeCurveSwap f)
        (planeCurveSwap_irreducible f hirr) hsx hsy hsd
    refine ⟨g, hgi, hgx, hgy, ?_, ?_, ?_, hcount.trans (planeCurveSwap_zero_count f)⟩
    · simpa only [planeCurveSwap_degree_first, planeCurveSwap_degree_second,
        add_comm] using hsum
    · simpa only [planeCurveSwap_degree_first, planeCurveSwap_degree_second,
        max_comm] using hmax
    · simpa only [planeCurveSwap_degree_first, planeCurveSwap_degree_second,
        min_comm] using hmin

/-- An absolutely irreducible curve with positive partial degrees has an ordered
model separable in both coordinates, with the same rational zero count. -/
theorem planeCurve_separable_model (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hx : 0 < f.degreeOf 0) (hy : 0 < f.degreeOf 1) :
    ∃ g : MvPolynomial (Fin 2) F,
      Irreducible (map (algebraMap F (AlgebraicClosure F)) g) ∧
      pderiv 0 g ≠ 0 ∧ pderiv 1 g ≠ 0 ∧
      0 < g.degreeOf 1 ∧ g.degreeOf 1 ≤ g.degreeOf 0 ∧
      g.degreeOf 0 ≤ max (f.degreeOf 0) (f.degreeOf 1) ∧
      g.degreeOf 1 ≤ min (f.degreeOf 0) (f.degreeOf 1) ∧
      Nat.card {v : Fin 2 → F // eval v g = 0} =
        Nat.card {v : Fin 2 → F // eval v f = 0} := by
  suffices H : ∀ n : ℕ, ∀ h : MvPolynomial (Fin 2) F,
      h.degreeOf 0 + h.degreeOf 1 = n →
      Irreducible (map (algebraMap F (AlgebraicClosure F)) h) →
      0 < h.degreeOf 0 → 0 < h.degreeOf 1 →
      ∃ g : MvPolynomial (Fin 2) F,
        Irreducible (map (algebraMap F (AlgebraicClosure F)) g) ∧
        pderiv 0 g ≠ 0 ∧ pderiv 1 g ≠ 0 ∧
        0 < g.degreeOf 1 ∧ g.degreeOf 1 ≤ g.degreeOf 0 ∧
        g.degreeOf 0 ≤ max (h.degreeOf 0) (h.degreeOf 1) ∧
        g.degreeOf 1 ≤ min (h.degreeOf 0) (h.degreeOf 1) ∧
        Nat.card {v : Fin 2 → F // eval v g = 0} =
          Nat.card {v : Fin 2 → F // eval v h = 0} by
    exact H _ f rfl hirr hx hy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h hn hi hx hy
    by_cases hbad : pderiv 0 h = 0 ∨ pderiv 1 h = 0
    · obtain ⟨k, hki, hkx, hky, hklt, hkmax, hkmin, hkcount⟩ :=
        planeCurve_inseparable_reduction h hi hx hy hbad
      obtain ⟨g, hgi, hgdx, hgdy, hgy, hgord, hgmax, hgmin, hgcount⟩ :=
        ih (k.degreeOf 0 + k.degreeOf 1) (by omega) k rfl hki hkx hky
      exact ⟨g, hgi, hgdx, hgdy, hgy, hgord, hgmax.trans hkmax,
        hgmin.trans hkmin, hgcount.trans hkcount⟩
    · have hdx : pderiv 0 h ≠ 0 := fun hz => hbad (Or.inl hz)
      have hdy : pderiv 1 h ≠ 0 := fun hz => hbad (Or.inr hz)
      by_cases hord : h.degreeOf 1 ≤ h.degreeOf 0
      · exact ⟨h, hi, hdx, hdy, hy, hord,
          le_max_left _ _, by simpa only [min_eq_right hord] using (le_refl (h.degreeOf 1)), rfl⟩
      · have hrev : h.degreeOf 0 ≤ h.degreeOf 1 := by omega
        refine ⟨planeCurveSwap h, planeCurveSwap_irreducible h hi, ?_, ?_,
          ?_, ?_, ?_, ?_, planeCurveSwap_zero_count h⟩
        · rw [planeCurveSwap_pderiv_first]
          exact planeCurveSwap_ne_zero hdy
        · rw [planeCurveSwap_pderiv_second]
          exact planeCurveSwap_ne_zero hdx
        · rwa [planeCurveSwap_degree_second]
        · simpa only [planeCurveSwap_degree_first, planeCurveSwap_degree_second] using hrev
        · rw [planeCurveSwap_degree_first]
          exact le_max_right _ _
        · rw [planeCurveSwap_degree_second, min_eq_left hrev]

end Langlands.AlgebraicGeometry.LangWeil
