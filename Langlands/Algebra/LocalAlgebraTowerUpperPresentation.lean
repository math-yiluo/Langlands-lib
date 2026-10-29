import Langlands.Algebra.LocalAlgebraApproximationExistence

/-! # A polynomial presentation of the upper ring over the middle ring -/

namespace Langlands.Algebra

namespace LocalAlgebraTowerApproximation

open LocalAlgebraApproximationExistence MvPolynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Presentations of `S` and of `T` over `R` give a presentation of `T` over `S`, in the sense
of `Pres`. The variables are those of `T`; the relations are the relations of `T` with
coefficients pushed to `S`, together with one relation `x_k * b_k - a_k` for each generator
`x_k` of `S`, where `a_k / b_k` represents the image of `x_k` in `T`. -/
theorem nonempty_pres_upper (PS : Pres R R S (RingEquiv.refl R))
    (PT : Pres R R T (RingEquiv.refl R)) : Nonempty (Pres S S T (RingEquiv.refl S)) := by
  classical
  choose A B hB hAB using fun k : Fin PS.n ↦ PT.surj (algebraMap S T (PS.ρ (X k)))
  let φ : MvPolynomial (Fin PT.n) R →+* MvPolynomial (Fin PT.n) S := map (algebraMap R S)
  let σ : MvPolynomial (Fin PT.n) S →+* T := eval₂Hom (algebraMap S T) fun k ↦ PT.ρ (X k)
  have hσφ (f : MvPolynomial (Fin PT.n) R) : σ (φ f) = PT.ρ f := by
    have h : σ.comp φ = PT.ρ := by
      refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun k ↦ ?_)
      · simp only [RingHom.comp_apply, φ, σ, map_C, eval₂Hom_C, PT.ρ_C,
          ← IsScalarTower.algebraMap_apply]
        rfl
      · simp [φ, σ]
    exact DFunLike.congr_fun h f
  let rel : Fin PS.n → MvPolynomial (Fin PT.n) S := fun k ↦ C (PS.ρ (X k)) * φ (B k) - φ (A k)
  let G : Finset (MvPolynomial (Fin PT.n) S) := PT.F.image φ ∪ Finset.univ.image rel
  have hσG : ∀ g ∈ G, σ g = 0 := by
    intro g hg
    rcases Finset.mem_union.1 hg with hg | hg
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hg
      rw [hσφ, PT.ρ_F f hf]
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hg
      simp only [rel, map_sub, map_mul, hσφ, σ, eval₂Hom_C]
      rw [← hAB k, sub_self]
  let J : Ideal (MvPolynomial (Fin PT.n) S) := Ideal.span (G : Set _)
  let π := Ideal.Quotient.mk J
  have hJ : J ≤ RingHom.ker σ :=
    Ideal.span_le.2 fun g hg ↦ RingHom.mem_ker.2 (hσG g (Finset.mem_coe.1 hg))
  let σ' : MvPolynomial (Fin PT.n) S ⧸ J →+* T :=
    Ideal.Quotient.lift J σ fun _ ha ↦ RingHom.mem_ker.1 (hJ ha)
  have hσ' (f : MvPolynomial (Fin PT.n) S) : σ' (π f) = σ f := Ideal.Quotient.lift_mk _ _ _
  -- The fractions of polynomials over `R` with denominators that become units in `T`.
  let Fr : Subring (MvPolynomial (Fin PT.n) S ⧸ J) :=
    { carrier := {q | ∃ a c, IsUnit (PT.ρ c) ∧ π (φ c) * q = π (φ a)}
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro x y ⟨a, c, hc, hx⟩ ⟨b, d, hd, hy⟩
        refine ⟨a * d + b * c, c * d, by rw [map_mul]; exact hc.mul hd, ?_⟩
        simp only [map_mul, map_add]
        rw [← hx, ← hy]
        ring
      mul_mem' := by
        rintro x y ⟨a, c, hc, hx⟩ ⟨b, d, hd, hy⟩
        refine ⟨a * b, c * d, by rw [map_mul]; exact hc.mul hd, ?_⟩
        simp only [map_mul]
        rw [← hx, ← hy]
        ring
      neg_mem' := by
        rintro x ⟨a, c, hc, hx⟩
        refine ⟨-a, c, hc, ?_⟩
        rw [map_neg, map_neg, ← hx]
        ring }
  have hφFr (a : MvPolynomial (Fin PT.n) R) : π (φ a) ∈ Fr := ⟨a, 1, by simp, by simp⟩
  have hinv (q q' : MvPolynomial (Fin PT.n) S ⧸ J) (hq : q ∈ Fr) (hqq' : q * q' = 1) :
      q' ∈ Fr := by
    obtain ⟨a, c, hc, h⟩ := hq
    refine ⟨c, a, ?_, ?_⟩
    · have hu : IsUnit (σ' q) := (Units.mkOfMulEqOne q q' hqq').isUnit.map σ'
      have e := congrArg σ' h
      rw [map_mul, hσ', hσ', hσφ, hσφ] at e
      rw [← e]
      exact hc.mul hu
    · rw [← h, mul_assoc, hqq', mul_one]
  have hX (k : Fin PS.n) : π (C (PS.ρ (X k))) ∈ Fr := by
    refine ⟨A k, B k, hB k, ?_⟩
    rw [← map_mul, mul_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)))
  have hρS (u : MvPolynomial (Fin PS.n) R) : π (C (PS.ρ u)) ∈ Fr := by
    induction u using MvPolynomial.induction_on with
    | C r => simpa [φ, PS.ρ_C] using hφFr (C r)
    | add p q hp hq =>
      rw [map_add, map_add, map_add]
      exact Fr.add_mem hp hq
    | mul_X p k hp =>
      rw [map_mul, map_mul, map_mul]
      exact Fr.mul_mem hp (hX k)
  have hC (s : S) : π (C s) ∈ Fr := by
    obtain ⟨u, v, hv, hs⟩ := PS.surj s
    obtain ⟨w, hw⟩ := hv.exists_right_inv
    have hs' : s = PS.ρ u * w := by
      rw [← hs, mul_assoc, hw, mul_one]
    rw [hs', map_mul, map_mul]
    refine Fr.mul_mem (hρS u) (hinv _ _ (hρS v) ?_)
    rw [← map_mul, ← map_mul, hw, map_one, map_one]
  have hall (f : MvPolynomial (Fin PT.n) S) : π f ∈ Fr := by
    induction f using MvPolynomial.induction_on with
    | C s => exact hC s
    | add p q hp hq =>
      rw [map_add]
      exact Fr.add_mem hp hq
    | mul_X p k hp =>
      rw [map_mul]
      refine Fr.mul_mem hp ?_
      have := hφFr (X k)
      simpa [φ] using this
  refine ⟨⟨PT.n, G, σ, fun s ↦ ?_, hσG, fun t ↦ ?_, fun f hf ↦ ?_⟩⟩
  · simp [σ]
  · obtain ⟨a, c, hc, h⟩ := PT.surj t
    exact ⟨φ a, φ c, by rwa [hσφ], by rw [hσφ, hσφ, h]⟩
  · obtain ⟨a, c, hc, h⟩ := hall f
    have ha : PT.ρ a = 0 := by
      have e := congrArg σ' h
      rw [map_mul, hσ', hσ', hσ', hσφ, hσφ, hf, mul_zero] at e
      exact e.symm
    obtain ⟨d, hd, hda⟩ := PT.ker a ha
    refine ⟨φ (d * c), by rw [hσφ, map_mul]; exact hd.mul hc, ?_⟩
    have hJ' : φ (d * a) ∈ J := by
      have h1 := Ideal.mem_map_of_mem φ hda
      rw [Ideal.map_span] at h1
      refine Ideal.span_mono ?_ h1
      rintro _ ⟨g, hg, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_union_left _
        (Finset.mem_image_of_mem φ (Finset.mem_coe.1 hg)))
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (φ (d * c) * f) = 0
    simp only [map_mul]
    rw [mul_assoc, h, show π (φ d) * π (φ a) = π (φ (d * a)) by simp only [map_mul]]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hJ'

/-- If `S` and `T` are essentially finitely presented over `R`, then `T` has a presentation over
`S` in the sense of `Pres`. -/
theorem nonempty_pres_upper_of_essFinitePresentation (hS : EssFinitePresentation R S)
    (hT : EssFinitePresentation R T) : Nonempty (Pres S S T (RingEquiv.refl S)) := by
  obtain ⟨PS⟩ := nonempty_pres (RingEquiv.refl R) hS
  obtain ⟨PT⟩ := nonempty_pres (RingEquiv.refl R) hT
  exact nonempty_pres_upper PS PT

end LocalAlgebraTowerApproximation

end Langlands.Algebra
