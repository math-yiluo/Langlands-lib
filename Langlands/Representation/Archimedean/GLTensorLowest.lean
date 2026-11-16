import Langlands.Representation.Archimedean.GLBurnside
import Langlands.Representation.Archimedean.BGChaseReps

/-!
# Lowest weight vectors in `Hom(W, V)` and covariants

* `aeval_prod_apply_eq_zero` (filtration kill): if weight vectors `x_j` (`j ∈ J`) satisfy
  `e_pq x_j ∈ span {x_i : ht ν_i > ht ν_j}` for `q < p`, then
  `∏_{i ∈ J} (c - casVal ν_i)` kills every `x_j`.
* `homFam s e`: the family `φ ↦ e_pq ∘ φ - φ ∘ s_pq` on `Hom(W, V)`.
* `isLowest_ys`: for a lowest weight vector `v₀` of weight `λ` of `V`, a weight basis `b` of `W`
  and `μ_k = 0`, the vector `ys k = R(c) (b_k^* ⊗ v₀)` is a lowest weight vector of weight `λ`.
* `exists_hom_of_lowest`: a lowest weight vector `y` of weight `λ` of a finite-dimensional `V₂`
  is the image of the generator under a map of families from `V₁ = genSub {v₀}`.
* `exists_covariant`: the corresponding covariant `g : W → End V` with `g(w) v₀ = y(w)`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GLReynolds

open ComplexJacquetFinite Module Polynomial

/-! ### Filtration kill -/

section Kill

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {e : Fin n → Fin n → Module.End ℂ V}

theorem aeval_cas_apply_comm (he : IsGlFamily e) (Q : ℂ[X]) (a b : Fin n) (v : V) :
    e a b (aeval (cas e) Q v) = aeval (cas e) Q (e a b v) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, LinearMap.add_apply, hP, hQ]
  | monomial k c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      cas_pow_apply_comm he, Module.End.mul_apply, Module.algebraMap_end_apply]

theorem isWeightVec_aeval_cas (he : IsGlFamily e) (Q : ℂ[X]) {μ : Fin n → ℤ} {v : V}
    (hv : IsWeightVec e μ v) : IsWeightVec e μ (aeval (cas e) Q v) := by
  intro p
  rw [aeval_cas_apply_comm he, hv p, map_smul]

theorem isStable_ker_aeval_cas (he : IsGlFamily e) (Q : ℂ[X]) :
    IsStable e (LinearMap.ker (aeval (cas e) Q)) := by
  intro p q v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← aeval_cas_apply_comm he, hv, map_zero]

/-- A weight vector of weight `μ` that is lowest modulo a stable subspace `G` is an eigenvector
of the Casimir operator with eigenvalue `casVal μ` modulo `G`. -/
theorem cas_sub_mem (he : IsGlFamily e) {G : Submodule ℂ V} (hG : IsStable e G)
    {μ : Fin n → ℤ} {x : V} (hx : IsWeightVec e μ x) (hlow : ∀ p q, q < p → e p q x ∈ G) :
    cas e x - ((casVal μ : ℤ) : ℂ) • x ∈ G := by
  have hS : ∀ p q, G ≤ G.comap (e p q) := fun p q v hv => hG p q v hv
  have h1 : IsWeightVec (qFam G hS) μ (Submodule.Quotient.mk x) := by
    intro p
    rw [qFam_mk, hx p, Submodule.Quotient.mk_smul]
  have h2 : ∀ p q, q < p → qFam G hS p q (Submodule.Quotient.mk x) = 0 := by
    intro p q hqp
    rw [qFam_mk, Submodule.Quotient.mk_eq_zero]
    exact hlow p q hqp
  have h3 := cas_apply_lowest (isGlFamily_qFam G hS he) h1 h2
  rw [cas_qFam_mk] at h3
  refine (Submodule.Quotient.eq G).mp ?_
  rw [h3, Submodule.Quotient.mk_smul]
  rfl

theorem aeval_X_sub_C_apply (c : ℂ) (v : V) :
    aeval (cas e) (X - C c) v = cas e v - c • v := by
  rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]

/-- **Filtration kill.** Let `x_j` (`j ∈ J`) be weight vectors of weights `ν_j` such that
`e_pq x_j` lies in the span of the `x_i` (`i ∈ J`) of larger height for `q < p`. Then
`∏_{i ∈ J} (c - casVal ν_i)` kills every `x_j`. -/
theorem aeval_prod_apply_eq_zero (he : IsGlFamily e) {ι : Type*} [DecidableEq ι] (x : ι → V)
    (ν : ι → Fin n → ℤ) (hx : ∀ i, IsWeightVec e (ν i) (x i)) (J : Finset ι)
    (hJ : ∀ j ∈ J, ∀ p q, q < p → e p q (x j) ∈
      Submodule.span ℂ (x '' {i | i ∈ J ∧ ht (ν j) < ht (ν i)})) :
    ∀ j ∈ J, aeval (cas e) (∏ i ∈ J, (X - C ((casVal (ν i) : ℤ) : ℂ))) (x j) = 0 := by
  induction J using Finset.strongInduction with
  | H J ih =>
    rcases J.eq_empty_or_nonempty with rfl | hne
    · intro j hj
      simp at hj
    obtain ⟨j₀, hj₀, hmin⟩ := J.exists_min_image (fun i => ht (ν i)) hne
    have hJ' : ∀ j ∈ J.erase j₀, ∀ p q, q < p → e p q (x j) ∈
        Submodule.span ℂ (x '' {i | i ∈ J.erase j₀ ∧ ht (ν j) < ht (ν i)}) := by
      intro j hj p q hqp
      have hjJ := Finset.mem_of_mem_erase hj
      refine Submodule.span_mono ?_ (hJ j hjJ p q hqp)
      rintro _ ⟨i, ⟨hi, hlt⟩, rfl⟩
      refine ⟨i, ⟨Finset.mem_erase.mpr ⟨?_, hi⟩, hlt⟩, rfl⟩
      rintro rfl
      exact absurd (hmin j hjJ) (not_le.mpr hlt)
    have ih' := ih (J.erase j₀) (Finset.erase_ssubset hj₀) hJ'
    set Q' := ∏ i ∈ J.erase j₀, (X - C ((casVal (ν i) : ℤ) : ℂ)) with hQ'
    have hprod : ∏ i ∈ J, (X - C ((casVal (ν i) : ℤ) : ℂ)) =
        (X - C ((casVal (ν j₀) : ℤ) : ℂ)) * Q' :=
      (Finset.mul_prod_erase J _ hj₀).symm
    have hK : IsStable e (LinearMap.ker (aeval (cas e) Q')) := isStable_ker_aeval_cas he Q'
    intro j hj
    rw [hprod]
    by_cases hjj : j = j₀
    · subst hjj
      rw [mul_comm, map_mul, Module.End.mul_apply, aeval_X_sub_C_apply]
      refine cas_sub_mem he hK (hx j) fun p q hqp => ?_
      refine Submodule.span_le.mpr ?_ (hJ j hj p q hqp)
      rintro _ ⟨i, ⟨hi, hlt⟩, rfl⟩
      refine ih' i (Finset.mem_erase.mpr ⟨?_, hi⟩)
      rintro rfl
      exact lt_irrefl _ hlt
    · rw [map_mul, Module.End.mul_apply, ih' j (Finset.mem_erase.mpr ⟨hjj, hj⟩), map_zero]

end Kill

/-! ### Heights -/

theorem ht_sub {n : ℕ} (a b : Fin n → ℤ) : ht (a - b) = ht a - ht b := by
  simp only [ht, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem ht_zero {n : ℕ} : ht (0 : Fin n → ℤ) = 0 := by
  simp [ht]

/-! ### The family on `Hom(W, V)` -/

section Hom

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {n : ℕ}

/-- The family `φ ↦ e_pq ∘ φ - φ ∘ s_pq` on `Hom(W, V)`. -/
def homFam (s : Fin n → Fin n → Module.End ℂ W) (e : Fin n → Fin n → Module.End ℂ V) :
    Fin n → Fin n → Module.End ℂ (W →ₗ[ℂ] V) := fun p q =>
  { toFun := fun φ => e p q ∘ₗ φ - φ ∘ₗ s p q
    map_add' := fun φ ψ => by
      ext w
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
      abel
    map_smul' := fun c φ => by
      ext w
      simp [smul_sub] }

theorem homFam_apply (s : Fin n → Fin n → Module.End ℂ W) (e : Fin n → Fin n → Module.End ℂ V)
    (p q : Fin n) (φ : W →ₗ[ℂ] V) (w : W) :
    homFam s e p q φ w = e p q (φ w) - φ (s p q w) := rfl

variable {s : Fin n → Fin n → Module.End ℂ W} {e : Fin n → Fin n → Module.End ℂ V}

theorem homFam_eq (hs : IsGlFamily s) (he : IsGlFamily e) :
    homFam s e = famOf (BGChase.homLie (lieOf s hs) (lieOf e he)) := by
  funext p q
  ext φ w
  rw [homFam_apply, famOf_apply, BGChase.homLie_apply, lieOf_single, lieOf_single]

theorem isGlFamily_homFam (hs : IsGlFamily s) (he : IsGlFamily e) :
    IsGlFamily (homFam s e) := by
  rw [homFam_eq hs he]
  exact isGlFamily_famOf _

/-! ### The vectors `b_i^* ⊗ v₀` -/

variable {ι : Type*} (b : Module.Basis ι ℂ W) {μ : ι → Fin n → ℤ}

theorem coord_apply_eq_sum [Fintype ι] (i : ι) (T : Module.End ℂ W) (w : W) :
    b.coord i (T w) = ∑ j, b.coord i (T (b j)) * b.coord j w := by
  conv_lhs => rw [← b.sum_repr w]
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]

theorem coord_diag (hb : ∀ i, IsWeightVec s (μ i) (b i)) (i : ι) (p : Fin n) (w : W) :
    b.coord i (s p p w) = ((μ i p : ℤ) : ℂ) * b.coord i w := by
  have h := LinearMap.congr_fun
    (BGChase.coord_comp_of_isWt b (H := fun r => s r r) (μ := μ) hb i p) w
  simpa using h

/-- A nonzero matrix coefficient `b_j^*(s_pq b_i)` forces `μ_j = μ_i + ε_p - ε_q`. -/
theorem wt_eq_of_coord_ne_zero (hs : IsGlFamily s) (hb : ∀ i, IsWeightVec s (μ i) (b i))
    {p q : Fin n} (hpq : p ≠ q) {i j : ι} (h : b.coord j (s p q (b i)) ≠ 0) :
    μ j = μ i + Pi.single p 1 - Pi.single q 1 := by
  have hv := isWeightVec_shift hs (hb i) hpq
  funext r
  have h1 := coord_diag b hb j r (s p q (b i))
  rw [hv r, map_smul, smul_eq_mul] at h1
  have h2 := mul_right_cancel₀ h h1
  exact_mod_cast h2.symm

/-- The vector `b_i^* ⊗ v₀ ∈ Hom(W, V)`. -/
def xs (v₀ : V) (i : ι) : W →ₗ[ℂ] V := (b.coord i).smulRight v₀

theorem xs_apply (v₀ : V) (i : ι) (w : W) : xs b v₀ i w = b.coord i w • v₀ := rfl

variable [Fintype ι]

theorem homFam_xs (v₀ : V) (p q : Fin n) (i : ι) :
    homFam s e p q (xs b v₀ i) =
      xs b (e p q v₀) i - ∑ j, b.coord i (s p q (b j)) • xs b v₀ j := by
  ext w
  rw [homFam_apply, xs_apply, xs_apply, map_smul, LinearMap.sub_apply, xs_apply,
    LinearMap.sum_apply, coord_apply_eq_sum b i (s p q) w, Finset.sum_smul]
  simp only [LinearMap.smul_apply, xs_apply, smul_smul]

omit [Fintype ι] in
theorem isWeightVec_xs (hb : ∀ i, IsWeightVec s (μ i) (b i)) {lam : Fin n → ℤ} {v₀ : V}
    (hv₀ : IsWeightVec e lam v₀) (i : ι) :
    IsWeightVec (homFam s e) (lam - μ i) (xs b v₀ i) := by
  intro p
  ext w
  rw [homFam_apply, xs_apply, xs_apply, map_smul, hv₀ p, coord_diag b hb i p w,
    LinearMap.smul_apply, xs_apply, smul_smul, smul_smul, ← sub_smul]
  congr 1
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

/-- For `q < p`, `e_pq (b_i^* ⊗ v₀)` is a combination of `b_j^* ⊗ v₀` with `μ_i = μ_j + ε_p - ε_q`
when `v₀` is lowest. -/
theorem homFam_xs_mem (hs : IsGlFamily s) (hb : ∀ i, IsWeightVec s (μ i) (b i))
    {lam : Fin n → ℤ} {v₀ : V} (hv₀ : IsLowest e lam v₀) {p q : Fin n} (hqp : q < p) (i : ι)
    (S : Set ι) (hS : ∀ j, μ i = μ j + Pi.single p 1 - Pi.single q 1 → j ∈ S) :
    homFam s e p q (xs b v₀ i) ∈ Submodule.span ℂ (xs b v₀ '' S) := by
  rw [homFam_xs, hv₀.2 p q hqp]
  have h0 : xs b (0 : V) i = 0 := by ext w; simp [xs_apply]
  rw [h0, zero_sub]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ => ?_)
  by_cases hc : b.coord i (s p q (b j)) = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨j, hS j (wt_eq_of_coord_ne_zero b hs hb (ne_of_gt hqp) hc), rfl⟩)

/-- The indices of negative height. -/
def negIdx (μ : ι → Fin n → ℤ) : Finset ι := Finset.univ.filter fun i => ht (μ i) < 0

/-- The polynomial `R = ∏_{ht μ_i < 0} (X - casVal (λ - μ_i))`. -/
def polR (μ : ι → Fin n → ℤ) (lam : Fin n → ℤ) : ℂ[X] :=
  ∏ i ∈ negIdx μ, (X - C ((casVal (lam - μ i) : ℤ) : ℂ))

/-- The vector `ys k = R(c) (b_k^* ⊗ v₀)`. -/
def ys (s : Fin n → Fin n → Module.End ℂ W) (e : Fin n → Fin n → Module.End ℂ V)
    (μ : ι → Fin n → ℤ) (lam : Fin n → ℤ) (v₀ : V) (k : ι) : W →ₗ[ℂ] V :=
  aeval (cas (homFam s e)) (polR μ lam) (xs b v₀ k)

theorem ht_shift' {a c : Fin n → ℤ} {p q : Fin n} (h : a = c + Pi.single p 1 - Pi.single q 1) :
    ht a = ht c + p - q := by
  rw [h, ht_shift]

theorem aeval_polR_xs (hs : IsGlFamily s) (he : IsGlFamily e)
    (hb : ∀ i, IsWeightVec s (μ i) (b i)) {lam : Fin n → ℤ} {v₀ : V} (hv₀ : IsLowest e lam v₀)
    [DecidableEq ι] : ∀ j ∈ negIdx μ, aeval (cas (homFam s e)) (polR μ lam) (xs b v₀ j) = 0 := by
  refine aeval_prod_apply_eq_zero (isGlFamily_homFam hs he) (xs b v₀) (fun i => lam - μ i)
    (fun i => isWeightVec_xs b hb hv₀.1 i) (negIdx μ) fun j hj p q hqp => ?_
  refine homFam_xs_mem b hs hb hv₀ hqp j _ fun i hi => ?_
  have hji := ht_shift' hi
  have hj' : ht (μ j) < 0 := (Finset.mem_filter.mp hj).2
  have hqp' : (q : ℤ) < p := by exact_mod_cast hqp
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, ?_⟩
  simp only [ht_sub]
  omega

/-- **Lowest weight vectors in `Hom(W, V)`.** For `μ_k = 0`, `ys k` is a lowest weight vector of
weight `λ`. -/
theorem isLowest_ys (hs : IsGlFamily s) (he : IsGlFamily e)
    (hb : ∀ i, IsWeightVec s (μ i) (b i)) {lam : Fin n → ℤ} {v₀ : V} (hv₀ : IsLowest e lam v₀)
    {k : ι} (hk : μ k = 0) : IsLowest (homFam s e) lam (ys b s e μ lam v₀ k) := by
  classical
  constructor
  · have h := isWeightVec_xs b hb hv₀.1 k
    rw [hk, sub_zero] at h
    exact isWeightVec_aeval_cas (isGlFamily_homFam hs he) _ h
  · intro p q hqp
    rw [ys, aeval_cas_apply_comm (isGlFamily_homFam hs he)]
    have hmem : homFam s e p q (xs b v₀ k) ∈
        Submodule.span ℂ (xs b v₀ '' (negIdx μ : Set ι)) := by
      refine homFam_xs_mem b hs hb hv₀ hqp k _ fun i hi => ?_
      have hki := ht_shift' hi
      rw [hk, ht_zero] at hki
      have hqp' : (q : ℤ) < p := by exact_mod_cast hqp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hle : Submodule.span ℂ (xs b v₀ '' (negIdx μ : Set ι)) ≤
        LinearMap.ker (aeval (cas (homFam s e)) (polR μ lam)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact aeval_polR_xs b hs he hb hv₀ i hi
    exact hle hmem

end Hom

/-! ### Maps out of a module generated by a lowest weight vector -/

section Gamma

variable {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
  {e₁ : Fin n → Fin n → Module.End ℂ V₁} {e₂ : Fin n → Fin n → Module.End ℂ V₂}

/-- The diagonal family on `V₁ × V₂`. -/
def prodFam (e₁ : Fin n → Fin n → Module.End ℂ V₁) (e₂ : Fin n → Fin n → Module.End ℂ V₂) :
    Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun p q => LinearMap.prodMap (e₁ p q) (e₂ p q)

theorem prodFam_apply (p q : Fin n) (x : V₁ × V₂) :
    prodFam e₁ e₂ p q x = (e₁ p q x.1, e₂ p q x.2) := rfl

theorem isGlFamily_prodFam (he₁ : IsGlFamily e₁) (he₂ : IsGlFamily e₂) :
    IsGlFamily (prodFam e₁ e₂) := by
  intro a b c d
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · have h := LinearMap.congr_fun (he₁ a b c d) x.1
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, prodFam_apply, Prod.fst_sub]
    rw [h]
    split_ifs <;> simp [prodFam_apply]
  · have h := LinearMap.congr_fun (he₂ a b c d) x.2
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, prodFam_apply, Prod.snd_sub]
    rw [h]
    split_ifs <;> simp [prodFam_apply]

/-- **The `Γ`-trick.** If `V₁` is generated by a nonzero lowest weight vector `v₀` of weight
`λ` and `y ∈ V₂` is a lowest weight vector of weight `λ`, there is a map of families
`Φ : V₁ → V₂` with `Φ v₀ = y`. -/
theorem exists_hom_of_lowest [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂]
    (he₁ : IsGlFamily e₁) (he₂ : IsGlFamily e₂) {lam : Fin n → ℤ}
    {v₀ : V₁} (hv₀ : IsLowest e₁ lam v₀) (hv₀0 : v₀ ≠ 0) (hgen : genSub e₁ {v₀} = ⊤) {y : V₂}
    (hy : IsLowest e₂ lam y) :
    ∃ Φ : V₁ →ₗ[ℂ] V₂, (∀ p q v, Φ (e₁ p q v) = e₂ p q (Φ v)) ∧ Φ v₀ = y := by
  classical
  set f := prodFam e₁ e₂ with hfdef
  have hf : IsGlFamily f := isGlFamily_prodFam he₁ he₂
  set z₀ : V₁ × V₂ := (v₀, y)
  have hz₀ : IsLowest f lam z₀ := by
    constructor
    · intro p
      rw [prodFam_apply, hv₀.1 p, hy.1 p, Prod.smul_mk]
    · intro p q hqp
      rw [prodFam_apply, hv₀.2 p q hqp, hy.2 p q hqp, Prod.mk_zero_zero]
  set Γ := genSub f {z₀}
  have hΓ : IsStable f Γ := isStable_genSub {z₀}
  set fΓ := resFam Γ hΓ
  have hfΓ : IsGlFamily fΓ := isGlFamily_resFam hf Γ hΓ
  set γ₀ : Γ := ⟨z₀, mem_genSub_self z₀⟩
  have hγ₀ : IsLowest fΓ lam γ₀ := by
    constructor
    · exact isWeightVec_resFam_iff.mpr hz₀.1
    · intro p q hqp
      apply Subtype.ext
      exact hz₀.2 p q hqp
  have hγ₀0 : γ₀ ≠ 0 := fun h => hv₀0 (congrArg (fun x : Γ => (x : V₁ × V₂).1) h)
  have hirr : ∀ Z : Submodule ℂ Γ, IsStable fΓ Z → Z ≠ ⊥ → Z = ⊤ := fun Z hZ hZ0 =>
    eq_top_of_lowest hfΓ (intWeights_resFam_genSub hf hz₀) hγ₀ hγ₀0 (genSub_resFam_eq_top z₀)
      hZ hZ0
  set π₁ : Γ →ₗ[ℂ] V₁ := LinearMap.fst ℂ V₁ V₂ ∘ₗ Γ.subtype
  have hπ₁ : ∀ p q γ, π₁ (fΓ p q γ) = e₁ p q (π₁ γ) := fun p q γ => rfl
  have hinj : Function.Injective π₁ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    have hstab : IsStable fΓ (LinearMap.ker π₁) := by
      intro p q γ hγ
      rw [LinearMap.mem_ker] at hγ ⊢
      rw [hπ₁, hγ, map_zero]
    have htop := hirr _ hstab hne
    have : γ₀ ∈ LinearMap.ker π₁ := by rw [htop]; trivial
    exact hv₀0 this
  have hsurj : Function.Surjective π₁ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hgen]
    apply genSub_le
    · rintro _ (h : _ = v₀)
      rw [h]
      exact ⟨γ₀, rfl⟩
    · rintro p q _ ⟨γ, rfl⟩
      exact ⟨fΓ p q γ, hπ₁ p q γ⟩
  set E := LinearEquiv.ofBijective π₁ ⟨hinj, hsurj⟩
  have hE : ∀ γ, E γ = π₁ γ := fun γ => rfl
  refine ⟨LinearMap.snd ℂ V₁ V₂ ∘ₗ Γ.subtype ∘ₗ E.symm.toLinearMap, ?_, ?_⟩
  · intro p q v
    have hsymm : E.symm (e₁ p q v) = fΓ p q (E.symm v) := by
      rw [LinearEquiv.symm_apply_eq, hE, hπ₁, ← hE, LinearEquiv.apply_symm_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm]
    rfl
  · have hsymm : E.symm v₀ = γ₀ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm]
    rfl

end Gamma

/-! ### Covariants -/

section Covariant

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {n : ℕ}
  {s : Fin n → Fin n → Module.End ℂ W} {e : Fin n → Fin n → Module.End ℂ V}

/-- **Covariants from lowest weight vectors.** If `V` is generated by a nonzero lowest weight
vector `v₀` of weight `λ` and `y ∈ Hom(W, V)` is a lowest weight vector of weight `λ`, there is a
covariant `g : W → End V` (`g(s_pq w) = e_pq g(w) - g(w) e_pq`) with `g(w) v₀ = y(w)`. -/
theorem exists_covariant (hs : IsGlFamily s) (he : IsGlFamily e) {lam : Fin n → ℤ} {v₀ : V}
    (hv₀ : IsLowest e lam v₀) (hv₀0 : v₀ ≠ 0) (hgen : genSub e {v₀} = ⊤) {y : W →ₗ[ℂ] V}
    (hy : IsLowest (homFam s e) lam y) :
    ∃ g : W →ₗ[ℂ] Module.End ℂ V, (∀ p q w, g (s p q w) = e p q * g w - g w * e p q) ∧
      ∀ w, g w v₀ = y w := by
  obtain ⟨Φ, hΦ, hΦ₀⟩ := exists_hom_of_lowest he (isGlFamily_homFam hs he) hv₀ hv₀0 hgen hy
  refine ⟨Φ.flip, fun p q w => ?_, fun w => ?_⟩
  · ext v
    have h := LinearMap.congr_fun (hΦ p q v) w
    rw [homFam_apply] at h
    simp only [LinearMap.flip_apply, LinearMap.sub_apply, Module.End.mul_apply, h]
    abel
  · rw [LinearMap.flip_apply, hΦ₀]

end Covariant

end GLReynolds

end Langlands.Archimedean
