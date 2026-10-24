import Mathlib

/-!
# Cohomological triviality of complete filtrations

Let `G` act on an abelian group `Γ` (written multiplicatively) and let
`V 0 ⊇ V 1 ⊇ ⋯` be `G`-stable subgroups. Suppose every cocycle with values in `V k` agrees
with a coboundary of an element of `V k` up to an error in `V (k + 1)`, and that the filtration
is complete and separated. Then every multiplicative `1`- or `2`-cocycle with values in `V 0`
is the coboundary of a cochain with values in `V 0`.

We also record the explicit contracting formulas showing that coinduced modules `G → Y`,
with `g` acting by `φ ↦ (ρ ↦ φ (g⁻¹ * ρ))`, satisfy this approximation property modulo any
subgroup of `Y`.
-/

namespace Langlands.Cohomology.CompleteFiltration

open groupCohomology

section Boundaries

variable {G Γ : Type*} [Group G] [CommGroup Γ] [MulDistribMulAction G Γ]

/-- The multiplicative coboundary `g ↦ g • b / b` of an element `b`. -/
def coboundary1 (b : Γ) : G → Γ := fun g => g • b / b

/-- The multiplicative coboundary `(g, h) ↦ g • x h / x (g * h) * x g` of a `1`-cochain. -/
def coboundary2 (x : G → Γ) : G × G → Γ := fun p => p.1 • x p.2 / x (p.1 * p.2) * x p.1

theorem coboundary1_div (b c : Γ) (g : G) :
    coboundary1 (b / c) g = coboundary1 b g / coboundary1 c g := by
  simp only [coboundary1, smul_div']
  exact div_div_div_comm _ _ _ _

theorem coboundary1_mul (b c : Γ) (g : G) :
    coboundary1 (b * c) g = coboundary1 b g * coboundary1 c g := by
  simp only [coboundary1, smul_mul']
  exact mul_div_mul_comm _ _ _ _

theorem coboundary1_one (g : G) : coboundary1 (1 : Γ) g = 1 := by
  simp [coboundary1]

theorem coboundary2_div (x y : G → Γ) (p : G × G) :
    coboundary2 (x / y) p = coboundary2 x p / coboundary2 y p := by
  apply Additive.ofMul.injective
  simp only [coboundary2, Pi.div_apply, smul_div', ofMul_mul, ofMul_div]
  abel

theorem coboundary2_mul (x y : G → Γ) (p : G × G) :
    coboundary2 (x * y) p = coboundary2 x p * coboundary2 y p := by
  apply Additive.ofMul.injective
  simp only [coboundary2, Pi.mul_apply, smul_mul', ofMul_mul, ofMul_div]
  abel

theorem coboundary2_one (p : G × G) : coboundary2 (1 : G → Γ) p = 1 := by
  simp [coboundary2]

theorem isMulCocycle₁_coboundary1 (b : Γ) : IsMulCocycle₁ (coboundary1 (G := G) b) := by
  intro g h
  simp only [coboundary1, mul_smul, smul_div']
  exact (div_mul_div_cancel _ _ _).symm

theorem isMulCocycle₂_coboundary2 (x : G → Γ) : IsMulCocycle₂ (coboundary2 x) := by
  intro g h j
  apply Additive.ofMul.injective
  simp only [coboundary2, mul_smul, smul_div', smul_mul', ofMul_mul, ofMul_div, mul_assoc]
  abel

theorem isMulCocycle₁_div {f₁ f₂ : G → Γ} (h₁ : IsMulCocycle₁ f₁) (h₂ : IsMulCocycle₁ f₂) :
    IsMulCocycle₁ (fun g => f₁ g / f₂ g) := by
  intro g h
  simp only [h₁ g h, h₂ g h, smul_div']
  exact mul_div_mul_comm _ _ _ _

theorem isMulCocycle₂_div {f₁ f₂ : G × G → Γ} (h₁ : IsMulCocycle₂ f₁) (h₂ : IsMulCocycle₂ f₂) :
    IsMulCocycle₂ (fun p => f₁ p / f₂ p) := by
  intro g h j
  simp only [smul_div']
  rw [← mul_div_mul_comm, h₁ g h j, h₂ g h j, mul_div_mul_comm]

end Boundaries

/-- The hypotheses on a filtration `V` used below: `G`-stability, separatedness and
completeness (every sequence `b k ∈ V k` has a product `s` with `s / ∏_{i<k} b i ∈ V k`). -/
structure IsCompleteFiltration (G : Type*) {Γ : Type*} [Group G] [CommGroup Γ]
    [MulDistribMulAction G Γ] (V : ℕ → Subgroup Γ) : Prop where
  smul_mem : ∀ k (g : G) x, x ∈ V k → g • x ∈ V k
  eq_one : ∀ x, (∀ k, x ∈ V k) → x = 1
  exists_prod : ∀ b : ℕ → Γ, (∀ k, b k ∈ V k) →
    ∃ s, ∀ k, s / ∏ i ∈ Finset.range k, b i ∈ V k

section Filtration

variable {G Γ : Type*} [Group G] [CommGroup Γ] [MulDistribMulAction G Γ]

variable {V : ℕ → Subgroup Γ}

theorem IsCompleteFiltration.coboundary1_mem (hV : IsCompleteFiltration G V) {k : ℕ} {b : Γ}
    (hb : b ∈ V k) (g : G) : coboundary1 b g ∈ V k :=
  (V k).div_mem (hV.smul_mem k g b hb) hb

theorem IsCompleteFiltration.coboundary2_mem (hV : IsCompleteFiltration G V) {k : ℕ} {x : G → Γ}
    (hx : ∀ g, x g ∈ V k) (p : G × G) : coboundary2 x p ∈ V k :=
  (V k).mul_mem ((V k).div_mem (hV.smul_mem k p.1 _ (hx p.2)) (hx _)) (hx p.1)

theorem coboundary1_prod (c : ℕ → Γ) (k : ℕ) (g : G) :
    coboundary1 (∏ i ∈ Finset.range k, c i) g = ∏ i ∈ Finset.range k, coboundary1 (c i) g := by
  induction k with
  | zero => simp [coboundary1_one]
  | succ k ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, coboundary1_mul, ih]

/-- Approximation by coboundaries at each level of a complete filtration kills `H¹`. -/
theorem exists_coboundary1_eq (hV : IsCompleteFiltration G V)
    (happrox : ∀ k (f : G → Γ), IsMulCocycle₁ f → (∀ g, f g ∈ V k) →
      ∃ b ∈ V k, ∀ g, f g / coboundary1 b g ∈ V (k + 1))
    (f : G → Γ) (hf : IsMulCocycle₁ f) (hf0 : ∀ g, f g ∈ V 0) :
    ∃ s ∈ V 0, ∀ g, coboundary1 s g = f g := by
  choose! b hbV hb using happrox
  let F : ℕ → G → Γ := fun k =>
    Nat.rec (motive := fun _ => G → Γ) f (fun k fk => fun g => fk g / coboundary1 (b k fk) g) k
  have hF_succ : ∀ k, F (k + 1) = fun g => F k g / coboundary1 (b k (F k)) g := fun _ => rfl
  have hF_succ' : ∀ k g, F (k + 1) g = F k g / coboundary1 (b k (F k)) g := fun _ _ => rfl
  have hP : ∀ k, IsMulCocycle₁ (F k) ∧ ∀ g, F k g ∈ V k := by
    intro k
    induction k with
    | zero => exact ⟨hf, hf0⟩
    | succ k ih =>
      rw [hF_succ]
      exact ⟨isMulCocycle₁_div ih.1 (isMulCocycle₁_coboundary1 _), hb k (F k) ih.1 ih.2⟩
  let c : ℕ → Γ := fun k => b k (F k)
  have hc : ∀ k, c k ∈ V k := fun k => hbV k (F k) (hP k).1 (hP k).2
  have hFc : ∀ k g, F k g = f g / coboundary1 (∏ i ∈ Finset.range k, c i) g := by
    intro k
    induction k with
    | zero => intro g; simp [F, coboundary1_one]
    | succ k ih =>
      intro g
      rw [hF_succ' k g, ih g, Finset.prod_range_succ, coboundary1_mul, div_div]
  obtain ⟨s, hs⟩ := hV.exists_prod c hc
  refine ⟨s, by simpa using hs 0, fun g => ?_⟩
  have key : ∀ k, f g / coboundary1 s g ∈ V k := by
    intro k
    have h1 := (hP k).2 g
    have h2 := hV.coboundary1_mem (hs k) g
    have := (V k).div_mem h1 h2
    rwa [hFc, coboundary1_div, div_div_div_cancel_right] at this
  exact (div_eq_one.1 (hV.eq_one _ key)).symm

/-- Approximation by coboundaries at each level of a complete filtration kills `H²`. -/
theorem exists_coboundary2_eq (hV : IsCompleteFiltration G V)
    (happrox : ∀ k (f : G × G → Γ), IsMulCocycle₂ f → (∀ p, f p ∈ V k) →
      ∃ x : G → Γ, (∀ g, x g ∈ V k) ∧ ∀ p, f p / coboundary2 x p ∈ V (k + 1))
    (f : G × G → Γ) (hf : IsMulCocycle₂ f) (hf0 : ∀ p, f p ∈ V 0) :
    ∃ s : G → Γ, (∀ g, s g ∈ V 0) ∧ ∀ p, coboundary2 s p = f p := by
  choose! x hxV hx using happrox
  let F : ℕ → G × G → Γ := fun k =>
    Nat.rec (motive := fun _ => G × G → Γ) f
      (fun k fk => fun p => fk p / coboundary2 (x k fk) p) k
  have hF_succ : ∀ k, F (k + 1) = fun p => F k p / coboundary2 (x k (F k)) p := fun _ => rfl
  have hF_succ' : ∀ k p, F (k + 1) p = F k p / coboundary2 (x k (F k)) p := fun _ _ => rfl
  have hP : ∀ k, IsMulCocycle₂ (F k) ∧ ∀ p, F k p ∈ V k := by
    intro k
    induction k with
    | zero => exact ⟨hf, hf0⟩
    | succ k ih =>
      rw [hF_succ]
      exact ⟨isMulCocycle₂_div ih.1 (isMulCocycle₂_coboundary2 _), hx k (F k) ih.1 ih.2⟩
  let c : ℕ → G → Γ := fun k => x k (F k)
  have hc : ∀ k g, c k g ∈ V k := fun k => hxV k (F k) (hP k).1 (hP k).2
  have hprod : ∀ k : ℕ, ∀ g, (∏ i ∈ Finset.range k, c i) g = ∏ i ∈ Finset.range k, c i g :=
    fun k g => Finset.prod_apply g _ _
  have hFc : ∀ k p, F k p = f p / coboundary2 (∏ i ∈ Finset.range k, c i) p := by
    intro k
    induction k with
    | zero => intro p; simp [F, coboundary2_one]
    | succ k ih =>
      intro p
      rw [hF_succ' k p, ih p, Finset.prod_range_succ, coboundary2_mul, div_div]
  choose s hs using fun g => hV.exists_prod (fun i => c i g) (fun i => hc i g)
  refine ⟨s, fun g => by simpa using hs g 0, fun p => ?_⟩
  have key : ∀ k, f p / coboundary2 s p ∈ V k := by
    intro k
    have h1 := (hP k).2 p
    have h2 := hV.coboundary2_mem (x := s / ∏ i ∈ Finset.range k, c i)
      (fun g => by rw [Pi.div_apply, hprod]; exact hs g k) p
    have := (V k).div_mem h1 h2
    rwa [hFc, coboundary2_div, div_div_div_cancel_right] at this
  exact (div_eq_one.1 (hV.eq_one _ key)).symm

end Filtration

section Coinduced

variable {G : Type*} [Group G] {Y : Type*} [AddCommGroup Y]

/-- Coinduced modules modulo a subgroup: a `1`-cocycle `a` for the action
`(g • φ) ρ = φ (g⁻¹ * ρ)`, valid modulo `Y'`, is a coboundary modulo `Y'`. If `a` takes values
in a subgroup `Y''`, the cochain can be chosen with values in `Y''`. -/
theorem coinduced_approx₁ (Y' Y'' : AddSubgroup Y) (a : G → G → Y)
    (ha : ∀ g h ρ, a (g * h) ρ - a h (g⁻¹ * ρ) - a g ρ ∈ Y') (ha'' : ∀ g ρ, a g ρ ∈ Y'') :
    ∃ x : G → Y, (∀ ρ, x ρ ∈ Y'') ∧ ∀ g ρ, a g ρ - (x (g⁻¹ * ρ) - x ρ) ∈ Y' := by
  refine ⟨fun ρ => -a ρ ρ, fun ρ => Y''.neg_mem (ha'' ρ ρ), fun g ρ => ?_⟩
  show a g ρ - (-a (g⁻¹ * ρ) (g⁻¹ * ρ) - -a ρ ρ) ∈ Y'
  have h := ha g (g⁻¹ * ρ) ρ
  rw [mul_inv_cancel_left] at h
  have := Y'.neg_mem h
  convert this using 1
  abel

/-- Coinduced modules modulo a subgroup: a `2`-cocycle `a` for the action
`(g • φ) ρ = φ (g⁻¹ * ρ)`, valid modulo `Y'`, is a coboundary modulo `Y'`. If `a` takes values
in a subgroup `Y''`, the cochain can be chosen with values in `Y''`. -/
theorem coinduced_approx₂ (Y' Y'' : AddSubgroup Y) (a : G × G → G → Y)
    (ha : ∀ g h j ρ, a (g * h, j) ρ + a (g, h) ρ - a (h, j) (g⁻¹ * ρ) - a (g, h * j) ρ ∈ Y')
    (ha'' : ∀ p ρ, a p ρ ∈ Y'') :
    ∃ x : G → G → Y, (∀ g ρ, x g ρ ∈ Y'') ∧
      ∀ g h ρ, x h (g⁻¹ * ρ) - x (g * h) ρ + x g ρ - a (g, h) ρ ∈ Y' := by
  refine ⟨fun g ρ => a (g, g⁻¹ * ρ) ρ, fun g ρ => ha'' _ _, fun g h ρ => ?_⟩
  show a (h, h⁻¹ * (g⁻¹ * ρ)) (g⁻¹ * ρ) - a (g * h, (g * h)⁻¹ * ρ) ρ + a (g, g⁻¹ * ρ) ρ -
    a (g, h) ρ ∈ Y'
  have h' := ha g h (h⁻¹ * (g⁻¹ * ρ)) ρ
  rw [mul_inv_cancel_left] at h'
  have e : (g * h)⁻¹ * ρ = h⁻¹ * (g⁻¹ * ρ) := by rw [mul_inv_rev, mul_assoc]
  have := Y'.neg_mem h'
  rw [e]
  convert this using 1
  abel

end Coinduced

end Langlands.Cohomology.CompleteFiltration
