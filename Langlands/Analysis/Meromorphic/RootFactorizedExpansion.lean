import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Analysis.Meromorphic.RootFactorization

/-! # Finite meromorphic expansions with root factorizations

Families `μ ↦ Op μ` of functions on a set `Gp`, parametrized by a finite-dimensional complex
vector space, that agree on a region `Reg R₀` of parameters with finite sums
`∑ i, coeff i μ * χ i` with meromorphic coefficients. The module proves the algebra used to
compose such expansions along a chain of operators:

* a finite family of functions contains a linearly independent subfamily spanning it, and
  coefficients along a linearly independent family are unique;
* finitely many expansions can be merged into one expansion with a common family and a common
  domain of holomorphy;
* `HasRootFactorizedExpansion.step`: if `Op₀` has an expansion whose coefficients have root
  factorizations, the operators `S μ` have expansions and are invariant under translation of
  `μ` by the kernel of a linear form `α`, and a composition rule relates the expansions of
  `Op₀`, `S` and `Op₁`, then `Op₁` has an expansion whose coefficients have root
  factorizations;
* `exists_rootFactorization_of_combination`: a combination of finitely many such expansions with
  entire coefficients, after a linear change of parameters, has a single expansion with root
  factorizations of common length. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set

section Basis

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A finite family of vectors contains a linearly independent subfamily that spans it. -/
theorem exists_fin_linearIndependent_subfamily {K : ℕ} (f : Fin K → V) :
    ∃ (k : ℕ) (σ : Fin k → Fin K), LinearIndependent ℂ (f ∘ σ) ∧
      ∀ i, ∃ A : Fin k → ℂ, f i = ∑ s, A s • f (σ s) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ f
  have : Finite κ := Finite.of_injective a ha
  let e : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  refine ⟨Nat.card κ, a ∘ e.symm, hli.comp e.symm e.symm.injective, fun i => ?_⟩
  have hr : range (f ∘ (a ∘ e.symm)) = range (f ∘ a) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e.symm s, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, by simp⟩
  have hmem : f i ∈ Submodule.span ℂ (range (f ∘ (a ∘ e.symm))) := by
    rw [hr, hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  exact ⟨A, hA.symm⟩

end Basis

variable {Gp : Type*}

/-- Coefficients of a function along a linearly independent finite family of scalar functions
are unique. -/
theorem coeff_eq_of_linearIndependent {k : ℕ} {e : Fin k → Gp → ℂ}
    (he : LinearIndependent ℂ e) {x y : Fin k → ℂ}
    (h : ∀ g, ∑ s, x s * e s g = ∑ s, y s * e s g) : x = y := by
  have h0 : ∑ s, (x s - y s) • e s = 0 := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      h g, sub_self, Pi.zero_apply]
  funext s
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 he _ h0 s)

/-- Re-expansion of a finite combination along a family in terms of which every member is
expanded. -/
theorem sum_mul_eq_sum_of_expansion {K k : ℕ} (f : Fin K → Gp → ℂ) (e : Fin k → Gp → ℂ)
    (A : Fin K → Fin k → ℂ) (hA : ∀ j, f j = ∑ s, A j s • e s) (x : Fin K → ℂ) (g : Gp) :
    ∑ j, x j * f j g = ∑ s, (∑ j, x j * A j s) * e s g := by
  have hfg : ∀ j, f j g = ∑ s, A j s * e s g := fun j => by
    conv_lhs => rw [hA j]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, x j * f j g = ∑ j, ∑ s, x j * A j s * e s g := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hfg j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ s, (∑ j, x j * A j s) * e s g := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem IsOpenDenseInCoordinates.preimage_linearEquiv {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {D : Set Y} (hD : IsOpenDenseInCoordinates D) (e : X ≃ₗ[ℂ] Y) :
    IsOpenDenseInCoordinates (e ⁻¹' D) := fun n e₀ =>
  hD n (e₀.trans e)

theorem IsMeromorphicInCoordinatesOn.mul_const' {f : X → ℂ} {D : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) (hD : IsOpenDenseInCoordinates D) (c : ℂ) :
    IsMeromorphicInCoordinatesOn (fun x => f x * c) D := by
  let : FiniteDimensional ℂ X := hf.1
  exact (hf.mul (isMeromorphicInCoordinatesOn_const c)).congr_mono hD
    (fun x hx => ⟨hx, mem_univ x⟩) fun _ _ => rfl

theorem isMeromorphicInCoordinatesOn_sum' [FiniteDimensional ℂ X] {κ : Type*} (s : Finset κ)
    {h : κ → X → ℂ} {D : Set X} (hD : IsOpenDenseInCoordinates D)
    (hh : ∀ i ∈ s, IsMeromorphicInCoordinatesOn (h i) D) :
    IsMeromorphicInCoordinatesOn (fun x => ∑ i ∈ s, h i x) D := by
  have := IsMeromorphicInCoordinatesOn.sum s hD hh
  convert this using 1
  funext x
  simp only [Finset.sum_apply]

theorem IsMeromorphicInCoordinatesOn.mono' {f : X → ℂ} {D D' : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) (hD' : IsOpenDenseInCoordinates D')
    (hsub : D' ⊆ D) : IsMeromorphicInCoordinatesOn f D' :=
  hf.congr_mono hD' hsub fun _ _ => rfl

/-! ### Expansions -/

/-- `Op` has a finite meromorphic expansion on the region `Reg`: there are finitely many
functions `χ i` satisfying `Aut` and coefficients meromorphic in linear coordinates with one
domain `D` such that `Op μ = ∑ i, coeff i μ • χ i` whenever `Reg R₀ μ`, for some `R₀`. -/
def HasMeromorphicExpansion (Reg : ℝ → X → Prop) (Aut : (Gp → ℂ) → Prop) (Op : X → Gp → ℂ) :
    Prop :=
  ∃ (k : ℕ) (χ : Fin k → Gp → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
    (∀ i, Aut (χ i)) ∧ (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
    ∃ R₀ : ℝ, ∀ μ, Reg R₀ μ → ∀ g, Op μ g = ∑ i, coeff i μ * χ i g

variable {ι : Type*}

/-- `Op` has a finite meromorphic expansion whose coefficients have root factorizations on
their common domain of holomorphy, which is open and dense in coordinates. -/
def HasRootFactorizedExpansion (L : ι → X →ₗ[ℂ] ℂ) (R : Set ι) (Reg : ℝ → X → Prop)
    (Aut : (Gp → ℂ) → Prop) (Op : X → Gp → ℂ) : Prop :=
  ∃ (k : ℕ) (χ : Fin k → Gp → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
    IsOpenDenseInCoordinates D ∧ (∀ i, Aut (χ i)) ∧
    (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
    (∃ R₀ : ℝ, ∀ μ, Reg R₀ μ → ∀ g, Op μ g = ∑ i, coeff i μ * χ i g) ∧
    ∀ i, HasRootFactorizationOn L R D (coeff i)

variable {Reg : ℝ → X → Prop} {Aut : (Gp → ℂ) → Prop} {Op : X → Gp → ℂ}

/-- The domain of holomorphy of an expansion can be taken open and dense in coordinates. -/
theorem HasMeromorphicExpansion.exists_openDense (h : HasMeromorphicExpansion Reg Aut Op) :
    ∃ (k : ℕ) (χ : Fin k → Gp → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
      IsOpenDenseInCoordinates D ∧ (∀ i, Aut (χ i)) ∧
      (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
      ∃ R₀ : ℝ, ∀ μ, Reg R₀ μ → ∀ g, Op μ g = ∑ i, coeff i μ * χ i g := by
  obtain ⟨k, χ, coeff, D, hχ, hm, hag⟩ := h
  cases k with
  | zero => exact ⟨0, χ, coeff, univ, Langlands.Global.isOpenDenseInCoordinates_univ, hχ, fun i => i.elim0, hag⟩
  | succ k => exact ⟨k + 1, χ, coeff, D, (hm 0).isOpenDenseInCoordinates, hχ, hm, hag⟩

/-- A family constant in the parameter has a root factorized expansion with one term. -/
theorem hasRootFactorizedExpansion_of_eq [FiniteDimensional ℂ X] {L : ι → X →ₗ[ℂ] ℂ}
    {R : Set ι} {ψ : Gp → ℂ} (hψ : Aut ψ) (hOp : ∀ μ g, Op μ g = ψ g) :
    HasRootFactorizedExpansion L R Reg Aut Op :=
  ⟨1, fun _ => ψ, fun _ _ => 1, univ, Langlands.Global.isOpenDenseInCoordinates_univ, fun _ => hψ,
    fun _ => isMeromorphicInCoordinatesOn_const 1, ⟨0, fun μ _ g => by simp [hOp]⟩,
    fun _ => HasRootFactorizationOn.of_isRootFactorOn (isRootFactorOn_const 1)⟩

/-- Finitely many expansions merge into expansions along one family with one domain. -/
theorem exists_merged_expansion [FiniteDimensional ℂ X] {k : ℕ} {S : Fin k → X → Gp → ℂ}
    (h : ∀ i, HasMeromorphicExpansion Reg Aut (S i)) :
    ∃ (k' : ℕ) (ξ : Fin k' → Gp → ℂ) (b : Fin k → Fin k' → X → ℂ) (D : Set X),
      IsOpenDenseInCoordinates D ∧ (∀ j, Aut (ξ j)) ∧
      (∀ i j, IsMeromorphicInCoordinatesOn (b i j) D) ∧
      ∀ i, ∃ R₀ : ℝ, ∀ μ, Reg R₀ μ → ∀ g, S i μ g = ∑ j, b i j μ * ξ j g := by
  classical
  choose kk ξξ bb DD hDD hξξ hbb hag using fun i => (h i).exists_openDense
  let e := finSigmaFinEquiv (m := k) (n := kk)
  let ξ : Fin (∑ i, kk i) → Gp → ℂ := fun j => ξξ (e.symm j).1 (e.symm j).2
  let b : Fin k → Fin (∑ i, kk i) → X → ℂ := fun i j =>
    if (e.symm j).1 = i then bb (e.symm j).1 (e.symm j).2 else fun _ => 0
  have hD : IsOpenDenseInCoordinates (⋂ i, DD i) := isOpenDenseInCoordinates_iInter hDD
  refine ⟨∑ i, kk i, ξ, b, ⋂ i, DD i, hD, fun j => hξξ _ _, fun i j => ?_, fun i => ?_⟩
  · simp only [b]
    split_ifs
    · exact (hbb _ _).mono' hD (iInter_subset _ _)
    · exact (isMeromorphicInCoordinatesOn_const (0 : ℂ)).mono' hD (subset_univ _)
  · obtain ⟨R₀, hR₀⟩ := hag i
    refine ⟨R₀, fun μ hμ g => ?_⟩
    rw [hR₀ μ hμ g, Fintype.sum_equiv e.symm (fun j => b i j μ * ξ j g)
      (fun p => (if p.1 = i then bb p.1 p.2 else fun _ => 0) μ * ξξ p.1 p.2 g) (fun j => rfl),
      Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'
      simp [hi']
    · simp


/-! ### Composition along one step -/

section Step

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- **Composition step.** Let `Op₀` have an expansion on the region `RegX` whose coefficients
have root factorizations for the forms `L β`, `β ∈ R`. Let the operators `S μ`, `μ ∈ Y`, have
expansions on the region `RegY` on every function satisfying `Aut₁`, and be invariant there
under translation of `μ` by the kernel of a linear form `α` whose pull-back along `We` vanishes
on the kernel of some `L β`. Let `Op₁` have an expansion, and let every choice of expansions of
`Op₀`, of the `S μ` on the family of `Op₀` and of `Op₁` satisfy the composition rule
`Op₁ x = ∑ i, a i x • S (We x) (χ i)` on the common domains. Then `Op₁` has an expansion whose
coefficients have root factorizations. -/
theorem HasRootFactorizedExpansion.step [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {RegX : ℝ → X → Prop} {RegY : ℝ → Y → Prop}
    {Aut₁ Aut₂ : (Gp → ℂ) → Prop} {Op₀ Op₁ : X → Gp → ℂ} {S : Y → (Gp → ℂ) → Gp → ℂ}
    (We : X ≃ₗ[ℂ] Y) (α : Y →ₗ[ℂ] ℂ)
    (hRegY : ∀ {R₁ R₂ : ℝ} {μ : Y}, R₁ ≤ R₂ → RegY R₂ μ → RegY R₁ μ)
    (hregY : ∀ (R₀ : ℝ) (ν : Y), ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] Y) (O : Set (Fin n → ℂ)),
      IsOpen O ∧ O.Nonempty ∧ ∀ s ∈ O, RegY R₀ (e s) ∧ RegY R₀ (e s + ν))
    (htrans : ∃ β ∈ R, ∀ ν, L β ν = 0 → α (We ν) = 0)
    (h₀ : HasRootFactorizedExpansion L R RegX Aut₁ Op₀)
    (hS : ∀ ψ, Aut₁ ψ → HasMeromorphicExpansion RegY Aut₂ (fun μ => S μ ψ))
    (hinv : ∀ ψ, Aut₁ ψ → ∃ R₀ : ℝ, ∀ μ ν, RegY R₀ μ → RegY R₀ (μ + ν) → α ν = 0 →
      ∀ g, S (μ + ν) ψ g = S μ ψ g)
    (h₁ : HasMeromorphicExpansion RegX Aut₂ Op₁)
    (hcoc : ∀ (k : ℕ) (χ : Fin k → Gp → ℂ) (a : Fin k → X → ℂ) (D : Set X),
      (∀ i, Aut₁ (χ i)) → (∀ i, IsMeromorphicInCoordinatesOn (a i) D) →
      (∃ R₀ : ℝ, ∀ μ, RegX R₀ μ → ∀ g, Op₀ μ g = ∑ i, a i μ * χ i g) →
      ∀ (k' : ℕ) (ξ : Fin k' → Gp → ℂ) (b : Fin k → Fin k' → Y → ℂ) (D' : Set Y),
      (∀ i j, IsMeromorphicInCoordinatesOn (b i j) D') →
      (∀ i, ∃ R₀ : ℝ, ∀ μ, RegY R₀ μ → ∀ g, S μ (χ i) g = ∑ j, b i j μ * ξ j g) →
      ∀ (k'' : ℕ) (ζ : Fin k'' → Gp → ℂ) (c : Fin k'' → X → ℂ) (D'' : Set X),
      (∀ j, IsMeromorphicInCoordinatesOn (c j) D'') →
      (∃ R₀ : ℝ, ∀ μ, RegX R₀ μ → ∀ g, Op₁ μ g = ∑ j, c j μ * ζ j g) →
      ∀ x ∈ D ∩ D'', We x ∈ D' → ∀ g,
        ∑ j, c j x * ζ j g = ∑ i, a i x * ∑ j, b i j (We x) * ξ j g) :
    HasRootFactorizedExpansion L R RegX Aut₂ Op₁ := by
  classical
  obtain ⟨k, χ, a, D, hD, hχ, ha, hag₀, hfac₀⟩ := h₀
  -- expansions of the step operators on the family `χ`, merged into one family
  obtain ⟨k', ξ, b, D', hD', hξ, hb, hagS⟩ :=
    exists_merged_expansion (S := fun i μ => S μ (χ i)) fun i => hS (χ i) (hχ i)
  -- a linearly independent subfamily of `ξ`
  obtain ⟨k₁, σ, hli₁, hA₁⟩ := exists_fin_linearIndependent_subfamily ξ
  choose A₁ hA₁ using hA₁
  let b₁ : Fin k → Fin k₁ → Y → ℂ := fun i s μ => ∑ j, b i j μ * A₁ j s
  have hb₁ : ∀ i s, IsMeromorphicInCoordinatesOn (b₁ i s) D' := fun i s =>
    isMeromorphicInCoordinatesOn_sum' Finset.univ hD' fun j _ => (hb i j).mul_const' hD' _
  have hagS₁ : ∀ i, ∃ R₀ : ℝ, ∀ μ, RegY R₀ μ → ∀ g,
      S μ (χ i) g = ∑ s, b₁ i s μ * (ξ ∘ σ) s g := fun i => by
    obtain ⟨R₀, hR₀⟩ := hagS i
    exact ⟨R₀, fun μ hμ g => by
      rw [hR₀ μ hμ g, sum_mul_eq_sum_of_expansion ξ (ξ ∘ σ) A₁ hA₁ (fun j => b i j μ) g]⟩
  -- the new coefficients are invariant under the kernel of `α`
  have hinv₁ : ∀ i s, ∀ x ∈ D', ∀ ν : Y, α ν = 0 → x + ν ∈ D' →
      b₁ i s (x + ν) = b₁ i s x := by
    intro i s x hx ν hν hxν
    obtain ⟨R₁, hR₁⟩ := hagS₁ i
    obtain ⟨R₂, hR₂⟩ := hinv (χ i) (hχ i)
    obtain ⟨n, e, O, hO, hne, hreg⟩ := hregY (max R₁ R₂) ν
    refine (hb₁ i s).translate_invariant_of_open ν e hO hne (fun t ht _ _ => ?_) x hx hxν
    have h1 := hreg t ht
    have hcoef : (fun s => b₁ i s (e t + ν)) = fun s => b₁ i s (e t) := by
      refine coeff_eq_of_linearIndependent hli₁ fun g => ?_
      rw [← hR₁ _ (hRegY (le_max_left _ _) h1.2) g, ← hR₁ _ (hRegY (le_max_left _ _) h1.1) g]
      exact hR₂ _ _ (hRegY (le_max_right _ _) h1.1) (hRegY (le_max_right _ _) h1.2) hν g
    exact congrFun hcoef s
  have hroot₁ : ∀ i s, IsRootFactorOn L R (We ⁻¹' D') (b₁ i s ∘ We) := by
    intro i s
    have hf : IsRootFactorOn (fun _ : Unit => α) univ D' (b₁ i s) :=
      Or.inr ⟨hb₁ i s, (), mem_univ _, hinv₁ i s⟩
    refine hf.comp_linearEquiv We fun _ _ => ?_
    obtain ⟨β, hβ, hker⟩ := htrans
    exact ⟨β, hβ, hker⟩
  -- the composite operator and the composition rule
  obtain ⟨k'', ζ, c, D'', hD'', hζ, hc, hag₁⟩ := h₁.exists_openDense
  have hrel := hcoc k χ a D hχ ha hag₀ k₁ (ξ ∘ σ) b₁ D' hb₁ hagS₁ k'' ζ c D'' hc hag₁
  -- a linearly independent subfamily of `ζ` followed by `ξ ∘ σ`
  let Φ : Fin (k'' + k₁) → Gp → ℂ := Fin.append ζ (ξ ∘ σ)
  obtain ⟨k₂, τ, hli₂, hA₂⟩ := exists_fin_linearIndependent_subfamily Φ
  choose A₂ hA₂ using hA₂
  have hζ₂ : ∀ j, ζ j = ∑ v, A₂ (Fin.castAdd k₁ j) v • (Φ ∘ τ) v := fun j =>
    calc ζ j = Φ (Fin.castAdd k₁ j) := by simp [Φ]
      _ = _ := hA₂ _
  have hξ₂ : ∀ s, (ξ ∘ σ) s = ∑ v, A₂ (Fin.natAdd k'' s) v • (Φ ∘ τ) v := fun s =>
    calc (ξ ∘ σ) s = Φ (Fin.natAdd k'' s) := by simp [Φ]
      _ = _ := hA₂ _
  let c₂ : Fin k₂ → X → ℂ := fun v x => ∑ j, c j x * A₂ (Fin.castAdd k₁ j) v
  let Dn : Set X := D ∩ D'' ∩ We ⁻¹' D'
  have hDn : IsOpenDenseInCoordinates Dn :=
    (hD.inter hD'').inter (hD'.preimage_linearEquiv We)
  have hDnD : Dn ⊆ D := fun x hx => hx.1.1
  have hDnD'' : Dn ⊆ D'' := fun x hx => hx.1.2
  have hDnD' : Dn ⊆ We ⁻¹' D' := fun x hx => hx.2
  have hexp₁ : ∀ x g, ∑ j, c j x * ζ j g = ∑ v, c₂ v x * (Φ ∘ τ) v g := fun x g =>
    sum_mul_eq_sum_of_expansion ζ (Φ ∘ τ) (fun j v => A₂ (Fin.castAdd k₁ j) v) hζ₂
      (fun j => c j x) g
  refine ⟨k₂, Φ ∘ τ, c₂, Dn, hDn, fun v => ?_, fun v => ?_, ?_, fun v => ?_⟩
  · simp only [Function.comp_apply, Φ]
    refine Fin.addCases (fun j => ?_) (fun s => ?_) (τ v)
    · simpa [Fin.append_left] using hζ j
    · simpa [Fin.append_right] using hξ (σ s)
  · exact (isMeromorphicInCoordinatesOn_sum' Finset.univ hD'' fun j _ =>
      (hc j).mul_const' hD'' _).mono' hDn hDnD''
  · obtain ⟨R₀, hR₀⟩ := hag₁
    exact ⟨R₀, fun μ hμ g => by rw [hR₀ μ hμ g, hexp₁]⟩
  · -- coefficient comparison on the common domain
    have key : ∀ x ∈ Dn, c₂ v x =
        ∑ i, ∑ s, a i x * ((b₁ i s ∘ We) x * A₂ (Fin.natAdd k'' s) v) := by
      intro x hx
      have hfun : (fun v => c₂ v x) =
          fun v => ∑ i, ∑ s, a i x * ((b₁ i s ∘ We) x * A₂ (Fin.natAdd k'' s) v) := by
        refine coeff_eq_of_linearIndependent hli₂ fun g => ?_
        rw [← hexp₁, hrel x ⟨hx.1.1, hx.1.2⟩ hx.2 g]
        calc ∑ i, a i x * ∑ s, b₁ i s (We x) * (ξ ∘ σ) s g
            = ∑ i, a i x * ∑ v, (∑ s, b₁ i s (We x) * A₂ (Fin.natAdd k'' s) v) *
                (Φ ∘ τ) v g := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [sum_mul_eq_sum_of_expansion (ξ ∘ σ) (Φ ∘ τ)
                (fun s v => A₂ (Fin.natAdd k'' s) v) hξ₂ (fun s => b₁ i s (We x)) g]
          _ = ∑ v, (∑ i, ∑ s, a i x * ((b₁ i s ∘ We) x * A₂ (Fin.natAdd k'' s) v)) *
                (Φ ∘ τ) v g := by
              simp only [Finset.mul_sum, Finset.sum_mul, Function.comp_apply]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun s _ => ?_
              ring
      exact congrFun hfun v
    have hF : HasRootFactorizationOn L R Dn
        (fun x => ∑ i, ∑ s, a i x * ((b₁ i s ∘ We) x * A₂ (Fin.natAdd k'' s) v)) :=
      HasRootFactorizationOn.sum Finset.univ fun i _ =>
        HasRootFactorizationOn.sum Finset.univ fun s _ =>
          ((hfac₀ i).mono hDn hDnD).mul
            ((HasRootFactorizationOn.of_isRootFactorOn ((hroot₁ i s).mono hDn hDnD')).mul
              (HasRootFactorizationOn.of_isRootFactorOn (isRootFactorOn_const _)))
    exact hF.congr key

end Step

/-! ### Combination and common lengths -/

section Combination

variable {X₀ : Type*} [AddCommGroup X₀] [Module ℂ X₀]

/-- **Final assembly.** A family `T` that on a region of parameters is a finite combination
`T λ g = ∑ j, E j λ * h j g * Op j (iota λ) (τ j g)` with coefficients `E j` entire in linear
coordinates, a linear isomorphism `iota` of parameter spaces compatible with the regions and
carrying the kernels of the forms `L β` into kernels of the forms `L₀ β₀`, and families `Op j`
with root factorized expansions, has a finite meromorphic expansion whose coefficients agree on
one domain with sums of products of root factors with common numbers of summands and
factors. -/
theorem exists_rootFactorization_of_combination [FiniteDimensional ℂ X]
    {L : ι → X →ₗ[ℂ] ℂ} {R : Set ι} {κ : Type*} {L₀ : κ → X₀ →ₗ[ℂ] ℂ} {R₀ : Set κ}
    {RegX : ℝ → X → Prop} {Reg₀ : ℝ → X₀ → Prop} {Aut : (Gp → ℂ) → Prop}
    (hRegX : ∀ {R₁ R₂ : ℝ} {lam : X}, R₁ ≤ R₂ → RegX R₂ lam → RegX R₁ lam)
    (iota : X ≃ₗ[ℂ] X₀)
    (hreg : ∀ R' : ℝ, ∃ R'' : ℝ, ∀ lam, RegX R'' lam → Reg₀ R' (iota lam))
    (htrans : ∀ β₀ ∈ R₀, ∃ β ∈ R, ∀ ν, L β ν = 0 → L₀ β₀ (iota ν) = 0)
    {m : ℕ} (E : Fin m → X → ℂ) (hE : ∀ j, IsEntireInCoordinates (E j))
    (h : Fin m → Gp → ℂ) (τ : Fin m → Gp → Gp) (Op : Fin m → X₀ → Gp → ℂ)
    (hOp : ∀ j, HasRootFactorizedExpansion L₀ R₀ Reg₀ Aut (Op j))
    (T : X → Gp → ℂ)
    (hT : ∃ R' : ℝ, ∀ lam, RegX R' lam → ∀ g,
      T lam g = ∑ j, E j lam * h j g * Op j (iota lam) (τ j g)) :
    ∃ (k : ℕ) (ψ : Fin k → Gp → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
      (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
      (∃ R' : ℝ, ∀ lam, RegX R' lam → ∀ g, T lam g = ∑ i, coeff i lam * ψ i g) ∧
      ∃ (J n : ℕ) (fac : Fin k → Fin J → Fin n → X → ℂ),
        (∀ i j t, IsRootFactorOn L R D (fac i j t)) ∧
        ∀ i, ∀ x ∈ D, coeff i x = ∑ j, ∏ t, fac i j t x := by
  classical
  choose kk χχ aa DD hDD hχχ haa hagg hfacc using hOp
  choose Rj hRj using hagg
  choose R'' hR'' using fun j => hreg (Rj j)
  obtain ⟨RT, hRT⟩ := hT
  let Rf : ℝ := max RT (∑ j, |R'' j|)
  have hRfT : RT ≤ Rf := le_max_left _ _
  have hRfj : ∀ j, R'' j ≤ Rf := fun j =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R'' j))
      (Finset.mem_univ j)).trans (le_max_right _ _))
  let e := finSigmaFinEquiv (m := m) (n := kk)
  let ψ : Fin (∑ j, kk j) → Gp → ℂ := fun i g =>
    h (e.symm i).1 g * χχ (e.symm i).1 (e.symm i).2 (τ (e.symm i).1 g)
  let coeff : Fin (∑ j, kk j) → X → ℂ := fun i x =>
    E (e.symm i).1 x * aa (e.symm i).1 (e.symm i).2 (iota x)
  let D : Set X := ⋂ j, iota ⁻¹' DD j
  have hD : IsOpenDenseInCoordinates D :=
    isOpenDenseInCoordinates_iInter fun j => (hDD j).preimage_linearEquiv iota
  have hDj : ∀ j, D ⊆ iota ⁻¹' DD j := fun j => iInter_subset _ j
  have hcoeff : ∀ i, HasRootFactorizationOn L R D (coeff i) := fun i =>
    (HasRootFactorizationOn.of_isRootFactorOn (hE _).isRootFactorOn).mul
      (((hfacc _ _).comp_linearEquiv iota htrans).mono hD (hDj _))
  obtain ⟨J, n, fac, hfac, heq⟩ := exists_uniform_rootFactorization hcoeff
  refine ⟨∑ j, kk j, ψ, coeff, D, fun i => ?_, ⟨Rf, fun lam hlam g => ?_⟩, J, n, fac, hfac, heq⟩
  · exact (((hE _).isMeromorphicInCoordinatesOn hD).mul
      ((haa _ _).comp_linearEquiv iota)).mono' hD fun x hx => ⟨hx, hDj _ hx⟩
  · rw [hRT lam (hRegX hRfT hlam) g]
    rw [Fintype.sum_equiv e.symm (fun i => coeff i lam * ψ i g)
      (fun p => (E p.1 lam * aa p.1 p.2 (iota lam)) * (h p.1 g * χχ p.1 p.2 (τ p.1 g)))
      (fun i => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hRj j (iota lam) (hR'' j lam (hRegX (hRfj j) hlam)) (τ j g), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Combination

end Langlands.Analysis.Meromorphic
