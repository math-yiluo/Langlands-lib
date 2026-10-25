import Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement

/-! Algebraic restriction and descent for trilinear uniqueness. -/

noncomputable section

namespace Langlands.RankinSelberg.TrilinearReduction

universe uG uV uW uS uV' uW'

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW} {S : Type uS}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup S] [Module ℂ S]

abbrev Form := V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] ℂ

/-- Restriction in the third variable to a specified submodule. -/
def restrict (K : Submodule ℂ S) :
    Form (V := V) (W := W) (S := S) →ₗ[ℂ]
      Form (V := V) (W := W) (S := K) where
  toFun B :=
    { toFun := fun v =>
        { toFun := fun w => (B v w).comp K.subtype
          map_add' := by intros; ext; simp
          map_smul' := by intros; ext; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

@[simp] theorem restrict_apply (K : Submodule ℂ S)
    (B : Form (V := V) (W := W) (S := S)) (v : V) (w : W) (φ : K) :
    restrict K B v w φ = B v w φ := rfl

/-- Evaluation in the test-function variable produces an actual bilinear map. -/
def evaluate (φ : S) (B : Form (V := V) (W := W) (S := S)) : V →ₗ[ℂ] W →ₗ[ℂ] ℂ where
  toFun v :=
    { toFun := fun w => B v w φ
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem evaluate_apply (φ : S) (B : Form (V := V) (W := W) (S := S))
    (v : V) (w : W) : evaluate φ B v w = B v w φ := rfl

/-- Vanishing on a functional's kernel forces factorization through that functional. -/
theorem factor_evaluation (e : S →ₗ[ℂ] ℂ) (φ₀ : S) (hφ₀ : e φ₀ = 1)
    (B : Form (V := V) (W := W) (S := S))
    (hB : restrict (LinearMap.ker e) B = 0) (v : V) (w : W) (φ : S) :
    B v w φ = e φ * evaluate φ₀ B v w := by
  have hker : φ - e φ • φ₀ ∈ LinearMap.ker e := by
    simp [LinearMap.mem_ker, hφ₀]
  have hzero := congrArg (fun C => C v w ⟨φ - e φ • φ₀, hker⟩) hB
  change B v w (φ - e φ • φ₀) = 0 at hzero
  simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, evaluate_apply] using hzero

/-- The action on test functions is supplied as actual linear maps. -/
def Invariant (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ)
    (B : Form (V := V) (W := W) (S := S)) : Prop :=
  ∀ g v w φ, B (ρ g v) (σ g w) (a g φ) = χ g * B v w φ

/-- Restriction has zero kernel on invariant forms when the residual bilinear
forms vanish. No nonzero test-function assumption is needed. -/
theorem eq_zero_of_restrict_eq_zero
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ) (e : S →ₗ[ℂ] ℂ)
    (he : ∀ g φ, e (a g φ) = e φ)
    (hbil : ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
      (∀ g v w, β (ρ g v) (σ g w) = χ g * β v w) → β = 0)
    (B : Form (V := V) (W := W) (S := S))
    (hB : Invariant ρ σ a χ B) (hres : restrict (LinearMap.ker e) B = 0) : B = 0 := by
  by_cases he0 : ∀ φ, e φ = 0
  · ext v w φ
    have h := congrArg (fun C => C v w ⟨φ, he0 φ⟩) hres
    exact h
  · push Not at he0
    obtain ⟨φ, hφ⟩ := he0
    let φ₀ := (e φ)⁻¹ • φ
    have hφ₀ : e φ₀ = 1 := by simp [φ₀, hφ]
    have hβ : evaluate φ₀ B = 0 := by
      apply hbil
      intro g v w
      have h := hB g v w φ₀
      rw [factor_evaluation e φ₀ hφ₀ B hres, he, hφ₀, one_mul] at h
      exact h
    ext v w φ
    rw [factor_evaluation e φ₀ hφ₀ B hres]
    simp [hβ]

/-- Uniqueness on the kernel and residual bilinear vanishing give full uniqueness. -/
theorem uniqueness_of_restriction
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ) (e : S →ₗ[ℂ] ℂ)
    (he : ∀ g φ, e (a g φ) = e φ)
    (hbil : ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
      (∀ g v w, β (ρ g v) (σ g w) = χ g * β v w) → β = 0)
    (hplus : ∀ B B' : Form (V := V) (W := W) (S := S),
      Invariant ρ σ a χ B → Invariant ρ σ a χ B' →
      restrict (LinearMap.ker e) B ≠ 0 →
      ∃ c : ℂ, restrict (LinearMap.ker e) B' = c • restrict (LinearMap.ker e) B)
    (B B' : Form (V := V) (W := W) (S := S))
    (hB : Invariant ρ σ a χ B) (hB' : Invariant ρ σ a χ B') (hB0 : B ≠ 0) :
    ∃ c : ℂ, B' = c • B := by
  have hr : restrict (LinearMap.ker e) B ≠ 0 := by
    intro hz
    exact hB0 (eq_zero_of_restrict_eq_zero ρ σ a χ e he hbil B hB hz)
  obtain ⟨c, hc⟩ := hplus B B' hB hB' hr
  refine ⟨c, sub_eq_zero.mp ?_⟩
  apply eq_zero_of_restrict_eq_zero ρ σ a χ e he hbil (B' - c • B)
  · intro g v w φ
    change B' (ρ g v) (σ g w) (a g φ) - c * B (ρ g v) (σ g w) (a g φ) =
      χ g * (B' v w φ - c * B v w φ)
    rw [hB', hB]
    ring
  · ext v w φ
    have h := congrArg (fun C => C v w φ) hc
    change B' v w φ.val - c * B v w φ.val = 0
    exact sub_eq_zero.mpr h

section Pullback

variable {V' : Type uV'} {W' : Type uW'}
variable [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

/-- Pull a trilinear form back in both representation variables. -/
def pullback (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W') :
    Form (V := V') (W := W') (S := S) →ₗ[ℂ] Form (V := V) (W := W) (S := S) where
  toFun B :=
    { toFun := fun v => (B (f v)).comp g
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

@[simp] theorem pullback_apply (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W')
    (B : Form (V := V') (W := W') (S := S)) (v : V) (w : W) (φ : S) :
    pullback f g B v w φ = B (f v) (g w) φ := rfl

theorem pullback_injective (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Injective (pullback (S := S) f g) := by
  intro B B' h
  ext v' w' φ
  obtain ⟨v, rfl⟩ := hf v'
  obtain ⟨w, rfl⟩ := hg w'
  exact congrArg (fun C => C v w φ) h

theorem invariant_pullback
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (ρ' : Representation ℂ G V') (σ' : Representation ℂ G W')
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ')
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ)
    (B : Form (V := V') (W := W') (S := S))
    (hB : Invariant ρ' σ' a χ B) :
    Invariant ρ σ a χ (pullback f.toLinearMap g.toLinearMap B) := by
  intro x v w φ
  change B (f (ρ x v)) (g (σ x w)) (a x φ) = χ x * B (f v) (g w) φ
  rw [f.isIntertwining, g.isIntertwining]
  exact hB x (f v) (g w) φ

/-- A uniqueness bound descends through surjective intertwining maps. -/
theorem uniqueness_of_surjective
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (ρ' : Representation ℂ G V') (σ' : Representation ℂ G W')
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (a : G → S →ₗ[ℂ] S) (χ : G → ℂ)
    (h : ∀ B B' : Form (V := V) (W := W) (S := S),
      Invariant ρ σ a χ B → Invariant ρ σ a χ B' → B ≠ 0 →
      ∃ c : ℂ, B' = c • B)
    (B B' : Form (V := V') (W := W') (S := S))
    (hB : Invariant ρ' σ' a χ B) (hB' : Invariant ρ' σ' a χ B')
    (hB0 : B ≠ 0) : ∃ c : ℂ, B' = c • B := by
  let P := pullback (S := S) f.toLinearMap g.toLinearMap
  have hinj : Function.Injective P := pullback_injective _ _ hf hg
  have hn : P B ≠ 0 := by
    intro hz
    exact hB0 (hinj (hz.trans P.map_zero.symm))
  obtain ⟨c, hc⟩ := h (P B) (P B')
    (invariant_pullback ρ σ ρ' σ' f g a χ B hB)
    (invariant_pullback ρ σ ρ' σ' f g a χ B' hB') hn
  refine ⟨c, hinj ?_⟩
  rw [P.map_smul]
  exact hc

end Pullback

/-- Two uniform finite exceptional sets combine before the spectral parameter. -/
theorem uniqueness_outside_finite_union
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (a : G → S →ₗ[ℂ] S) (χ : ℂ → G → ℂ) (e : S →ₗ[ℂ] ℂ)
    (he : ∀ g φ, e (a g φ) = e φ) (z : ℂ → ℂ)
    (hbil : ∃ E : Finset ℂ, ∀ s, z s ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ g v w, β (ρ g v) (σ g w) = χ s g * β v w) → β = 0)
    (hplus : ∃ E : Finset ℂ, ∀ s, z s ∉ E →
      ∀ B B' : Form (V := V) (W := W) (S := S),
        Invariant ρ σ a (χ s) B → Invariant ρ σ a (χ s) B' →
        restrict (LinearMap.ker e) B ≠ 0 →
        ∃ c : ℂ, restrict (LinearMap.ker e) B' = c • restrict (LinearMap.ker e) B) :
    ∃ E : Finset ℂ, ∀ s, z s ∉ E →
      ∀ B B' : Form (V := V) (W := W) (S := S),
        Invariant ρ σ a (χ s) B → Invariant ρ σ a (χ s) B' →
        B ≠ 0 → ∃ c : ℂ, B' = c • B := by
  classical
  obtain ⟨Eb, hb⟩ := hbil
  obtain ⟨Ep, hp⟩ := hplus
  refine ⟨Eb ∪ Ep, ?_⟩
  intro s hs
  have hb' : z s ∉ Eb := fun hz => hs (Finset.mem_union_left Ep hz)
  have hp' : z s ∉ Ep := fun hz => hs (Finset.mem_union_right Eb hz)
  exact uniqueness_of_restriction ρ σ a (χ s) e he (hb s hb') (hp s hp')

end Langlands.RankinSelberg.TrilinearReduction
