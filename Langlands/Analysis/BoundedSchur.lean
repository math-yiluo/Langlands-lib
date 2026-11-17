import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # A Schur lemma for algebraically irreducible families of bounded operators

Let `H` be a complex Banach space, `B` a set of bounded operators on `H`, and `V` a
(not necessarily closed) subspace of `H` that is invariant under `B` and on which `B`
acts transitively: every nonzero vector of `V` is sent to every vector of `V` by some
element of `B`. Then every linear endomorphism of `V` commuting with `B` is a scalar.

No countability assumption is needed: the proof replaces Dixmier's countable-dimension
argument by the nonemptiness of spectra in a complex Banach algebra.
-/

noncomputable section

namespace Langlands.Analysis

open Function Set

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A linear endomorphism `e` of the subspace `V` commutes with the operators in `B`:
whenever `w = b v` with `v w ∈ V`, also `e w = b (e v)`. -/
def CommutesOn (B : Set (H →L[ℂ] H)) (V : Submodule ℂ H) (e : V →ₗ[ℂ] V) : Prop :=
  ∀ b ∈ B, ∀ v w : V, (w : H) = b v → (e w : H) = b (e v)

namespace CommutesOn

variable {B : Set (H →L[ℂ] H)} {V : Submodule ℂ H}

theorem zero : CommutesOn B V 0 := by
  intro b _ v w _
  simp

theorem id : CommutesOn B V LinearMap.id := by
  intro b _ v w hw
  simpa using hw

theorem comp {e f : V →ₗ[ℂ] V} (he : CommutesOn B V e) (hf : CommutesOn B V f) :
    CommutesOn B V (e ∘ₗ f) := by
  intro b hb v w hw
  exact he b hb (f v) (f w) (hf b hb v w hw)

theorem add {e f : V →ₗ[ℂ] V} (he : CommutesOn B V e) (hf : CommutesOn B V f) :
    CommutesOn B V (e + f) := by
  intro b hb v w hw
  simp only [LinearMap.add_apply, Submodule.coe_add, map_add]
  rw [he b hb v w hw, hf b hb v w hw]

theorem smul {e : V →ₗ[ℂ] V} (he : CommutesOn B V e) (c : ℂ) :
    CommutesOn B V (c • e) := by
  intro b hb v w hw
  simp only [LinearMap.smul_apply, Submodule.coe_smul, map_smul]
  rw [he b hb v w hw]

theorem sub_smul_id {e : V →ₗ[ℂ] V} (he : CommutesOn B V e) (μ : ℂ) :
    CommutesOn B V (e - μ • LinearMap.id) := by
  intro b hb v w hw
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
  rw [he b hb v w hw, hw]

end CommutesOn

variable (B : Set (H →L[ℂ] H)) (V : Submodule ℂ H)

/-- Schur's lemma, algebraic part: a nonzero endomorphism commuting with a transitive
invariant family is bijective. -/
theorem bijective_of_commutesOn (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V)
    (htrans : ∀ u w : V, u ≠ 0 → ∃ b ∈ B, b u = w)
    {e : V →ₗ[ℂ] V} (he : CommutesOn B V e) (hne : e ≠ 0) : Bijective e := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    apply hne
    refine LinearMap.ext fun w => ?_
    obtain ⟨b, hb, hbw⟩ := htrans v w hv0
    apply Subtype.ext
    rw [he b hb v w hbw.symm, LinearMap.mem_ker.mp hv]
    simp
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, e v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext fun v => by simpa using h v)
    intro w
    obtain ⟨b, hb, hbw⟩ := htrans (e v₀) w hv₀
    refine ⟨⟨b v₀, hBV b hb v₀ v₀.2⟩, Subtype.ext ?_⟩
    rw [he b hb v₀ ⟨b v₀, hBV b hb v₀ v₀.2⟩ rfl, hbw]

/-- The image `{e u | e commutes with B}` of a vector `u` under the commutant. -/
def commutantOrbit (u : V) : Submodule ℂ H where
  carrier := {x | ∃ e : V →ₗ[ℂ] V, CommutesOn B V e ∧ (e u : H) = x}
  zero_mem' := ⟨0, CommutesOn.zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    exact ⟨e + f, he.add hf, by simp⟩
  smul_mem' := by
    rintro c _ ⟨e, he, rfl⟩
    exact ⟨c • e, he.smul c, by simp⟩

variable [CompleteSpace H]

/-- **Bounded Schur lemma.** If `B` is a family of bounded operators on a complex Banach
space leaving a subspace `V` invariant and acting transitively on its nonzero vectors, then
every linear endomorphism of `V` commuting with `B` is a scalar multiple of the identity. -/
theorem exists_eq_smul_id_of_commutesOn (hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V)
    (htrans : ∀ u w : V, u ≠ 0 → ∃ b ∈ B, b u = w)
    (d : V →ₗ[ℂ] V) (hd : CommutesOn B V d) : ∃ μ : ℂ, d = μ • LinearMap.id := by
  classical
  by_contra hcon
  push Not at hcon
  let dμ : ℂ → (V →ₗ[ℂ] V) := fun μ => d - μ • LinearMap.id
  have hdμ : ∀ μ v, (dμ μ v : H) = d v - μ • (v : H) := fun μ v => by simp [dμ]
  have hdμc : ∀ μ, CommutesOn B V (dμ μ) := fun μ => hd.sub_smul_id μ
  have hne : ∀ μ : ℂ, dμ μ ≠ 0 := fun μ h => hcon μ (sub_eq_zero.mp h)
  have hbij : ∀ μ : ℂ, Bijective (dμ μ) := fun μ =>
    bijective_of_commutesOn B V hBV htrans (hdμc μ) (hne μ)
  -- the inverse of `d - μ`
  let f : ℂ → (V →ₗ[ℂ] V) := fun μ =>
    (LinearEquiv.ofBijective (dμ μ) (hbij μ)).symm.toLinearMap
  have hf_left : ∀ μ v, dμ μ (f μ v) = v := fun μ v =>
    (LinearEquiv.ofBijective (dμ μ) (hbij μ)).apply_symm_apply v
  have hf_right : ∀ μ v, f μ (dμ μ v) = v := fun μ v =>
    (LinearEquiv.ofBijective (dμ μ) (hbij μ)).symm_apply_apply v
  have hfc : ∀ μ, CommutesOn B V (f μ) := by
    intro μ b hb v w hw
    set v' := f μ v with hv'
    have hbv' : b v' ∈ V := hBV b hb v' v'.2
    have key : dμ μ ⟨b v', hbv'⟩ = w := by
      apply Subtype.ext
      rw [(hdμc μ) b hb v' ⟨b v', hbv'⟩ rfl, hf_left μ v, hw]
    have : f μ w = ⟨b v', hbv'⟩ := by rw [← key, hf_right]
    rw [this]
  -- a nonzero vector
  obtain ⟨u, hu⟩ : ∃ u : V, u ≠ 0 := by
    by_contra h
    push Not at h
    exact hcon 0 (LinearMap.ext fun v => by rw [h v]; simp)
  obtain ⟨b₀, hb₀, hb₀u⟩ := htrans u (d u) hu
  let M := commutantOrbit B V u
  let W := M.topologicalClosure
  have hMW : ∀ x ∈ M, x ∈ W := fun x hx => M.le_topologicalClosure hx
  have huW : (u : H) ∈ W := hMW _ ⟨LinearMap.id, CommutesOn.id, rfl⟩
  -- `b₀` acts on `M` as `e u ↦ (e ∘ d) u`
  have hb₀e : ∀ e : V →ₗ[ℂ] V, CommutesOn B V e → b₀ (e u) = (e (d u) : H) := by
    intro e he
    exact (he b₀ hb₀ u (d u) hb₀u.symm).symm
  have hb₀M : ∀ x ∈ M, b₀ x ∈ M := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e ∘ₗ d, he.comp hd, by simp [hb₀e e he]⟩
  -- for each `μ`, an element of `B` acting on `M` as `e u ↦ (e ∘ f μ) u`
  have hbμ : ∀ μ : ℂ, ∃ b ∈ B, b u = (f μ u : H) := fun μ => htrans u (f μ u) hu
  choose b hbB hbu using hbμ
  have hbe : ∀ μ (e : V →ₗ[ℂ] V), CommutesOn B V e → b μ (e u) = (e (f μ u) : H) := by
    intro μ e he
    exact (he (b μ) (hbB μ) u (f μ u) (hbu μ).symm).symm
  have hbM : ∀ μ, ∀ x ∈ M, b μ x ∈ M := by
    rintro μ _ ⟨e, he, rfl⟩
    exact ⟨e ∘ₗ f μ, he.comp (hfc μ), by simp [hbe μ e he]⟩
  -- the two compositions are the identity on `M`
  have hleftM : ∀ μ, EqOn (fun x => b₀ (b μ x) - μ • b μ x) (fun x => x) M := by
    rintro μ _ ⟨e, he, rfl⟩
    have h1 : b₀ (b μ (e u)) = (e (f μ (d u)) : H) := by
      rw [hbe μ e he]
      have := hb₀e (e ∘ₗ f μ) (he.comp (hfc μ))
      simpa using this
    change b₀ (b μ (e u)) - μ • b μ (e u) = (e u : H)
    rw [h1, hbe μ e he]
    have h2 := congrArg (fun v : V => (e v : H)) (hf_right μ u)
    simp only [dμ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, Submodule.coe_sub, Submodule.coe_smul] at h2
    exact h2
  have hrightM : ∀ μ, EqOn (fun x => b μ (b₀ x - μ • x)) (fun x => x) M := by
    rintro μ _ ⟨e, he, rfl⟩
    change b μ (b₀ (e u) - μ • (e u : H)) = (e u : H)
    rw [map_sub, map_smul, hb₀e e he]
    have h1 : b μ (e (d u)) = (e (d (f μ u)) : H) := by
      have := hbe μ (e ∘ₗ d) (he.comp hd)
      simpa using this
    rw [h1, hbe μ e he]
    have h2 := congrArg (fun v : V => (e v : H)) (hf_left μ u)
    simp only [dμ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, Submodule.coe_sub, Submodule.coe_smul] at h2
    exact h2
  -- extend to the closure
  have hclos : ∀ (T : H →L[ℂ] H), (∀ x ∈ M, T x ∈ M) → ∀ x ∈ W, T x ∈ W := by
    intro T hT x hx
    exact map_mem_closure T.continuous hx hT
  have hleftW : ∀ μ, ∀ x ∈ W, b₀ (b μ x) - μ • b μ x = x := by
    intro μ x hx
    exact (hleftM μ).closure (by fun_prop) continuous_id hx
  have hrightW : ∀ μ, ∀ x ∈ W, b μ (b₀ x - μ • x) = x := by
    intro μ x hx
    exact (hrightM μ).closure (by fun_prop) continuous_id hx
  -- the Banach algebra of operators on `W`
  have : Nontrivial W := ⟨⟨⟨u, huW⟩, 0, fun h => hu (Subtype.ext (by
    simpa using congrArg Subtype.val h))⟩⟩
  let β : W →L[ℂ] W := b₀.restrict (hclos b₀ hb₀M)
  let γ : ℂ → (W →L[ℂ] W) := fun μ => (b μ).restrict (hclos (b μ) (hbM μ))
  have hunit : ∀ μ : ℂ, IsUnit (algebraMap ℂ (W →L[ℂ] W) μ - β) := by
    intro μ
    refine ⟨⟨algebraMap ℂ (W →L[ℂ] W) μ - β, -γ μ, ?_, ?_⟩, rfl⟩
    · ext x
      change μ • (-(b μ (x : H))) - b₀ (-(b μ (x : H))) = (x : H)
      rw [map_neg, smul_neg, neg_sub_neg]
      exact hleftW μ x x.2
    · ext x
      change -(b μ (μ • (x : H) - b₀ x)) = x
      rw [← map_neg, neg_sub]
      exact hrightW μ x x.2
  obtain ⟨μ, hμ⟩ := spectrum.nonempty β
  exact (spectrum.mem_iff.mp hμ) (hunit μ)

end Langlands.Analysis
