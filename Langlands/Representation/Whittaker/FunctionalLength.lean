import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.RingTheory.Length

/-! Length of actual equivariant-functional spaces along finite filtrations. -/

noncomputable section

namespace Langlands.Whittaker

universe uK uG uV uW uX

section Algebraic

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (U : Subgroup G) (θ : U →* kˣ)

/-- The length of the full equivariant-functional space, including infinite length. -/
def functionalLength (ρ : Representation k G V) : ℕ∞ :=
  Module.length k (functionals U θ ρ)

theorem functionalLength_congr {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : functionalLength U θ ρ = functionalLength U θ σ :=
  (functionalsCongr (N := U) (θ := θ) e).length_eq

theorem functionalLength_eq_zero_iff (ρ : Representation k G V) :
    functionalLength U θ ρ = 0 ↔ Subsingleton (functionals U θ ρ) :=
  Module.length_eq_zero_iff

theorem functionalLength_ne_zero_iff (ρ : Representation k G V) :
    functionalLength U θ ρ ≠ 0 ↔ HasFunctional (N := U) (θ := θ) ρ := by
  rw [ne_eq, functionalLength_eq_zero_iff, not_subsingleton_iff_nontrivial]
  constructor
  · intro h
    let := h
    obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : functionals U θ ρ)
    exact ⟨ℓ, fun hz => hℓ (Subtype.ext hz)⟩
  · rintro ⟨ℓ, hℓ⟩
    exact ⟨⟨ℓ, 0, fun hz => hℓ (congrArg Subtype.val hz)⟩⟩

theorem functionalLength_eq_one_of_equiv (ρ : Representation k G V)
    (e : functionals U θ ρ ≃ₗ[k] k) : functionalLength U θ ρ = 1 := by
  exact e.length_eq.trans (Module.length_eq_one k k)

theorem functionalLength_top (ρ : Representation k G V) :
    functionalLength U θ (⊤ : Subrepresentation ρ).toRepresentation =
      functionalLength U θ ρ := by
  refine functionalLength_congr U θ
    { toLinearMap := (⊤ : Subrepresentation ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem functionalLength_bot (ρ : Representation k G V) :
    functionalLength U θ (⊥ : Subrepresentation ρ).toRepresentation = 0 := by
  apply (functionalLength_eq_zero_iff U θ _).mpr
  constructor
  intro ℓ m
  apply Subtype.ext
  ext ⟨v, hv⟩
  have hv' : v = 0 := hv
  subst hv'
  exact (map_zero ℓ.val).trans (map_zero m.val).symm

end Algebraic

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]
variable (U : Subgroup G) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
variable (θ : U →* ℂˣ) (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))

include hU hθ

/-- Smooth functional exactness gives additivity on actual short exact sequences. -/
theorem functionalLength_eq_add_of_exact
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G X}
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (hσ : IsSmooth σ) :
    functionalLength U θ σ = functionalLength U θ ρ + functionalLength U θ τ := by
  rw [add_comm]
  exact Module.length_eq_add_of_exact
    (functionalsComap (N := U) (θ := θ) p) (functionalsComap (N := U) (θ := θ) i)
    (functionalsComap_injective U θ p hp)
    (functionalsComap_surjective_of_smooth U hU θ hθ i hi hσ)
    (LinearMap.exact_iff.mpr (functionalsComap_range_eq_ker U θ i p hp hex).symm)

/-- Each actual successive quotient gives the increment in functional length. -/
theorem functionalLength_filtration_step {A : Rep.{uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hA : IsSmooth A.ρ) (j : Fin n) :
    functionalLength U θ (s.subrepresentation j.succ).toRepresentation =
      functionalLength U θ (s.subrepresentation j.castSucc).toRepresentation +
        functionalLength U θ (s.gradedRepresentation j).ρ := by
  have hle : s.subrepresentation j.castSucc ≤ s.subrepresentation j.succ :=
    s.monotone_subrepresentation (Fin.castSucc_le_succ j)
  let i : (s.subrepresentation j.castSucc).toRepresentation.IntertwiningMap
      (s.subrepresentation j.succ).toRepresentation :=
    { toLinearMap := Submodule.inclusion hle
      isIntertwining' := fun _ => rfl }
  let p := (s.gradedProjection j).hom
  let incl : (s.subrepresentation j.succ).toRepresentation.IntertwiningMap A.ρ :=
    { toLinearMap := (s.subrepresentation j.succ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  refine functionalLength_eq_add_of_exact U hU θ hθ i p
    (Submodule.inclusion_injective hle) (s.gradedProjection_surjective j) ?_
    (isSmooth_of_injective incl (Submodule.injective_subtype _) hA)
  ext ⟨v, hv⟩
  constructor
  · rintro ⟨⟨w, hw⟩, hwv⟩
    have hvw : v = w := (congrArg Subtype.val hwv).symm
    subst hvw
    change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  · intro hp
    change Submodule.Quotient.mk _ = 0 at hp
    have hp' := (Submodule.Quotient.mk_eq_zero _).mp hp
    exact ⟨⟨v, hp'⟩, rfl⟩

/-- Functional length adds along any actual finite filtration of a smooth representation. -/
theorem functionalLength_eq_sum_of_filtration {A : Rep.{uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hA : IsSmooth A.ρ) :
    functionalLength U θ A.ρ =
      ∑ j : Fin n, functionalLength U θ (s.gradedRepresentation j).ρ := by
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      functionalLength U θ (s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation =
        ∑ i : Fin j, functionalLength U θ (s.gradedRepresentation
          ⟨i, lt_of_lt_of_le i.isLt hj⟩).ρ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0]
      exact functionalLength_bot U θ A.ρ
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← ih hjn.le]
      exact functionalLength_filtration_step U hU θ hθ s hA ⟨j, hjn⟩
  have h := key n le_rfl
  have hl : (⟨n, Nat.lt_succ_of_le le_rfl⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hl, s.subrepresentation_last, functionalLength_top] at h
  exact h

/-- Total functional length one forces exactly one graded factor of length one;
all other graded factors have zero functional space. -/
theorem functionalLength_factors_of_eq_one {A : Rep.{uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hA : IsSmooth A.ρ)
    (hone : functionalLength U θ A.ρ = 1) :
    ∃ j : Fin n, functionalLength U θ (s.gradedRepresentation j).ρ = 1 ∧
      ∀ i : Fin n, i ≠ j → functionalLength U θ (s.gradedRepresentation i).ρ = 0 := by
  classical
  let f : Fin n → ℕ∞ := fun i => functionalLength U θ (s.gradedRepresentation i).ρ
  have hsum : ∑ i, f i = 1 := (functionalLength_eq_sum_of_filtration U hU θ hθ s hA).symm.trans hone
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra! hzero
    simp [hzero] at hsum
  have hjle : f j ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
  have hjone : f j = 1 := le_antisymm hjle (Order.one_le_iff_ne_zero.mpr hj)
  refine ⟨j, hjone, ?_⟩
  have heq : (1 : ℕ∞) + ∑ i ∈ Finset.univ.erase j, f i = 1 + 0 := by
    calc
      1 + ∑ i ∈ Finset.univ.erase j, f i = ∑ i, f i := by
        rw [← hjone]
        exact Finset.add_sum_erase _ _ (Finset.mem_univ j)
      _ = 1 + 0 := by simpa using hsum
  have herase : ∑ i ∈ Finset.univ.erase j, f i = 0 :=
    ENat.add_right_injective_of_ne_top (by simp) heq
  intro i hij
  have hle : f i ≤ ∑ k ∈ Finset.univ.erase j, f k :=
    Finset.single_le_sum (fun _ _ => bot_le)
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  exact le_antisymm (herase ▸ hle) bot_le

/-- In a supplied finite filtration, a one-dimensional total functional space
gives a unique actual graded factor admitting a nonzero functional. -/
theorem existsUnique_hasFunctional_factor {A : Rep.{uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hA : IsSmooth A.ρ)
    (e : functionals U θ A.ρ ≃ₗ[ℂ] ℂ) :
    ∃! j : Fin n, HasFunctional (N := U) (θ := θ) (s.gradedRepresentation j).ρ := by
  obtain ⟨j, hj, hzero⟩ := functionalLength_factors_of_eq_one U hU θ hθ s hA
    (functionalLength_eq_one_of_equiv U θ A.ρ e)
  refine ⟨j, (functionalLength_ne_zero_iff U θ _).mp (by rw [hj]; exact one_ne_zero), ?_⟩
  intro i hi
  by_contra hij
  exact (functionalLength_ne_zero_iff U θ _).mpr hi (hzero i hij)

end Smooth

end Langlands.Whittaker
