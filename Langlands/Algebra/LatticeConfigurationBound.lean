import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval

/-! # Linear extension of bounded configurations compatible modulo a large integer -/

open Finset

namespace Langlands.Algebra.LatticeConfiguration

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- Coordinatewise reduction modulo `m`. -/
def red (r : Type*) (m : ℕ) : (r → ℤ) →+ (r → ZMod m) :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod m)) (r)

omit [Fintype r] [DecidableEq r] in
@[simp] theorem red_apply (m : ℕ) (x : r → ℤ) (j : r) :
    red r m x j = (x j : ZMod m) := rfl

omit [Fintype r] [DecidableEq r] in
/-- Reduction modulo `m` is surjective. -/
theorem red_surjective (r : Type*) (m : ℕ) : Function.Surjective (red r m) := by
  intro y
  refine ⟨fun j => ((y j).cast : ℤ), ?_⟩
  funext j
  simp [red_apply]

/-- The linear combination map attached to a finite family of vectors. -/
def combination (S : Finset (r → ℤ)) (φ : (r → ℤ) → (r → ℤ)) :
    (S → ℤ) →+ (r → ℤ) where
  toFun c := ∑ χ : S, c χ • φ χ
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]

omit [Fintype r] [DecidableEq r] in
theorem combination_apply (S : Finset (r → ℤ)) (φ : (r → ℤ) → (r → ℤ))
    (c : S → ℤ) : combination S φ c = ∑ χ : S, c χ • φ χ := rfl

omit [DecidableEq r] in
/-- A finite generating set has a homomorphism with prescribed values once
every relation is preserved. -/
theorem exists_hom_of_relations (S : Finset (r → ℤ))
    (hS : AddSubgroup.closure (S : Set (r → ℤ)) = ⊤) (φ : (r → ℤ) → (r → ℤ))
    (h : ∀ c : S → ℤ, combination S id c = 0 → combination S φ c = 0) :
    ∃ T : (r → ℤ) →+ (r → ℤ), ∀ χ ∈ S, T χ = φ χ := by
  classical
  have hsurj : Function.Surjective (combination S id) := by
    have hle : AddSubgroup.closure (S : Set (r → ℤ)) ≤ (combination S id).range := by
      rw [AddSubgroup.closure_le]
      intro χ hχ
      refine ⟨fun ψ => if (ψ : r → ℤ) = χ then 1 else 0, ?_⟩
      rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
      · simp
      · intro b _ hb
        have : (b : r → ℤ) ≠ χ := fun h' => hb (Subtype.ext h')
        simp [this]
      · simp
    intro x
    have hx : x ∈ (combination S id).range := hle (hS ▸ AddSubgroup.mem_top x)
    exact hx
  let T := (AddMonoidHom.liftOfRightInverse (combination S id) (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)) ⟨combination S φ, fun c hc => h c hc⟩
  refine ⟨T, fun χ hχ => ?_⟩
  let c : S → ℤ := fun ψ => if (ψ : r → ℤ) = χ then 1 else 0
  have hc : combination S id c = χ := by
    rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
    · simp [c]
    · intro b _ hb
      have : (b : r → ℤ) ≠ χ := fun h' => hb (Subtype.ext h')
      simp [c, this]
    · simp
  have hcφ : combination S φ c = φ χ := by
    rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
    · simp [c]
    · intro b _ hb
      have : (b : r → ℤ) ≠ χ := fun h' => hb (Subtype.ext h')
      simp [c, this]
    · simp
  calc T χ = T (combination S id c) := by rw [hc]
    _ = combination S φ c := AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
    _ = φ χ := hcφ

omit [DecidableEq r] in
/-- A vector divisible by `m` coordinatewise and of small size vanishes. -/
theorem eq_zero_of_red_eq_zero {m : ℕ} {v : r → ℤ} (hv : red r m v = 0)
    (hsmall : ∑ j, (v j).natAbs < m) : v = 0 := by
  funext j
  have hj : ((v j : ℤ) : ZMod m) = 0 := congrFun hv j
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
  have hle : (v j).natAbs ≤ ∑ j, (v j).natAbs :=
    Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  apply Int.eq_zero_of_abs_lt_dvd hj
  have : ((v j).natAbs : ℤ) < m := by exact_mod_cast lt_of_le_of_lt hle hsmall
  rw [Int.abs_eq_natAbs]
  exact this

/-- The box of vectors with all coordinates of absolute value at most `n`. -/
def box (r : Type*) [Fintype r] [DecidableEq r] (n : ℕ) : Finset (r → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem mem_box {n : ℕ} {x : r → ℤ} : x ∈ box r n ↔ ∀ j, |x j| ≤ n := by
  simp [box, Fintype.mem_piFinset, abs_le]

/-- Uniform bound: there is `m₀` such that for every `m ≥ m₀`, every generating
configuration `S` in the box of radius `n` and every map `φ` into the box that is
compatible modulo `m` with some endomorphism of `(ℤ/m)^r` extends to a
homomorphism of `ℤ^r`. -/
theorem exists_bound (r : Type*) [Fintype r] [DecidableEq r] (n : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∀ S : Finset (r → ℤ), (∀ χ ∈ S, ∀ j, |χ j| ≤ n) →
      AddSubgroup.closure (S : Set (r → ℤ)) = ⊤ →
      ∀ φ : (r → ℤ) → (r → ℤ), (∀ χ ∈ S, ∀ j, |φ χ j| ≤ n) →
      ∀ γ : (r → ZMod m) →+ (r → ZMod m),
        (∀ χ ∈ S, red r m (φ χ) = γ (red r m χ)) →
        ∃ T : (r → ℤ) →+ (r → ℤ), ∀ χ ∈ S, T χ = φ χ := by
  classical
  let B := box r n
  -- configurations: a subset of the box and a self-map of the box
  let ext : (B → B) → (r → ℤ) → (r → ℤ) :=
    fun ψ χ => if h : χ ∈ B then (ψ ⟨χ, h⟩ : r → ℤ) else 0
  let Bad : Finset (r → ℤ) → (B → B) → Prop := fun S ψ =>
    ∃ c : S → ℤ, combination S id c = 0 ∧ combination S (ext ψ) c ≠ 0
  let bound : Finset (r → ℤ) → (B → B) → ℕ := fun S ψ =>
    if h : Bad S ψ then ∑ j, (combination S (ext ψ) h.choose j).natAbs else 0
  let m₀ := (B.powerset ×ˢ (Finset.univ : Finset (B → B))).sup (fun p => bound p.1 p.2) + 1
  refine ⟨m₀, fun m hm S hSbox hS φ hφ γ hγ => ?_⟩
  apply exists_hom_of_relations S hS φ
  intro c hc
  by_contra hne
  have hSB : S ⊆ B := fun χ hχ => mem_box.mpr (hSbox χ hχ)
  let ψ : B → B := fun χ =>
    if hχ : (χ : r → ℤ) ∈ S then ⟨φ χ, mem_box.mpr (hφ χ hχ)⟩ else χ
  have hext : ∀ χ ∈ S, ext ψ χ = φ χ := by
    intro χ hχ
    simp [ext, ψ, hSB hχ, hχ]
  have hcomb : ∀ d : S → ℤ, combination S (ext ψ) d = combination S φ d := by
    intro d
    simp only [combination_apply]
    exact Finset.sum_congr rfl fun χ _ => by rw [hext χ χ.2]
  have hbad : Bad S ψ := ⟨c, hc, by rw [hcomb]; exact hne⟩
  obtain ⟨hc'0, hc'ne⟩ := hbad.choose_spec
  set c' := hbad.choose
  have hred : red r m (combination S φ c') = 0 := by
    rw [combination_apply, map_sum]
    have : ∀ χ : S, red r m (c' χ • φ χ) = γ (red r m (c' χ • (χ : r → ℤ))) := by
      intro χ
      rw [map_zsmul, map_zsmul, map_zsmul, hγ χ χ.2]
    rw [Finset.sum_congr rfl fun χ _ => this χ, ← map_sum, ← map_sum]
    have h0 : ∑ χ : S, c' χ • (χ : r → ℤ) = 0 := hc'0
    rw [h0, map_zero, map_zero]
  have hsmall : ∑ j, (combination S φ c' j).natAbs < m := by
    have hle : bound S ψ ≤ m₀ - 1 := by
      have hmem : (S, ψ) ∈ B.powerset ×ˢ (Finset.univ : Finset (B → B)) :=
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hSB, Finset.mem_univ _⟩
      have := Finset.le_sup (f := fun p : Finset (r → ℤ) × (B → B) => bound p.1 p.2) hmem
      simpa [m₀] using this
    have hb : bound S ψ = ∑ j, (combination S (ext ψ) c' j).natAbs := by
      simp only [bound, hbad, ↓reduceDIte]
      rfl
    rw [← hcomb, ← hb]
    omega
  exact hc'ne (by rw [hcomb]; exact eq_zero_of_red_eq_zero hred hsmall)

section Reduction

omit [Fintype r] [DecidableEq r]

/-- An endomorphism of `ℤ^r` induces an endomorphism of `(ℤ/m)^r`. -/
theorem exists_red_comp (m : ℕ) (T : (r → ℤ) →+ (r → ℤ)) :
    ∃ Tb : (r → ZMod m) →+ (r → ZMod m), Tb.comp (red r m) = (red r m).comp T := by
  have hker : (red r m).ker ≤ ((red r m).comp T).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hdvd : ∀ j, ∃ k : ℤ, x j = (m : ℤ) * k := by
      intro j
      have hj := congrFun hx j
      rw [red_apply, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
      exact hj
    choose y hy using hdvd
    have hx' : x = (m : ℤ) • y := by
      funext j
      rw [hy j, Pi.smul_apply, smul_eq_mul]
    rw [hx', AddMonoidHom.comp_apply, map_zsmul, map_zsmul]
    funext j
    simp
  exact ⟨(red r m).liftOfRightInverse (Function.surjInv (red_surjective r m))
    (Function.rightInverse_surjInv _) ⟨(red r m).comp T, hker⟩,
    (red r m).liftOfRightInverse_comp _ _ _⟩

/-- An automorphism of `ℤ^r` induces an automorphism of `(ℤ/m)^r`. -/
theorem exists_red_equiv (m : ℕ) (T : (r → ℤ) ≃+ (r → ℤ)) :
    ∃ Tb : (r → ZMod m) ≃+ (r → ZMod m), ∀ x, Tb (red r m x) = red r m (T x) := by
  obtain ⟨Tb₁, h₁⟩ := exists_red_comp m T.toAddMonoidHom
  obtain ⟨Tb₂, h₂⟩ := exists_red_comp m T.symm.toAddMonoidHom
  have e₁ : ∀ x, Tb₁ (red r m x) = red r m (T x) := fun x => congrArg (· x) h₁
  have e₂ : ∀ x, Tb₂ (red r m x) = red r m (T.symm x) := fun x => congrArg (· x) h₂
  have hl : ∀ y, Tb₂ (Tb₁ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := red_surjective r m y
    rw [e₁, e₂, AddEquiv.symm_apply_apply]
  have hr : ∀ y, Tb₁ (Tb₂ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := red_surjective r m y
    rw [e₂, e₁, AddEquiv.apply_symm_apply]
  let Tb : (r → ZMod m) ≃+ (r → ZMod m) :=
    { toFun := Tb₁
      invFun := Tb₂
      left_inv := hl
      right_inv := hr
      map_add' := fun x y => Tb₁.map_add x y }
  exact ⟨Tb, e₁⟩

end Reduction

end Langlands.Algebra.LatticeConfiguration
