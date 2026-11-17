import Langlands.Algebra.LatticeConfigurationBound

/-! # Bounded configurations in `ℤ^r × F` compatible modulo a large integer -/

open Finset

namespace Langlands.Algebra.MixedLatticeConfiguration

open LatticeConfiguration

section General

variable {M : Type*} [AddCommGroup M]

/-- The linear combination map attached to a finite family of elements of an additive
group. -/
def combination (S : Finset M) (φ : M → M) : (S → ℤ) →+ M where
  toFun c := ∑ χ : S, c χ • φ χ
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]

theorem combination_apply (S : Finset M) (φ : M → M) (c : S → ℤ) :
    combination S φ c = ∑ χ : S, c χ • φ χ := rfl

/-- A finite generating set of an additive group has a homomorphism with prescribed
values once every relation is preserved. -/
theorem exists_hom_of_relations (S : Finset M)
    (hS : AddSubgroup.closure (S : Set M) = ⊤) (φ : M → M)
    (h : ∀ c : S → ℤ, combination S id c = 0 → combination S φ c = 0) :
    ∃ T : M →+ M, ∀ χ ∈ S, T χ = φ χ := by
  classical
  have hsurj : Function.Surjective (combination S id) := by
    have hle : AddSubgroup.closure (S : Set M) ≤ (combination S id).range := by
      rw [AddSubgroup.closure_le]
      intro χ hχ
      refine ⟨fun ψ => if (ψ : M) = χ then 1 else 0, ?_⟩
      rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
      · simp
      · intro b _ hb
        have : (b : M) ≠ χ := fun h' => hb (Subtype.ext h')
        simp [this]
      · simp
    intro x
    have hx : x ∈ (combination S id).range := hle (hS ▸ AddSubgroup.mem_top x)
    exact hx
  let T := (AddMonoidHom.liftOfRightInverse (combination S id) (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj)) ⟨combination S φ, fun c hc => h c hc⟩
  refine ⟨T, fun χ hχ => ?_⟩
  let c : S → ℤ := fun ψ => if (ψ : M) = χ then 1 else 0
  have hc : combination S id c = χ := by
    rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
    · simp [c]
    · intro b _ hb
      have : (b : M) ≠ χ := fun h' => hb (Subtype.ext h')
      simp [c, this]
    · simp
  have hcφ : combination S φ c = φ χ := by
    rw [combination_apply, Finset.sum_eq_single ⟨χ, hχ⟩]
    · simp [c]
    · intro b _ hb
      have : (b : M) ≠ χ := fun h' => hb (Subtype.ext h')
      simp [c, this]
    · simp
  calc T χ = T (combination S id c) := by rw [hc]
    _ = combination S φ c := AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
    _ = φ χ := hcφ

end General

variable {r : Type*} [Fintype r] [DecidableEq r] {F : Type*} [AddCommGroup F]

/-- Reduction modulo `m` on `ℤ^r × F`: coordinatewise reduction on `ℤ^r` and the
identity on `F`. -/
def mred (r : Type*) (F : Type*) [AddCommGroup F] (m : ℕ) :
    (r → ℤ) × F →+ (r → ZMod m) × F :=
  (red r m).prodMap (AddMonoidHom.id F)

omit [Fintype r] [DecidableEq r] in
@[simp] theorem mred_apply (m : ℕ) (x : (r → ℤ) × F) :
    mred r F m x = (red r m x.1, x.2) := rfl

omit [Fintype r] [DecidableEq r] in
/-- Reduction modulo `m` on `ℤ^r × F` is surjective. -/
theorem mred_surjective (r : Type*) (F : Type*) [AddCommGroup F] (m : ℕ) :
    Function.Surjective (mred r F m) := by
  rintro ⟨y, z⟩
  obtain ⟨x, hx⟩ := red_surjective r m y
  exact ⟨(x, z), by simp [hx]⟩

omit [DecidableEq r] in
/-- An element of `ℤ^r × F` reducing to `0` modulo `m`, whose `ℤ^r`-coordinates have
absolute values summing to less than `m`, is zero. -/
theorem eq_zero_of_mred_eq_zero {m : ℕ} {v : (r → ℤ) × F} (hv : mred r F m v = 0)
    (hsmall : ∑ j, (v.1 j).natAbs < m) : v = 0 := by
  have h1 : red r m v.1 = 0 := congrArg Prod.fst hv
  have h2 : v.2 = 0 := congrArg Prod.snd hv
  exact Prod.ext (eq_zero_of_red_eq_zero h1 hsmall) h2

/-- The box of `ℤ^r × F`: the elements whose `ℤ^r`-coordinates all have absolute value
at most `n`. -/
def mbox (r : Type*) [Fintype r] [DecidableEq r] (F : Type*) [Fintype F] (n : ℕ) :
    Finset ((r → ℤ) × F) :=
  box r n ×ˢ Finset.univ

omit [AddCommGroup F] in
theorem mem_mbox [Fintype F] {n : ℕ} {x : (r → ℤ) × F} :
    x ∈ mbox r F n ↔ ∀ j, |x.1 j| ≤ n := by
  simp [mbox, mem_box]

/-- Uniform bound: there is `m₀` such that for every `m ≥ m₀`, every generating
configuration `S` in the box of radius `n` of `ℤ^r × F` and every map `φ` into the box
that is compatible modulo `m` with some endomorphism of `(ℤ/m)^r × F` extends to a
homomorphism of `ℤ^r × F`. -/
theorem exists_bound (r : Type*) [Fintype r] [DecidableEq r] (F : Type*) [AddCommGroup F]
    [Fintype F] (n : ℕ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ S : Finset ((r → ℤ) × F), (∀ χ ∈ S, χ ∈ mbox r F n) →
      AddSubgroup.closure (S : Set ((r → ℤ) × F)) = ⊤ →
      ∀ φ : (r → ℤ) × F → (r → ℤ) × F, (∀ χ ∈ S, φ χ ∈ mbox r F n) →
      ∀ γ : (r → ZMod m) × F →+ (r → ZMod m) × F,
        (∀ χ ∈ S, mred r F m (φ χ) = γ (mred r F m χ)) →
        ∃ T : (r → ℤ) × F →+ (r → ℤ) × F, ∀ χ ∈ S, T χ = φ χ := by
  classical
  let B := mbox r F n
  -- configurations: a subset of the box and a self-map of the box
  let ext : (B → B) → (r → ℤ) × F → (r → ℤ) × F :=
    fun ψ χ => if h : χ ∈ B then (ψ ⟨χ, h⟩ : (r → ℤ) × F) else 0
  let Bad : Finset ((r → ℤ) × F) → (B → B) → Prop := fun S ψ =>
    ∃ c : S → ℤ, combination S id c = 0 ∧ combination S (ext ψ) c ≠ 0
  let bound : Finset ((r → ℤ) × F) → (B → B) → ℕ := fun S ψ =>
    if h : Bad S ψ then ∑ j, ((combination S (ext ψ) h.choose).1 j).natAbs else 0
  let m₀ := (B.powerset ×ˢ (Finset.univ : Finset (B → B))).sup (fun p => bound p.1 p.2) + 1
  refine ⟨m₀, fun m hm S hSbox hS φ hφ γ hγ => ?_⟩
  apply exists_hom_of_relations S hS φ
  intro c hc
  by_contra hne
  have hSB : S ⊆ B := fun χ hχ => hSbox χ hχ
  let ψ : B → B := fun χ =>
    if hχ : (χ : (r → ℤ) × F) ∈ S then ⟨φ χ, hφ χ hχ⟩ else χ
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
  have hred : mred r F m (combination S φ c') = 0 := by
    rw [combination_apply, map_sum]
    have : ∀ χ : S, mred r F m (c' χ • φ χ) =
        γ (mred r F m (c' χ • (χ : (r → ℤ) × F))) := by
      intro χ
      rw [map_zsmul, map_zsmul, map_zsmul, hγ χ χ.2]
    rw [Finset.sum_congr rfl fun χ _ => this χ, ← map_sum, ← map_sum]
    have h0 : ∑ χ : S, c' χ • (χ : (r → ℤ) × F) = 0 := hc'0
    rw [h0, map_zero, map_zero]
  have hsmall : ∑ j, ((combination S φ c').1 j).natAbs < m := by
    have hle : bound S ψ ≤ m₀ - 1 := by
      have hmem : (S, ψ) ∈ B.powerset ×ˢ (Finset.univ : Finset (B → B)) :=
        Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hSB, Finset.mem_univ _⟩
      have := Finset.le_sup (f := fun p : Finset ((r → ℤ) × F) × (B → B) => bound p.1 p.2) hmem
      simpa [m₀] using this
    have hb : bound S ψ = ∑ j, ((combination S (ext ψ) c').1 j).natAbs := by
      simp only [bound, hbad, ↓reduceDIte]
      rfl
    rw [← hcomb, ← hb]
    omega
  exact hc'ne (by rw [hcomb]; exact eq_zero_of_mred_eq_zero hred hsmall)

section Reduction

omit [Fintype r] [DecidableEq r]

/-- If `m` kills `F`, every endomorphism of `ℤ^r × F` induces an endomorphism of
`(ℤ/m)^r × F`. -/
theorem exists_mred_comp {m : ℕ} (hF : ∀ x : F, m • x = 0)
    (T : (r → ℤ) × F →+ (r → ℤ) × F) :
    ∃ Tb : (r → ZMod m) × F →+ (r → ZMod m) × F,
      Tb.comp (mred r F m) = (mred r F m).comp T := by
  have hker : (mred r F m).ker ≤ ((mred r F m).comp T).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hx1 : red r m x.1 = 0 := congrArg Prod.fst hx
    have hx2 : x.2 = 0 := congrArg Prod.snd hx
    have hdvd : ∀ j, ∃ k : ℤ, x.1 j = (m : ℤ) * k := by
      intro j
      have hj := congrFun hx1 j
      rw [red_apply, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
      exact hj
    choose y hy using hdvd
    have hx' : x = (m : ℤ) • ((y, 0) : (r → ℤ) × F) := by
      refine Prod.ext ?_ ?_
      · funext j
        simp [hy j]
      · simp [hx2]
    rw [hx', AddMonoidHom.comp_apply, map_zsmul, map_zsmul]
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · change ((m : ℤ) • (mred r F m (T (y, 0)))).2 = 0
      rw [Prod.smul_snd, natCast_zsmul]
      exact hF _
  exact ⟨(mred r F m).liftOfRightInverse (Function.surjInv (mred_surjective r F m))
    (Function.rightInverse_surjInv _) ⟨(mred r F m).comp T, hker⟩,
    (mred r F m).liftOfRightInverse_comp _ _ _⟩

/-- If `m` kills `F`, every automorphism of `ℤ^r × F` induces an automorphism of
`(ℤ/m)^r × F`. -/
theorem exists_mred_equiv {m : ℕ} (hF : ∀ x : F, m • x = 0)
    (T : (r → ℤ) × F ≃+ (r → ℤ) × F) :
    ∃ Tb : (r → ZMod m) × F ≃+ (r → ZMod m) × F,
      ∀ x, Tb (mred r F m x) = mred r F m (T x) := by
  obtain ⟨Tb₁, h₁⟩ := exists_mred_comp hF T.toAddMonoidHom
  obtain ⟨Tb₂, h₂⟩ := exists_mred_comp hF T.symm.toAddMonoidHom
  have e₁ : ∀ x, Tb₁ (mred r F m x) = mred r F m (T x) := fun x => congrArg (· x) h₁
  have e₂ : ∀ x, Tb₂ (mred r F m x) = mred r F m (T.symm x) := fun x => congrArg (· x) h₂
  have hl : ∀ y, Tb₂ (Tb₁ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := mred_surjective r F m y
    rw [e₁, e₂, AddEquiv.symm_apply_apply]
  have hr : ∀ y, Tb₁ (Tb₂ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := mred_surjective r F m y
    rw [e₂, e₁, AddEquiv.apply_symm_apply]
  let Tb : (r → ZMod m) × F ≃+ (r → ZMod m) × F :=
    { toFun := Tb₁
      invFun := Tb₂
      left_inv := hl
      right_inv := hr
      map_add' := fun x y => Tb₁.map_add x y }
  exact ⟨Tb, e₁⟩

end Reduction

end Langlands.Algebra.MixedLatticeConfiguration
