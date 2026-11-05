import Langlands.GroupScheme.SplitExistence.ShortRootModule
import Langlands.GroupScheme.SplitExistence.BlockRep

/-!
# The representations of `SL₂` of the simple roots on the short-root module

For every simple root `α_i` of a reduced root datum with a finite index type, this file builds
an integral representation of `SL₂` (`SL2Rep`) on the short-root module `ℤ^(Idx P b gen)`
(see `ShortRootModule`), attached to `α_i` and to the coroot `⟨·, α_i^∨⟩`, whose raising and
lowering operators are `raiseMat P b gen i` and `lowerMat P b gen i` (`simpleRep_E_one`,
`simpleRep_F_one`).

* If `α_i` is short, the vectors `v_{-α_i}`, `v_{α_i}` and the `u_t` form a Cartan block with
  `c_t = |⟨α_t, α_i^∨⟩|`, and the other short roots and the minimal-norm weights form strings of
  length at most one (`shortCartanRep`).
* Otherwise all short roots and all minimal-norm weights form strings of length at most one, and
  the vectors `u_t` form strings of length zero (`nonShortRep`).
-/

noncomputable section

universe u

open Matrix RootPairing

namespace Langlands.GroupScheme.SplitExistence

/-! ### More on column-monomial matrices -/

section ColMat

theorem colMat_congr_inst {B : Type*} {inst₁ inst₂ : DecidableEq B} {f f' : B → B}
    {κ κ' : B → ℤ} (h : ∀ c, κ c = κ' c ∧ (κ c ≠ 0 → f c = f' c)) :
    @colMat B inst₁ f κ = @colMat B inst₂ f' κ' := by
  obtain rfl : inst₁ = inst₂ := Subsingleton.elim _ _
  exact colMat_congr h

variable {B : Type*} [DecidableEq B]

theorem colMat_zero (f : B → B) : colMat f (0 : B → ℤ) = 0 := by
  ext r c
  simp [colMat_apply]

theorem submatrix_colMat {B' : Type*} [DecidableEq B'] (σ : B ≃ B') (f : B' → B')
    (κ : B' → ℤ) : (colMat f κ).submatrix σ σ = colMat (σ.symm ∘ f ∘ σ) (κ ∘ σ) := by
  ext r c
  rw [submatrix_apply, colMat_apply, colMat_apply]
  by_cases h : f (σ c) = σ r
  · rw [ite_eq_left h, ite_eq_left (show (σ.symm ∘ f ∘ σ) c = r by simp [h])]
    rfl
  · rw [ite_eq_right h,
      ite_eq_right (show ¬ (σ.symm ∘ f ∘ σ) c = r by simpa [Equiv.symm_apply_eq] using h)]

theorem fromBlocks_colMat {B' : Type*} [DecidableEq B'] (f : B → B) (κ : B → ℤ) (g : B' → B')
    (μ : B' → ℤ) :
    fromBlocks (colMat f κ) 0 0 (colMat g μ) = colMat (Sum.map f g) (Sum.elim κ μ) := by
  ext (r | r) (c | c)
  · by_cases h : f c = r <;> simp [colMat_apply, h]
  · simp [colMat_apply]
  · simp [colMat_apply]
  · by_cases h : g c = r <;> simp [colMat_apply, h]

omit [DecidableEq B] in
theorem submatrix_map_ne_zero {B' : Type*} (e : B ≃ B') {M : Matrix B B ℤ} {R : Type*}
    [CommRing R] {f : ℤ →+* R} (h : M.map f ≠ 0) : (M.submatrix e.symm e.symm).map f ≠ 0 := by
  intro h'
  apply h
  ext r c
  have := congrFun (congrFun h' (e r)) (e c)
  simpa using this

end ColMat

/-! ### The Cartan block as column-monomial matrices -/

section Cartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (c : ι → ℤ)

omit [Fintype ι] in
/-- The raising operator of the Cartan block: `v₋ ↦ u_{i₀}`, `u_t ↦ c_t v₊`, `v₊ ↦ 0`. -/
theorem cartE_one_eq_colMat :
    cartE i₀ c 1 = colMat (Sum.elim (fun k => if k = 0 then Sum.inr i₀ else Sum.inl 1)
      fun _ => Sum.inl 1) (Sum.elim (fun k => if k = 0 then 1 else 0) c) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cartE, colMat_apply]
  · fin_cases r <;> simp [cartE, colMat_apply]
  · fin_cases r'
    · by_cases h : t = i₀
      · subst h
        simp [cartE, colMat_apply]
      · simp [cartE, colMat_apply, h, Ne.symm h]
    · simp [cartE, colMat_apply]
  · simp [cartE, colMat_apply]

omit [Fintype ι] in
/-- The lowering operator of the Cartan block: `v₊ ↦ u_{i₀}`, `u_t ↦ c_t v₋`, `v₋ ↦ 0`. -/
theorem cartF_one_eq_colMat :
    cartF i₀ c 1 = colMat (Sum.elim (fun k => if k = 0 then Sum.inl 0 else Sum.inr i₀)
      fun _ => Sum.inl 0) (Sum.elim (fun k => if k = 0 then 0 else 1) c) := by
  ext (r | t) (r' | t')
  · fin_cases r <;> fin_cases r' <;> simp [cartF, colMat_apply]
  · fin_cases r <;> simp [cartF, colMat_apply]
  · fin_cases r'
    · simp [cartF, colMat_apply]
    · by_cases h : t = i₀
      · subst h
        simp [cartF, colMat_apply]
      · simp [cartF, colMat_apply, h, Ne.symm h]
  · simp [cartF, colMat_apply]

end Cartan

/-! ### Strings of length at most one as column-monomial matrices -/

section Strings

variable {X : Type*} [AddCommGroup X] {α : X} {pair : X →+ ℤ}

/-- For weights with pairings in `[-1, 1]`, `y = x + α` exactly when `pair x = -1` and `y` is
the reflection of `x`. -/
theorem eq_add_iff_of_abs_le (hα : pair α = 2) {x y : X} (hx : |pair x| ≤ 1)
    (hy : |pair y| ≤ 1) : y = x + α ↔ pair x = -1 ∧ x - pair x • α = y := by
  constructor
  · intro h
    have h1 := congrArg pair h
    rw [map_add, hα] at h1
    have h2 := abs_le.1 hx
    have h3 := abs_le.1 hy
    have hx1 : pair x = -1 := by omega
    refine ⟨hx1, ?_⟩
    rw [h, hx1]
    module
  · rintro ⟨h1, h2⟩
    rw [← h2, h1]
    module

/-- For weights with pairings in `[-1, 1]`, `y + α = x` exactly when `pair x = 1` and `y` is
the reflection of `x`. -/
theorem add_eq_iff_of_abs_le (hα : pair α = 2) {x y : X} (hx : |pair x| ≤ 1)
    (hy : |pair y| ≤ 1) : y + α = x ↔ pair x = 1 ∧ x - pair x • α = y := by
  constructor
  · intro h
    have h1 := congrArg pair h
    rw [map_add, hα] at h1
    have h2 := abs_le.1 hx
    have h3 := abs_le.1 hy
    have hx1 : pair x = 1 := by omega
    refine ⟨hx1, ?_⟩
    rw [hx1, ← h]
    module
  · rintro ⟨h1, h2⟩
    rw [← h2, h1]
    module

/-- The string decomposition of an injective family of weights with pairings in `[-1, 1]` that
is stable under a reflection map `f`: strings of length at most one. -/
def StringDecomp.ofRefl {C : Type u} [Finite C] {ω : C → X} (hinj : Function.Injective ω)
    (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1) (f : C → C)
    (hf : ∀ d, ω (f d) = ω d - pair (ω d) • α) : StringDecomp α pair C ω :=
  (StringData.ofUnit hinj hα hp fun d => ⟨f d, hf d⟩).decomp

theorem StringDecomp.ofRefl_E_one {C : Type u} [Finite C] [DecidableEq C] {ω : C → X}
    (hinj : Function.Injective ω) (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1) (f : C → C)
    (hf : ∀ d, ω (f d) = ω d - pair (ω d) • α) :
    (StringDecomp.ofRefl hinj hα hp f hf).E 1 =
      colMat f fun d => if pair (ω d) = -1 then 1 else 0 := by
  ext r c
  rw [ofRefl, StringData.ofUnit_decomp_E_one, colMat_apply]
  have key : ω r = ω c + α ↔ pair (ω c) = -1 ∧ f c = r := by
    rw [eq_add_iff_of_abs_le hα (hp c) (hp r), ← hf c, hinj.eq_iff]
  by_cases h1 : pair (ω c) = -1 <;> by_cases h2 : f c = r <;> simp [key, h1, h2]

theorem StringDecomp.ofRefl_F_one {C : Type u} [Finite C] [DecidableEq C] {ω : C → X}
    (hinj : Function.Injective ω) (hα : pair α = 2) (hp : ∀ d, |pair (ω d)| ≤ 1) (f : C → C)
    (hf : ∀ d, ω (f d) = ω d - pair (ω d) • α) :
    (StringDecomp.ofRefl hinj hα hp f hf).F 1 =
      colMat f fun d => if pair (ω d) = 1 then 1 else 0 := by
  ext r c
  rw [ofRefl, StringData.ofUnit_decomp_F_one, colMat_apply]
  have key : ω r + α = ω c ↔ pair (ω c) = 1 ∧ f c = r := by
    rw [add_eq_iff_of_abs_le hα (hp c) (hp r), ← hf c, hinj.eq_iff]
  by_cases h1 : pair (ω c) = 1 <;> by_cases h2 : f c = r <;> simp [key, h1, h2]

end Strings

/-! ### The pieces of the short-root module along a simple root -/

section Module

variable {J X Y : Type u} [Fintype J] [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  {b : P.Base} {r : ℕ} {gen : Fin r → X}

open Classical

variable (P) in
/-- The coroot `⟨·, α_i^∨⟩` as an additive map. -/
abbrev corootHom (i : J) : X →+ ℤ := (P.coroot' i).toAddMonoidHom

omit [Fintype J] in
theorem corootHom_apply (i : J) (x : X) : corootHom P i x = P.toLinearMap x (P.coroot i) := rfl

omit [Fintype J] in
theorem corootHom_root (i j : J) : corootHom P i (P.root j) = P.pairing j i := by
  rw [corootHom_apply, root_coroot_eq_pairing]

omit [Fintype J] in
theorem corootHom_root_self (i : J) : corootHom P i (P.root i) = 2 := by
  rw [corootHom_root, pairing_same]

omit [Fintype J] in
theorem root_reflectionPerm_eq_root_iff (i k : J) :
    P.root (P.reflectionPerm i k) = P.root i ↔ P.root k = -P.root i := by
  rw [← root_reflectionPerm_self, P.root.injective.eq_iff, P.root.injective.eq_iff]
  exact (P.reflectionPerm_involutive (i := i)).eq_iff

omit [Fintype J] in
theorem root_reflectionPerm_eq_neg_root_iff (i k : J) :
    P.root (P.reflectionPerm i k) = -P.root i ↔ P.root k = P.root i := by
  rw [← root_reflectionPerm_self, P.root.injective.eq_iff, P.root.injective.eq_iff,
    (P.reflectionPerm i).injective.eq_iff]

variable (P) in
/-- The short roots other than `±α_i`. -/
abbrev ShortIdxNe (i : J) : Type u :=
  {γ : ShortIdx P // P.root γ ≠ P.root i ∧ P.root γ ≠ -P.root i}

omit [Fintype J] in
theorem shRefl_ne (i : J) {γ : ShortIdx P} (h : P.root γ ≠ P.root i ∧ P.root γ ≠ -P.root i) :
    P.root (shRefl (P := P) i γ : J) ≠ P.root i ∧ P.root (shRefl (P := P) i γ : J) ≠ -P.root i := by
  rw [coe_shRefl, ne_eq, root_reflectionPerm_eq_root_iff, ne_eq,
    root_reflectionPerm_eq_neg_root_iff]
  exact ⟨h.2, h.1⟩

/-- The reflection of a short root other than `±α_i`. -/
def shReflNe (i : J) (γ : ShortIdxNe P i) : ShortIdxNe P i :=
  ⟨shRefl i γ.1, shRefl_ne i γ.2⟩

/-- The short roots other than `±α_i` form strings of length at most one along `α_i`. -/
def shortNeDecomp (i : J) :
    StringDecomp (P.root i) (corootHom P i) (ShortIdxNe P i) fun γ => P.root (γ.1 : J) :=
  StringDecomp.ofRefl (fun γ δ h => Subtype.ext (Subtype.ext (P.root.injective h)))
    (corootHom_root_self i)
    (fun γ => by
      rw [corootHom_root]
      exact γ.1.2 i (Ne.symm γ.2.1) fun h => γ.2.2 (neg_eq_iff_eq_neg.mpr h).symm)
    (shReflNe i) fun γ => by
      rw [corootHom_root]
      exact root_reflectionPerm_eq i γ.1.1

/-- If `α_i` is not short, all short roots form strings of length at most one along `α_i`. -/
def shortDecomp (i : J) (hi : ¬ IsShortRoot P i) :
    StringDecomp (P.root i) (corootHom P i) (ShortIdx P) fun γ => P.root γ :=
  StringDecomp.ofRefl (fun γ δ h => Subtype.ext (P.root.injective h)) (corootHom_root_self i)
    (fun γ => by
      rw [corootHom_root]
      exact γ.2 i (fun h => hi (γ.2.of_root_eq (Or.inl h)))
        fun h => hi (γ.2.of_root_eq (Or.inr h)))
    (shRefl i) fun γ => by
      rw [corootHom_root]
      exact root_reflectionPerm_eq i γ.1

variable (gen) in
/-- The minimal-norm weights form strings of length at most one along `α_i`. -/
def minDecomp (i : J) :
    StringDecomp (P.root i) (corootHom P i) (MinIdx P gen) fun ν => ν.1 :=
  StringDecomp.ofRefl Subtype.val_injective (corootHom_root_self i)
    (fun ν => abs_le.2 (minIdx_pairing ν i)) (minRefl i) fun _ => rfl

theorem shortNeDecomp_E_one (i : J) :
    (shortNeDecomp (P := P) i).E 1 =
      colMat (shReflNe i) fun γ => if corootHom P i (P.root (γ.1 : J)) = -1 then 1 else 0 :=
  StringDecomp.ofRefl_E_one _ _ _ _ _

theorem shortNeDecomp_F_one (i : J) :
    (shortNeDecomp (P := P) i).F 1 =
      colMat (shReflNe i) fun γ => if corootHom P i (P.root (γ.1 : J)) = 1 then 1 else 0 :=
  StringDecomp.ofRefl_F_one _ _ _ _ _

theorem shortDecomp_E_one (i : J) (hi : ¬ IsShortRoot P i) :
    (shortDecomp i hi).E 1 =
      colMat (shRefl i) fun γ => if corootHom P i (P.root (γ : J)) = -1 then 1 else 0 :=
  StringDecomp.ofRefl_E_one _ _ _ _ _

theorem shortDecomp_F_one (i : J) (hi : ¬ IsShortRoot P i) :
    (shortDecomp i hi).F 1 =
      colMat (shRefl i) fun γ => if corootHom P i (P.root (γ : J)) = 1 then 1 else 0 :=
  StringDecomp.ofRefl_F_one _ _ _ _ _

theorem minDecomp_E_one (i : J) :
    (minDecomp (P := P) gen i).E 1 =
      colMat (minRefl i) fun ν => if corootHom P i ν.1 = -1 then 1 else 0 :=
  StringDecomp.ofRefl_E_one _ _ _ _ _

theorem minDecomp_F_one (i : J) :
    (minDecomp (P := P) gen i).F 1 =
      colMat (minRefl i) fun ν => if corootHom P i ν.1 = 1 then 1 else 0 :=
  StringDecomp.ofRefl_F_one _ _ _ _ _

/-! ### The splitting of the basis along a short simple root -/

/-- The splitting of the basis of the short-root module along a short root `α_i`: the vectors
`v_{α_i}`, `v_{-α_i}` (to `Fin 2`), the vectors `u_t`, and the remaining vectors. -/
def cartSplitFun (i : J) : Idx P b gen → (Fin 2 ⊕ b.support) ⊕ (ShortIdxNe P i ⊕ MinIdx P gen)
  | .inl (.inl t) => .inl (.inr t)
  | .inl (.inr γ) =>
    if h : P.root γ = P.root i then .inl (.inl 1)
    else if h' : P.root γ = -P.root i then .inl (.inl 0) else .inr (.inl ⟨γ, h, h'⟩)
  | .inr ν => .inr (.inr ν)

/-- The inverse of `cartSplitFun`. -/
def cartSplitInv (i : J) (hi : IsShortRoot P i) :
    (Fin 2 ⊕ b.support) ⊕ (ShortIdxNe P i ⊕ MinIdx P gen) → Idx P b gen
  | .inl (.inl k) =>
    if k = 0 then .inl (.inr (shRefl (P := P) i ⟨i, hi⟩)) else .inl (.inr ⟨i, hi⟩)
  | .inl (.inr t) => .inl (.inl t)
  | .inr (.inl γ) => .inl (.inr γ.1)
  | .inr (.inr ν) => .inr ν

theorem cartSplitFun_of_eq (i : J) {γ : ShortIdx P} (h : P.root γ = P.root i) :
    cartSplitFun (b := b) (gen := gen) i (.inl (.inr γ)) = .inl (.inl 1) := by
  simp only [cartSplitFun]
  rw [dite_eq_left h]

theorem cartSplitFun_of_eq_neg (i : J) {γ : ShortIdx P} (h : P.root γ = -P.root i) :
    cartSplitFun (b := b) (gen := gen) i (.inl (.inr γ)) = .inl (.inl 0) := by
  have h' : P.root γ ≠ P.root i := fun h'' => root_ne_neg_self (P := P) i (h''.symm.trans h)
  simp only [cartSplitFun]
  rw [dite_eq_right h', dite_eq_left h]

theorem cartSplitFun_of_ne (i : J) {γ : ShortIdx P}
    (h : P.root γ ≠ P.root i ∧ P.root γ ≠ -P.root i) :
    cartSplitFun (b := b) (gen := gen) i (.inl (.inr γ)) = .inr (.inl ⟨γ, h⟩) := by
  simp only [cartSplitFun]
  rw [dite_eq_right h.1, dite_eq_right h.2]

theorem cartSplitInv_zero (i : J) (hi : IsShortRoot P i) :
    cartSplitInv (b := b) (gen := gen) i hi (.inl (.inl 0)) =
      .inl (.inr (shRefl (P := P) i ⟨i, hi⟩)) := rfl

theorem cartSplitInv_one (i : J) (hi : IsShortRoot P i) :
    cartSplitInv (b := b) (gen := gen) i hi (.inl (.inl 1)) = .inl (.inr ⟨i, hi⟩) := rfl

omit [Fintype J] in
theorem root_shRefl_self (i : J) (hi : IsShortRoot P i) :
    P.root (shRefl (P := P) i ⟨i, hi⟩ : J) = -P.root i := by
  rw [coe_shRefl_self, root_reflectionPerm_self]

variable (b gen) in
/-- The splitting of the basis of the short-root module along a short root `α_i`. -/
def cartSplit (i : J) (hi : IsShortRoot P i) :
    Idx P b gen ≃ (Fin 2 ⊕ b.support) ⊕ (ShortIdxNe P i ⊕ MinIdx P gen) where
  toFun := cartSplitFun i
  invFun := cartSplitInv i hi
  left_inv := by
    rintro ((t | γ) | ν)
    · rfl
    · by_cases h : P.root γ = P.root i
      · rw [cartSplitFun_of_eq i h, cartSplitInv_one]
        rw [show γ = ⟨i, hi⟩ from Subtype.ext (P.root.injective h)]
      · by_cases h' : P.root γ = -P.root i
        · rw [cartSplitFun_of_eq_neg i h', cartSplitInv_zero]
          rw [show γ = shRefl (P := P) i ⟨i, hi⟩ from
            Subtype.ext (P.root.injective (by rw [h', root_shRefl_self]))]
        · rw [cartSplitFun_of_ne i ⟨h, h'⟩]
          rfl
    · rfl
  right_inv := by
    rintro ((k | t) | (γ | ν))
    · have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      rcases hk with rfl | rfl
      · rw [cartSplitInv_zero, cartSplitFun_of_eq_neg i (root_shRefl_self i hi)]
      · rw [cartSplitInv_one, cartSplitFun_of_eq i (γ := ⟨i, hi⟩) rfl]
    · rfl
    · show cartSplitFun i (.inl (.inr γ.1)) = _
      rw [cartSplitFun_of_ne i γ.2]
    · rfl

theorem cartSplit_apply (i : J) (hi : IsShortRoot P i) (x : Idx P b gen) :
    cartSplit b gen i hi x = cartSplitFun i x := rfl

theorem cartSplit_symm_apply (i : J) (hi : IsShortRoot P i)
    (y : (Fin 2 ⊕ b.support) ⊕ (ShortIdxNe P i ⊕ MinIdx P gen)) :
    (cartSplit b gen i hi).symm y = cartSplitInv i hi y := rfl

/-! ### The representations of the simple roots -/

variable (b gen) in
/-- The representation of `SL₂` of a short simple root `α_i` on the short-root module: the
Cartan block on `v_{-α_i}`, `v_{α_i}` and the `u_t` with `c_t = |⟨α_t, α_i^∨⟩|`, and strings of
length at most one on the other short roots and on the minimal-norm weights. -/
def shortCartanRep (i : b.support) (hi : IsShortRoot P i) :
    SL2Rep.{u, u, u} (Idx P b gen) (idxWt P b gen) (P.root i) (corootHom P i) :=
  SL2Rep.ofCartan i (fun t => |P.pairing t i|) (cartSplit b gen i hi)
    ((shortNeDecomp (i : J)).sum (minDecomp gen (i : J)))
    (by simp [pairing_same]) (corootHom_root_self (i : J))
    (fun r => by
      rcases r with k | t
      · have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
        rcases hk with rfl | rfl
        · rw [cartSplit_symm_apply, cartSplitInv_zero]
          simp [idxWt, root_shRefl_self (i : J) hi, cartLevel]
        · rw [cartSplit_symm_apply, cartSplitInv_one]
          simp [idxWt, cartLevel]
      · simp [cartSplit_symm_apply, cartSplitInv, idxWt, cartLevel])
    (fun x => by rcases x with γ | ν <;> rfl)

variable (b gen) in
/-- The representation of `SL₂` of a simple root `α_i` that is not short on the short-root
module: strings of length zero on the `u_t`, and strings of length at most one on the short roots
and on the minimal-norm weights. -/
def nonShortRep (i : b.support) (hi : ¬ IsShortRoot P i) :
    SL2Rep.{u, u, u} (Idx P b gen) (idxWt P b gen) (P.root i) (corootHom P i) :=
  (((StringDecomp.trivial (α := P.root (i : J)) (pair := corootHom P i) (0 : b.support → X)
      fun _ => map_zero (corootHom P i)).sum (shortDecomp (i : J) hi)).sum
    (minDecomp gen (i : J))).toSL2Rep (corootHom_root_self (i : J))

theorem shortCartanRep_E_one (i : b.support) (hi : IsShortRoot P i) :
    (shortCartanRep b gen i hi).E 1 = raiseMat P b gen i := by
  rw [shortCartanRep, SL2Rep.ofCartan_E, StringDecomp.sum_E, shortNeDecomp_E_one,
    minDecomp_E_one, fromBlocks_colMat, cartE_one_eq_colMat,
    fromBlocks_colMat, submatrix_colMat, raiseMat]
  refine colMat_congr_inst fun c => ?_
  rcases c with (t | γ) | ν
  · simp [cartSplit_apply, cartSplit_symm_apply, cartSplitFun, cartSplitInv, raiseCoeff_inl_inl,
      raiseTgt_inl_inl, hi]
  · by_cases h1 : P.root γ = P.root i
    · have hγ : (γ : J) = i := P.root.injective h1
      have hne : P.root γ ≠ -P.root i := by
        rw [h1]
        exact root_ne_neg_self (i : J)
      simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_eq _ h1]
      rw [raiseCoeff_of_ne hne, hγ, pairing_same]
      simp
    · by_cases h2 : P.root γ = -P.root i
      · simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_eq_neg _ h2]
        rw [raiseCoeff_of_eq h2, raiseTgt_of_eq h2]
        simp [cartSplit_symm_apply, cartSplitInv]
      · simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_ne _ ⟨h1, h2⟩]
        rw [raiseCoeff_of_ne h2, raiseTgt_of_ne h2]
        simp [cartSplit_symm_apply, cartSplitInv, shReflNe, corootHom_root]
  · simp [cartSplit_apply, cartSplit_symm_apply, cartSplitFun, cartSplitInv, raiseCoeff_inr,
      raiseTgt_inr, corootHom_apply]
    exact if_congr Iff.rfl rfl rfl

theorem shortCartanRep_F_one (i : b.support) (hi : IsShortRoot P i) :
    (shortCartanRep b gen i hi).F 1 = lowerMat P b gen i := by
  rw [shortCartanRep, SL2Rep.ofCartan_F, StringDecomp.sum_F, shortNeDecomp_F_one,
    minDecomp_F_one, fromBlocks_colMat, cartF_one_eq_colMat,
    fromBlocks_colMat, submatrix_colMat, lowerMat]
  refine colMat_congr_inst fun c => ?_
  rcases c with (t | γ) | ν
  · simp [cartSplit_apply, cartSplit_symm_apply, cartSplitFun, cartSplitInv, lowerCoeff_inl_inl,
      lowerTgt_inl_inl, hi]
  · by_cases h1 : P.root γ = P.root i
    · simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_eq _ h1]
      rw [lowerCoeff_of_eq h1, lowerTgt_of_eq h1]
      simp [cartSplit_symm_apply, cartSplitInv]
    · by_cases h2 : P.root γ = -P.root i
      · have hp : P.pairing γ i = -2 := by
          rw [← corootHom_root, h2, map_neg, corootHom_root_self]
        simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_eq_neg _ h2]
        rw [lowerCoeff_of_ne h1, hp]
        simp
      · simp only [Function.comp_apply, cartSplit_apply, cartSplitFun_of_ne _ ⟨h1, h2⟩]
        rw [lowerCoeff_of_ne h1, lowerTgt_of_ne h1]
        simp [cartSplit_symm_apply, cartSplitInv, shReflNe, corootHom_root]
  · simp [cartSplit_apply, cartSplit_symm_apply, cartSplitFun, cartSplitInv, lowerCoeff_inr,
      lowerTgt_inr, corootHom_apply]
    exact if_congr Iff.rfl rfl rfl

theorem nonShortRep_E_one (i : b.support) (hi : ¬ IsShortRoot P i) :
    (nonShortRep b gen i hi).E 1 = raiseMat P b gen i := by
  rw [nonShortRep, StringDecomp.toSL2Rep_E, StringDecomp.sum_E, StringDecomp.sum_E,
    StringDecomp.trivial_E_one, ← colMat_zero (id : b.support → b.support), shortDecomp_E_one,
    minDecomp_E_one, fromBlocks_colMat,
    fromBlocks_colMat, raiseMat]
  refine colMat_congr_inst fun c => ?_
  rcases c with (t | γ) | ν
  · simp [raiseCoeff_inl_inl, hi]
  · have hne : P.root γ ≠ -P.root i := fun h =>
      hi (γ.2.of_root_eq (Or.inr (by rw [h, neg_neg])))
    rw [raiseCoeff_of_ne hne, raiseTgt_of_ne hne]
    simp [corootHom_root]
  · simp [raiseCoeff_inr, raiseTgt_inr, corootHom_apply]
    exact if_congr Iff.rfl rfl rfl

theorem nonShortRep_F_one (i : b.support) (hi : ¬ IsShortRoot P i) :
    (nonShortRep b gen i hi).F 1 = lowerMat P b gen i := by
  rw [nonShortRep, StringDecomp.toSL2Rep_F, StringDecomp.sum_F, StringDecomp.sum_F,
    StringDecomp.trivial_F_one, ← colMat_zero (id : b.support → b.support), shortDecomp_F_one,
    minDecomp_F_one, fromBlocks_colMat,
    fromBlocks_colMat, lowerMat]
  refine colMat_congr_inst fun c => ?_
  rcases c with (t | γ) | ν
  · simp [lowerCoeff_inl_inl, hi]
  · have hne : P.root γ ≠ P.root i := fun h => hi (γ.2.of_root_eq (Or.inl h.symm))
    rw [lowerCoeff_of_ne hne, lowerTgt_of_ne hne]
    simp [corootHom_root]
  · simp [lowerCoeff_inr, lowerTgt_inr, corootHom_apply]
    exact if_congr Iff.rfl rfl rfl

variable (b gen) in
/-- The representation of `SL₂` of the simple root `α_i` on the short-root module. -/
def simpleRep (i : b.support) :
    SL2Rep.{u, u, u} (Idx P b gen) (idxWt P b gen) (P.root i) (corootHom P i) :=
  if hi : IsShortRoot P i then shortCartanRep b gen i hi else nonShortRep b gen i hi

/-- The raising operator of `simpleRep i` is `raiseMat i`. -/
theorem simpleRep_E_one (i : b.support) : (simpleRep b gen i).E 1 = raiseMat P b gen i := by
  by_cases hi : IsShortRoot P i
  · rw [simpleRep, dite_eq_left hi, shortCartanRep_E_one]
  · rw [simpleRep, dite_eq_right hi, nonShortRep_E_one]

/-- The lowering operator of `simpleRep i` is `lowerMat i`. -/
theorem simpleRep_F_one (i : b.support) : (simpleRep b gen i).F 1 = lowerMat P b gen i := by
  by_cases hi : IsShortRoot P i
  · rw [simpleRep, dite_eq_left hi, shortCartanRep_F_one]
  · rw [simpleRep, dite_eq_right hi, nonShortRep_F_one]

/-! ### Nonvanishing of the raising and lowering operators -/

variable [P.IsReduced]

/-- Some basis vector is sent to a basis vector by the raising operator of `α_i`. -/
theorem exists_raiseCoeff_eq_one (i : b.support) : ∃ c, raiseCoeff P b gen i c = 1 := by
  by_cases hi : IsShortRoot P i
  · exact ⟨.inl (.inr (shRefl (P := P) i ⟨i, hi⟩)), raiseCoeff_of_eq (root_shRefl_self (i : J) hi)⟩
  · obtain ⟨β, hβ, hβi⟩ := exists_isShortRoot_pairing_eq_neg_one (i : J) hi
    have hne : P.root β ≠ -P.root i := fun h => hi (hβ.of_root_eq (Or.inr (by rw [h, neg_neg])))
    refine ⟨.inl (.inr ⟨β, hβ⟩), ?_⟩
    rw [raiseCoeff_of_ne (γ := ⟨β, hβ⟩) hne, ite_eq_left hβi]

/-- Some basis vector is sent to a basis vector by the lowering operator of `α_i`. -/
theorem exists_lowerCoeff_eq_one (i : b.support) : ∃ c, lowerCoeff P b gen i c = 1 := by
  by_cases hi : IsShortRoot P i
  · exact ⟨.inl (.inr ⟨i, hi⟩), lowerCoeff_of_eq (P := P) (b := b) (gen := gen) (i := i)
    (γ := (⟨(i : J), hi⟩ : ShortIdx P)) rfl⟩
  · obtain ⟨β, hβ, hβi⟩ := exists_isShortRoot_pairing_eq_neg_one (i : J) hi
    have hp : P.pairing (shRefl (P := P) i ⟨β, hβ⟩ : J) i = 1 := by
      rw [coe_shRefl, pairing_reflectionPerm_left, pairing_same, hβi]
      norm_num
    have hne : P.root (shRefl (P := P) i ⟨β, hβ⟩ : J) ≠ P.root i := fun h =>
      hi ((shRefl (P := P) i ⟨β, hβ⟩).2.of_root_eq (Or.inl h.symm))
    exact ⟨.inl (.inr (shRefl i ⟨β, hβ⟩)), by rw [lowerCoeff_of_ne hne, ite_eq_left hp]⟩

end Module

end Langlands.GroupScheme.SplitExistence
