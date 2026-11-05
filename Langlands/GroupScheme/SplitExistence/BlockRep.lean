import Langlands.GroupScheme.SplitExistence.StringRep
import Langlands.GroupScheme.SplitExistence.ChevalleyData

/-!
# Integral representations of `SL₂` attached to one root

Fix `α : X` and an additive map `pair : X →+ ℤ` with `pair α = 2` (standing for
`⟨·, α^∨⟩`). An `SL2Rep B wt α pair` is an integral representation of `2 × 2` matrices of
determinant one on `ℤ^B`, whose basis vectors have weights `wt : B → X`, given by integral
divided powers `E k`, `F k` of a raising and a lowering operator of degree `α` and `-α`, with
the expected values at the unipotent, diagonal and Weyl matrices.

Such representations come from a string decomposition of the weights
(`StringDecomp.toSL2Rep`), or from a Cartan block together with a string decomposition of the
remaining weights (`SL2Rep.ofCartan`). They can be reindexed along an equivalence, and they
give group homomorphisms `SL₂(R) →* GL_B(R)` (`SL2Rep.hom`).
-/

noncomputable section

universe u u' v w

open Matrix

namespace Langlands.GroupScheme.SplitExistence

/-- An integral representation of `SL₂` on `ℤ^B` attached to `α : X` and `pair : X →+ ℤ`: the
matrices `rep R g` over every commutative ring `R : Type v`, multiplicative on matrices of
determinant one, natural in `R`, equal to the truncated exponentials of the divided powers
`E k` and `F k` at the unipotent matrices, diagonal with entries `t ^ pair (wt d)` at
`diag(t, t⁻¹)`, and moving weight `μ` to `μ - pair μ • α` at the Weyl matrix. The divided
powers vanish in degree above `3` and shift weights by multiples of `α`. -/
structure SL2Rep.{uB, uR, uX} {X : Type uX} [AddCommGroup X] (B : Type uB) [Fintype B]
    [DecidableEq B] (wt : B → X) (α : X) (pair : X →+ ℤ) where
  /-- The divided powers of the raising operator. -/
  E : ℕ → Matrix B B ℤ
  /-- The divided powers of the lowering operator. -/
  F : ℕ → Matrix B B ℤ
  /-- The matrix of a `2 × 2` matrix over `R`. -/
  rep : ∀ (R : Type uR) [CommRing R], Matrix (Fin 2) (Fin 2) R → Matrix B B R
  rep_mul : ∀ (R : Type uR) [CommRing R] (g h : Matrix (Fin 2) (Fin 2) R), g.det = 1 →
    h.det = 1 → rep R (g * h) = rep R g * rep R h
  rep_one : ∀ (R : Type uR) [CommRing R], rep R 1 = 1
  rep_map : ∀ (R S : Type uR) [CommRing R] [CommRing S] (f : R →+* S)
    (g : Matrix (Fin 2) (Fin 2) R), (rep R g).map f = rep S (g.map f)
  rep_upper : ∀ (R : Type uR) [CommRing R] (N : ℕ), 3 < N → ∀ s : R,
    rep R !![1, s; 0, 1] = ∑ k ∈ Finset.range N, s ^ k • (E k).map (Int.castRingHom R)
  rep_lower : ∀ (R : Type uR) [CommRing R] (N : ℕ), 3 < N → ∀ s : R,
    rep R !![1, 0; s, 1] = ∑ k ∈ Finset.range N, s ^ k • (F k).map (Int.castRingHom R)
  rep_diag : ∀ (R : Type uR) [CommRing R] (t : Rˣ),
    rep R !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)] = diagonal fun d => ((t ^ pair (wt d) : Rˣ) : R)
  rep_weyl : ∀ (R : Type uR) [CommRing R] (r c : B), rep R !![0, 1; -1, 0] r c ≠ 0 →
    wt r = wt c - pair (wt c) • α
  E_zero : E 0 = 1
  F_zero : F 0 = 1
  E_mul : ∀ a b, E a * E b = ((a + b).choose a : ℤ) • E (a + b)
  F_mul : ∀ a b, F a * F b = ((a + b).choose a : ℤ) • F (a + b)
  E_eq_zero : ∀ k, 3 < k → E k = 0
  F_eq_zero : ∀ k, 3 < k → F k = 0
  E_weight : ∀ k r c, E k r c ≠ 0 → wt r = wt c + k • α
  F_weight : ∀ k r c, F k r c ≠ 0 → wt r + k • α = wt c
  E_one_mul_F_one_sub : E 1 * F 1 - F 1 * E 1 = diagonal fun d => pair (wt d)

variable {X : Type w} [AddCommGroup X] {α : X} {pair : X →+ ℤ}

/-! ### Representations from string decompositions -/

/-- The representation of `SL₂` given by a string decomposition of the weights. -/
def StringDecomp.toSL2Rep {B : Type u} [Fintype B] [DecidableEq B] {wt : B → X}
    (S : StringDecomp α pair B wt) (hα : pair α = 2) : SL2Rep.{u, v, w} B wt α pair where
  E := S.E
  F := S.F
  rep _ _ g := S.rep g
  rep_mul _ _ g h _ _ := S.rep_mul g h
  rep_one _ _ := S.rep_one
  rep_map _ _ _ _ f g := S.rep_map f g
  rep_upper _ _ _ hN s := S.rep_upper hN s
  rep_lower _ _ _ hN s := S.rep_lower hN s
  rep_diag _ _ t := S.rep_diag_units hα t
  rep_weyl _ _ _ _ h := S.rep_weyl_ne_zero hα h
  E_zero := S.E_zero
  F_zero := S.F_zero
  E_mul := S.E_mul
  F_mul := S.F_mul
  E_eq_zero _ hk := S.E_eq_zero hk
  F_eq_zero _ hk := S.F_eq_zero hk
  E_weight _ _ _ h := S.E_ne_zero h
  F_weight _ _ _ h := S.F_ne_zero h
  E_one_mul_F_one_sub := S.E_one_mul_F_one_sub hα

theorem StringDecomp.toSL2Rep_E {B : Type u} [Fintype B] [DecidableEq B] {wt : B → X}
    (S : StringDecomp α pair B wt) (hα : pair α = 2) (k : ℕ) :
    (S.toSL2Rep.{u, v, w} hα).E k = S.E k := rfl

theorem StringDecomp.toSL2Rep_F {B : Type u} [Fintype B] [DecidableEq B] {wt : B → X}
    (S : StringDecomp α pair B wt) (hα : pair α = 2) (k : ℕ) :
    (S.toSL2Rep.{u, v, w} hα).F k = S.F k := rfl

/-! ### Representations with a Cartan block -/

section Cartan

variable {B : Type u} [Fintype B] [DecidableEq B] {wt : B → X}
  {ι C : Type u} [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C]
  (i₀ : ι) (c : ι → ℤ) (σ : B ≃ (Fin 2 ⊕ ι) ⊕ C) {ωC : C → X} (S : StringDecomp α pair C ωC)

theorem fromBlocks_ne_zero {l m : Type*} {R : Type*} [Zero R] {A : Matrix l l R}
    {D : Matrix m m R} {x y : l ⊕ m} (h : fromBlocks A 0 0 D x y ≠ 0) :
    (∃ r r', x = Sum.inl r ∧ y = Sum.inl r' ∧ A r r' ≠ 0) ∨
      (∃ r r', x = Sum.inr r ∧ y = Sum.inr r' ∧ D r r' ≠ 0) := by
  rcases x with r | r <;> rcases y with r' | r'
  · exact Or.inl ⟨r, r', rfl, rfl, h⟩
  · exact absurd rfl h
  · exact absurd rfl h
  · exact Or.inr ⟨r, r', rfl, rfl, h⟩

variable {i₀ c σ S}

omit [Fintype B] [DecidableEq B] [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C] in
theorem wt_eq_of_cartan (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) (d : B) :
    wt d = Sum.elim (fun r => cartLevel r • α) ωC (σ d) := by
  conv_lhs => rw [← σ.symm_apply_apply d]
  rcases σ d with r | x
  · exact hinl r
  · exact hinr x

variable (i₀ c σ S)

omit [DecidableEq B] [DecidableEq C] in
theorem ofCartan_rep_mul (hc : c i₀ = 2) {R : Type*} [CommRing R] (g h : Matrix (Fin 2) (Fin 2) R)
    (hg : g.det = 1) (hh : h.det = 1) :
    (fromBlocks (cart i₀ c (g * h)) 0 0 (S.rep (g * h))).submatrix σ σ =
      (fromBlocks (cart i₀ c g) 0 0 (S.rep g)).submatrix σ σ *
        (fromBlocks (cart i₀ c h) 0 0 (S.rep h)).submatrix σ σ := by
  rw [det_fin_two] at hg hh
  rw [submatrix_mul_equiv, fromBlocks_multiply, cart_mul i₀ c hc hg hh, S.rep_mul]
  simp

omit [Fintype B] [Fintype C] in
theorem ofCartan_rep_one {R : Type*} [CommRing R] :
    (fromBlocks (cart i₀ c (1 : Matrix (Fin 2) (Fin 2) R)) 0 0 (S.rep 1)).submatrix σ σ = 1 := by
  rw [cart_one, S.rep_one, fromBlocks_one, submatrix_one_equiv]

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_rep_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (g : Matrix (Fin 2) (Fin 2) R) :
    ((fromBlocks (cart i₀ c g) 0 0 (S.rep g)).submatrix σ σ).map f =
      (fromBlocks (cart i₀ c (g.map f)) 0 0 (S.rep (g.map f))).submatrix σ σ := by
  rw [← submatrix_map, fromBlocks_map, cart_map, S.rep_map]
  simp

omit [Fintype B] [DecidableEq B] in
theorem sum_fromBlocks_submatrix {l m : Type*} {R : Type*} [CommRing R] (σ : B ≃ l ⊕ m) (N : ℕ)
    (s : R) (A : ℕ → Matrix l l ℤ) (D : ℕ → Matrix m m ℤ) :
    ∑ k ∈ Finset.range N, s ^ k • ((fromBlocks (A k) 0 0 (D k)).submatrix σ σ).map
        (Int.castRingHom R) =
      (fromBlocks (∑ k ∈ Finset.range N, s ^ k • (A k).map (Int.castRingHom R)) 0 0
        (∑ k ∈ Finset.range N, s ^ k • (D k).map (Int.castRingHom R))).submatrix σ σ := by
  ext r r'
  simp only [submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  rcases σ r with x | x <;> rcases σ r' with y | y <;> simp [Matrix.sum_apply]

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_rep_upper {R : Type*} [CommRing R] {N : ℕ} (hN : 3 < N) (s : R) :
    (fromBlocks (cart i₀ c !![1, s; 0, 1]) 0 0 (S.rep !![1, s; 0, 1])).submatrix σ σ =
      ∑ k ∈ Finset.range N, s ^ k •
        ((fromBlocks (cartE i₀ c k) 0 0 (S.E k)).submatrix σ σ).map (Int.castRingHom R) := by
  rw [cart_upper i₀ c (by omega : 2 < N), S.rep_upper hN, sum_fromBlocks_submatrix]

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_rep_lower {R : Type*} [CommRing R] {N : ℕ} (hN : 3 < N) (s : R) :
    (fromBlocks (cart i₀ c !![1, 0; s, 1]) 0 0 (S.rep !![1, 0; s, 1])).submatrix σ σ =
      ∑ k ∈ Finset.range N, s ^ k •
        ((fromBlocks (cartF i₀ c k) 0 0 (S.F k)).submatrix σ σ).map (Int.castRingHom R) := by
  rw [cart_lower i₀ c (by omega : 2 < N), S.rep_lower hN, sum_fromBlocks_submatrix]

omit [Fintype B] [Fintype C] in
theorem ofCartan_rep_diag (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) {R : Type*} [CommRing R] (t : Rˣ) :
    (fromBlocks (cart i₀ c !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)]) 0 0
        (S.rep !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)])).submatrix σ σ =
      diagonal fun d => ((t ^ pair (wt d) : Rˣ) : R) := by
  rw [cart_diag, S.rep_diag_units hα, fromBlocks_diagonal, submatrix_diagonal_equiv]
  congr 1
  funext d
  rw [wt_eq_of_cartan hinl hinr d]
  simp only [Function.comp_apply]
  generalize σ d = x
  rcases x with (r | r) | x
  · fin_cases r
    · simp [cartLevel, hα, zpow_neg, ← inv_pow]
    · simp [cartLevel, hα]
  · simp [cartLevel]
  · rfl

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_rep_weyl (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) {R : Type*} [CommRing R] (r r' : B)
    (h : (fromBlocks (cart i₀ c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R)) 0 0
        (S.rep !![0, 1; -1, 0])).submatrix σ σ r r' ≠ 0) :
    wt r = wt r' - pair (wt r') • α := by
  rw [submatrix_apply] at h
  rw [wt_eq_of_cartan hinl hinr r, wt_eq_of_cartan hinl hinr r']
  rcases fromBlocks_ne_zero h with ⟨x, y, hx, hy, h⟩ | ⟨x, y, hx, hy, h⟩
  · rw [hx, hy]
    have := cart_weyl_ne_zero i₀ c h
    simp only [Sum.elim_inl, map_zsmul, hα, smul_eq_mul, this, sub_eq_add_neg,
      ← add_smul, ← neg_smul]
    congr 1
    ring
  · rw [hx, hy]
    exact S.rep_weyl_ne_zero hα h

omit [Fintype B] [Fintype C] in
theorem ofCartan_E_zero :
    (fromBlocks (cartE i₀ c 0) 0 0 (S.E 0)).submatrix σ σ = 1 := by
  rw [cartE_zero, S.E_zero, fromBlocks_one, submatrix_one_equiv]

omit [Fintype B] [Fintype C] in
theorem ofCartan_F_zero :
    (fromBlocks (cartF i₀ c 0) 0 0 (S.F 0)).submatrix σ σ = 1 := by
  rw [cartF_zero, S.F_zero, fromBlocks_one, submatrix_one_equiv]

omit [DecidableEq B] [DecidableEq C] in
theorem ofCartan_E_mul (hc : c i₀ = 2) (a b : ℕ) :
    (fromBlocks (cartE i₀ c a) 0 0 (S.E a)).submatrix σ σ *
        (fromBlocks (cartE i₀ c b) 0 0 (S.E b)).submatrix σ σ =
      ((a + b).choose a : ℤ) • (fromBlocks (cartE i₀ c (a + b)) 0 0 (S.E (a + b))).submatrix σ σ := by
  ext r r'
  rw [submatrix_mul_equiv, fromBlocks_multiply, cartE_mul i₀ c hc, S.E_mul]
  simp only [submatrix_apply, Matrix.smul_apply]
  rcases σ r with x | x <;> rcases σ r' with y | y <;> simp [-nsmul_eq_mul, -zsmul_eq_mul, -natCast_zsmul, Matrix.smul_apply]

omit [DecidableEq B] [DecidableEq C] in
theorem ofCartan_F_mul (hc : c i₀ = 2) (a b : ℕ) :
    (fromBlocks (cartF i₀ c a) 0 0 (S.F a)).submatrix σ σ *
        (fromBlocks (cartF i₀ c b) 0 0 (S.F b)).submatrix σ σ =
      ((a + b).choose a : ℤ) • (fromBlocks (cartF i₀ c (a + b)) 0 0 (S.F (a + b))).submatrix σ σ := by
  ext r r'
  rw [submatrix_mul_equiv, fromBlocks_multiply, cartF_mul i₀ c hc, S.F_mul]
  simp only [submatrix_apply, Matrix.smul_apply]
  rcases σ r with x | x <;> rcases σ r' with y | y <;> simp [-nsmul_eq_mul, -zsmul_eq_mul, -natCast_zsmul, Matrix.smul_apply]

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_E_eq_zero {k : ℕ} (hk : 3 < k) :
    (fromBlocks (cartE i₀ c k) 0 0 (S.E k)).submatrix σ σ = 0 := by
  rw [cartE_eq_zero i₀ c (by omega : 2 < k), S.E_eq_zero hk, fromBlocks_zero, submatrix_zero]
  rfl

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_F_eq_zero {k : ℕ} (hk : 3 < k) :
    (fromBlocks (cartF i₀ c k) 0 0 (S.F k)).submatrix σ σ = 0 := by
  rw [cartF_eq_zero i₀ c (by omega : 2 < k), S.F_eq_zero hk, fromBlocks_zero, submatrix_zero]
  rfl

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_E_weight (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) (k : ℕ) (r r' : B)
    (h : (fromBlocks (cartE i₀ c k) 0 0 (S.E k)).submatrix σ σ r r' ≠ 0) :
    wt r = wt r' + k • α := by
  rw [submatrix_apply] at h
  rw [wt_eq_of_cartan hinl hinr r, wt_eq_of_cartan hinl hinr r']
  rcases fromBlocks_ne_zero h with ⟨x, y, hx, hy, h⟩ | ⟨x, y, hx, hy, h⟩
  · rw [hx, hy]
    simp only [Sum.elim_inl, cartE_ne_zero i₀ c h, add_smul, natCast_zsmul]
  · rw [hx, hy]
    exact S.E_ne_zero h

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem ofCartan_F_weight (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) (k : ℕ) (r r' : B)
    (h : (fromBlocks (cartF i₀ c k) 0 0 (S.F k)).submatrix σ σ r r' ≠ 0) :
    wt r + k • α = wt r' := by
  rw [submatrix_apply] at h
  rw [wt_eq_of_cartan hinl hinr r, wt_eq_of_cartan hinl hinr r']
  rcases fromBlocks_ne_zero h with ⟨x, y, hx, hy, h⟩ | ⟨x, y, hx, hy, h⟩
  · rw [hx, hy]
    simp only [Sum.elim_inl, ← cartF_ne_zero i₀ c h, add_smul, natCast_zsmul]
  · rw [hx, hy]
    exact S.F_ne_zero h

omit [Fintype B] [Fintype ι] [Fintype C] in
theorem ofCartan_diagonal (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) :
    (diagonal fun d => pair (wt d)) =
      (fromBlocks (diagonal fun r => 2 * cartLevel r) 0 0
        (diagonal fun x => pair (ωC x))).submatrix σ σ := by
  rw [fromBlocks_diagonal, submatrix_diagonal_equiv]
  congr 1
  funext d
  rw [wt_eq_of_cartan hinl hinr d]
  simp only [Function.comp_apply]
  rcases σ d with r | x
  · simp [map_zsmul, hα, mul_comm]
  · rfl

theorem ofCartan_E_one_mul_F_one_sub (hc : c i₀ = 2) (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) :
    (fromBlocks (cartE i₀ c 1) 0 0 (S.E 1)).submatrix σ σ *
        (fromBlocks (cartF i₀ c 1) 0 0 (S.F 1)).submatrix σ σ -
      (fromBlocks (cartF i₀ c 1) 0 0 (S.F 1)).submatrix σ σ *
        (fromBlocks (cartE i₀ c 1) 0 0 (S.E 1)).submatrix σ σ =
      diagonal fun d => pair (wt d) := by
  rw [ofCartan_diagonal σ hα hinl hinr, ← cartE_one_mul_cartF_one_sub i₀ c hc,
    ← S.E_one_mul_F_one_sub hα, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply,
    fromBlocks_multiply]
  ext r r'
  simp only [Matrix.sub_apply, submatrix_apply]
  rcases σ r with x | x <;> rcases σ r' with y | y <;> simp [Matrix.sub_apply]

/-- The representation of `SL₂` given by a Cartan block `cart i₀ c` (with `c i₀ = 2`) on the
weights `-α, α, 0, …, 0` and a string decomposition of the remaining weights, glued along
`σ : B ≃ (Fin 2 ⊕ ι) ⊕ C`. -/
def SL2Rep.ofCartan (hc : c i₀ = 2) (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) : SL2Rep.{u, v, w} B wt α pair where
  E k := (fromBlocks (cartE i₀ c k) 0 0 (S.E k)).submatrix σ σ
  F k := (fromBlocks (cartF i₀ c k) 0 0 (S.F k)).submatrix σ σ
  rep _ _ g := (fromBlocks (cart i₀ c g) 0 0 (S.rep g)).submatrix σ σ
  rep_mul _ _ g h hg hh := ofCartan_rep_mul i₀ c σ S hc g h hg hh
  rep_one _ _ := ofCartan_rep_one i₀ c σ S
  rep_map _ _ _ _ f g := ofCartan_rep_map i₀ c σ S f g
  rep_upper _ _ _ hN s := ofCartan_rep_upper i₀ c σ S hN s
  rep_lower _ _ _ hN s := ofCartan_rep_lower i₀ c σ S hN s
  rep_diag _ _ t := ofCartan_rep_diag i₀ c σ S hα hinl hinr t
  rep_weyl _ _ r r' h := ofCartan_rep_weyl i₀ c σ S hα hinl hinr r r' h
  E_zero := ofCartan_E_zero i₀ c σ S
  F_zero := ofCartan_F_zero i₀ c σ S
  E_mul := ofCartan_E_mul i₀ c σ S hc
  F_mul := ofCartan_F_mul i₀ c σ S hc
  E_eq_zero _ hk := ofCartan_E_eq_zero i₀ c σ S hk
  F_eq_zero _ hk := ofCartan_F_eq_zero i₀ c σ S hk
  E_weight k r r' h := ofCartan_E_weight i₀ c σ S hinl hinr k r r' h
  F_weight k r r' h := ofCartan_F_weight i₀ c σ S hinl hinr k r r' h
  E_one_mul_F_one_sub := ofCartan_E_one_mul_F_one_sub i₀ c σ S hc hα hinl hinr

theorem SL2Rep.ofCartan_E (hc : c i₀ = 2) (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) (k : ℕ) :
    (SL2Rep.ofCartan.{u, v, w} i₀ c σ S hc hα hinl hinr).E k =
      (fromBlocks (cartE i₀ c k) 0 0 (S.E k)).submatrix σ σ := rfl

theorem SL2Rep.ofCartan_F (hc : c i₀ = 2) (hα : pair α = 2)
    (hinl : ∀ r, wt (σ.symm (Sum.inl r)) = cartLevel r • α)
    (hinr : ∀ x, wt (σ.symm (Sum.inr x)) = ωC x) (k : ℕ) :
    (SL2Rep.ofCartan.{u, v, w} i₀ c σ S hc hα hinl hinr).F k =
      (fromBlocks (cartF i₀ c k) 0 0 (S.F k)).submatrix σ σ := rfl

end Cartan

/-! ### Reindexing and the group homomorphism -/

namespace SL2Rep

variable {B : Type u} [Fintype B] [DecidableEq B] {wt : B → X}
  {B' : Type u'} [Fintype B'] [DecidableEq B']

/-- Transport of a representation along an equivalence of index types. -/
def reindex (V : SL2Rep.{u, v, w} B wt α pair) (e : B ≃ B') :
    SL2Rep.{u', v, w} B' (wt ∘ e.symm) α pair where
  E k := (V.E k).submatrix e.symm e.symm
  F k := (V.F k).submatrix e.symm e.symm
  rep R _ g := (V.rep R g).submatrix e.symm e.symm
  rep_mul R _ g h hg hh := by
    rw [V.rep_mul R g h hg hh, submatrix_mul_equiv]
  rep_one R _ := by rw [V.rep_one R, submatrix_one_equiv]
  rep_map R S _ _ f g := by rw [← submatrix_map, V.rep_map R S f g]
  rep_upper R _ N hN s := by
    rw [V.rep_upper R N hN s]
    ext r r'
    simp [Matrix.sum_apply]
  rep_lower R _ N hN s := by
    rw [V.rep_lower R N hN s]
    ext r r'
    simp [Matrix.sum_apply]
  rep_diag R _ t := by
    rw [V.rep_diag R t, submatrix_diagonal_equiv]
    rfl
  rep_weyl R _ r r' h := V.rep_weyl R (e.symm r) (e.symm r') h
  E_zero := by rw [V.E_zero, submatrix_one_equiv]
  F_zero := by rw [V.F_zero, submatrix_one_equiv]
  E_mul a b := by rw [submatrix_mul_equiv, V.E_mul]; rfl
  F_mul a b := by rw [submatrix_mul_equiv, V.F_mul]; rfl
  E_eq_zero k hk := by rw [V.E_eq_zero k hk, submatrix_zero]; rfl
  F_eq_zero k hk := by rw [V.F_eq_zero k hk, submatrix_zero]; rfl
  E_weight k r r' h := V.E_weight k (e.symm r) (e.symm r') h
  F_weight k r r' h := V.F_weight k (e.symm r) (e.symm r') h
  E_one_mul_F_one_sub := by
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    show (V.E 1 * V.F 1 - V.F 1 * V.E 1).submatrix e.symm e.symm = _
    rw [V.E_one_mul_F_one_sub, submatrix_diagonal_equiv]
    rfl

theorem reindex_E (V : SL2Rep.{u, v, w} B wt α pair) (e : B ≃ B') (k : ℕ) :
    (V.reindex e).E k = (V.E k).submatrix e.symm e.symm := rfl

theorem reindex_F (V : SL2Rep.{u, v, w} B wt α pair) (e : B ≃ B') (k : ℕ) :
    (V.reindex e).F k = (V.F k).submatrix e.symm e.symm := rfl

/-- The group homomorphism `SL₂(R) →* GL_B(R)` of a representation. -/
def hom (V : SL2Rep.{u, v, w} B wt α pair) (R : Type v) [CommRing R] :
    SpecialLinearGroup (Fin 2) R →* GL B R :=
  MonoidHom.toHomUnits
    { toFun := fun g => V.rep R g
      map_one' := V.rep_one R
      map_mul' := fun g h => V.rep_mul R g h g.2 h.2 }

theorem coe_hom (V : SL2Rep.{u, v, w} B wt α pair) (R : Type v) [CommRing R]
    (g : SpecialLinearGroup (Fin 2) R) :
    ((V.hom R g : GL B R) : Matrix B B R) = V.rep R g := rfl

end SL2Rep

end Langlands.GroupScheme.SplitExistence
