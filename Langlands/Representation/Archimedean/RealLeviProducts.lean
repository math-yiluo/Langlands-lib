import Langlands.Representation.Archimedean.RealLeviSlices

/-!
# Products over the classes of a block diagonal Levi subgroup

On the compact Levi subgroup `∏_j O(sz_j)` every element of the global dual space is a finite
sum of products of elements of the class dual spaces (`exists_isProdForm`). Iterated block Fourier
coefficients along slots inside the blocks act factor by factor (`coeffs_globalSlots`), and the
free algebra of one class acts on the factors of that class (`isProdForm_lift`). Internal
infrastructure for Task 6749; see `RealLeviProducts.md`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviProducts

open RealLeviChart RealLeviSlices RealInducedBlockBound RealInducedTorusCore

/-! ## Rotations inside a block -/

section Rotation

variable {c : ℕ} (sz : Fin c → ℕ)

theorem start_add_ne {j k : Fin c} (h : j ≠ k) (b : Fin (sz j)) (d : Fin (sz k)) :
    start sz j + (b : ℕ) ≠ start sz k + d := by
  intro e
  apply h
  have e' : pos sz j b = pos sz k d := Fin.ext (by rw [val_pos, val_pos]; exact e)
  exact congrArg Sigma.fst (finSigmaFinEquiv.injective
    (show finSigmaFinEquiv (⟨j, b⟩ : Σ i, Fin (sz i)) = finSigmaFinEquiv ⟨k, d⟩ from e'))

theorem start_add_lt (i : Fin c) {a : ℕ} (ha : a < sz i) : start sz i + a < ∑ j, sz j := by
  have h := (pos sz i ⟨a, ha⟩).2
  rwa [val_pos] at h

/-- The rotation in the coordinates `a, a + 1` of the block `i` is the rotation in the global
coordinates `start_i + a, start_i + a + 1`. -/
theorem blockRotation_start_add (i : Fin c) {a : ℕ} (ha : a + 1 < sz i) (θ : ℝ) :
    blockRotation (∑ j, sz j) (start sz i + a) θ = emb sz i (blockRotation (sz i) a θ) := by
  have hN : start sz i + a + 1 < ∑ j, sz j := start_add_lt sz i ha
  refine Units.ext ?_
  ext p q
  obtain ⟨⟨j, b⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨k, d⟩, rfl⟩ := finSigmaFinEquiv.surjective q
  rw [emb_val, embA, blockDiagHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, RealBlockRotation.blockRotation_apply hN]
  have hp : ((finSigmaFinEquiv (⟨j, b⟩ : Σ j, Fin (sz j)) : Fin (∑ j, sz j)) : ℕ) =
      start sz j + b := val_pos sz j b
  have hq : ((finSigmaFinEquiv (⟨k, d⟩ : Σ j, Fin (sz j)) : Fin (∑ j, sz j)) : ℕ) =
      start sz k + d := val_pos sz k d
  simp only [Fin.ext_iff, hp, hq]
  by_cases hjk : j = k
  · subst hjk
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases hji : j = i
    · subst hji
      rw [Pi.mulSingle_eq_same, RealBlockRotation.blockRotation_apply ha]
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [Pi.mulSingle_eq_of_ne hji, Matrix.one_apply]
      have h1 := start_add_ne sz hji b ⟨a, by omega⟩
      have h2 := start_add_ne sz hji b ⟨a + 1, ha⟩
      simp only [Fin.ext_iff] at h1 h2 ⊢
      split_ifs <;> first | rfl | (exfalso; omega)
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hjk]
    have h0 := start_add_ne sz hjk b d
    by_cases hji : j = i
    · have hki : k ≠ i := fun h => hjk (hji.trans h.symm)
      have h1 := start_add_ne sz hki d ⟨a, by omega⟩
      have h2 := start_add_ne sz hki d ⟨a + 1, ha⟩
      simp only at h1 h2
      split_ifs <;> first | rfl | (exfalso; omega)
    · have h1 := start_add_ne sz hji b ⟨a, by omega⟩
      have h2 := start_add_ne sz hji b ⟨a + 1, ha⟩
      simp only at h1 h2
      split_ifs <;> first | rfl | (exfalso; omega)

theorem emb_mul_blockDiagGL (i : Fin c) (κ : ∀ j, Langlands.GeneralLinear (sz j) ℝ)
    (x : Langlands.GeneralLinear (sz i) ℝ) :
    emb sz i x * blockDiagGL sz κ = blockDiagGL sz (Function.update κ i (x * κ i)) := by
  rw [emb_eq, ← map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

end Rotation

/-! ## Slots of a block -/

section Lift

variable {c : ℕ} (sz : Fin c → ℕ)

/-- A slot of the block `i`, at the corresponding global position. -/
def liftSlot (i : Fin c) (s : Slot (sz i)) : Slot (∑ j, sz j) where
  p := start sz i + s.p
  hp := by
    have h := start_add_lt sz i s.hp
    omega
  α := s.α
  M := s.M
  j := s.j
  x := s.x
  y := s.y
  w := s.w

/-- The iterated coefficients along lifted slots of the block `i` at `diag(κ)` are the
coefficients of the slice through `κ` in the block `i`. -/
theorem coeffs_liftSlots (i : Fin c) (F : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ) :
    ∀ (L : List (Slot (sz i))) (κ : ∀ j, Langlands.GeneralLinear (sz j) ℝ),
      coeffs (L.map (liftSlot sz i)) F (blockDiagGL sz κ) =
        coeffs L (fun x => F (blockDiagGL sz (Function.update κ i x))) (κ i)
  | [], κ => by
    simp only [List.map_nil, coeffs, Function.update_eq_self]
  | s :: L, κ => by
    simp only [List.map_cons, coeffs]
    unfold blockFourierCoefficient
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [show (liftSlot sz i s).p = start sz i + s.p from rfl,
      show (liftSlot sz i s).j = s.j from rfl, blockRotation_start_add sz i s.hp,
      emb_mul_blockDiagGL, coeffs_liftSlots i F L, Function.update_self]
    simp only [Function.update_idem]

theorem coeffs_append {N : ℕ} (A B : List (Slot N)) (F : Langlands.GeneralLinear N ℝ → ℂ) :
    coeffs (A ++ B) F = coeffs A (coeffs B F) := by
  induction A with
  | nil => rfl
  | cons s A ih => simp only [List.cons_append, coeffs, ih]

theorem coeffs_sum_mul {N : ℕ} {ι : Type*} [Fintype ι] (D : ι → ℂ)
    {f : ι → Langlands.GeneralLinear N ℝ → ℂ} (hf : ∀ a, Continuous (f a)) :
    ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      coeffs L (fun x => ∑ a, D a * f a x) g = ∑ a, D a * coeffs L (f a) g
  | [], _ => rfl
  | s :: L, g => by
    simp only [coeffs]
    rw [show coeffs L (fun x => ∑ a, D a * f a x) = fun x => ∑ a, D a * coeffs L (f a) x from
      funext fun x => coeffs_sum_mul D hf L x]
    unfold blockFourierCoefficient
    simp only [Finset.sum_mul]
    refine (intervalIntegral.integral_finsetSum fun a _ => ?_).trans
      (Finset.sum_congr rfl fun a _ => ?_)
    · simpa only [mul_assoc] using (intervalIntegrable_blockFourier (continuous_coeffs (hf a) L)
        s.p s.j g 0 (2 * Real.pi)).const_mul (D a)
    · simp only [mul_assoc]
      exact intervalIntegral.integral_const_mul _ _

end Lift

/-! ## Functions of product form on the compact Levi subgroup -/

section Prod

variable {c : ℕ} (sz : Fin c → ℕ)

/-- `F(diag(κ)) = ∑_a C_a ∏_j y_{a,j}(κ_j)` for `κ ∈ ∏_j O(sz_j)`. -/
def IsProdForm (F : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ) {ι : Type*} [Fintype ι]
    (C : ι → ℂ) (y : ι → ∀ j, Langlands.GeneralLinear (sz j) ℝ → ℂ) : Prop :=
  ∀ κ : ∀ j, Langlands.GeneralLinear (sz j) ℝ, (∀ j, κ j ∈ unitaryCompact ℝ (sz j)) →
    F (blockDiagGL sz κ) = ∑ a, C a * ∏ j, y a j (κ j)

theorem prod_apply_update {β : Fin c → Type*} (f : ∀ j, β j → ℂ) (g : ∀ j, β j) (i : Fin c)
    (v : β i) :
    ∏ j, f j (Function.update g i v j) = f i v * ∏ j ∈ Finset.univ \ {i}, f j (g j) := by
  simp_rw [Function.apply_update f g i v]
  exact Finset.prod_update_of_mem (Finset.mem_univ i) _ _

variable {sz}

theorem update_mem_unitaryCompact {κ : ∀ j, Langlands.GeneralLinear (sz j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz j)) {i : Fin c} {x : Langlands.GeneralLinear (sz i) ℝ}
    (hx : x ∈ unitaryCompact ℝ (sz i)) (j : Fin c) :
    Function.update κ i x j ∈ unitaryCompact ℝ (sz j) := by
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact hx
  · rw [Function.update_of_ne hj]
    exact hκ j

/-- Taking the coefficients along lifted slots of one block replaces the factors of that
block by their coefficients. -/
theorem isProdForm_coeffs {F : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ} {ι : Type*}
    [Fintype ι] {C : ι → ℂ} {y : ι → ∀ j, Langlands.GeneralLinear (sz j) ℝ → ℂ}
    (hF : IsProdForm sz F C y) (hy : ∀ a j, Continuous (y a j)) (i : Fin c)
    (L : List (Slot (sz i))) :
    IsProdForm sz (coeffs (L.map (liftSlot sz i)) F) C
      (fun a => Function.update (y a) i (coeffs L (y a i))) := by
  intro κ hκ
  rw [coeffs_liftSlots]
  have hcongr : ∀ x ∈ unitaryCompact ℝ (sz i), F (blockDiagGL sz (Function.update κ i x)) =
      ∑ a, (C a * ∏ j ∈ Finset.univ \ {i}, y a j (κ j)) * y a i x := by
    intro x hx
    rw [hF _ (update_mem_unitaryCompact hκ hx)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [prod_apply_update (fun j => y a j) κ i x]
    ring
  rw [coeffs_congr_of_eqOn hcongr L (κ i) (hκ i), coeffs_sum_mul _ (fun a => hy a i)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := prod_apply_update (fun j (h : Langlands.GeneralLinear (sz j) ℝ → ℂ) => h (κ j)) (y a)
    i (coeffs L (y a i))
  rw [e]
  ring

/-- The global list of slots of the class lists `Ls i`, in the order of the classes in `l`. -/
def globalSlots (Ls : ∀ i, List (Slot (sz i))) (l : List (Fin c)) : List (Slot (∑ j, sz j)) :=
  (l.map fun i => (Ls i).map (liftSlot sz i)).flatten

theorem isProdForm_globalSlots {F : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ} {ι : Type*}
    [Fintype ι] {C : ι → ℂ} {y : ι → ∀ j, Langlands.GeneralLinear (sz j) ℝ → ℂ}
    (hF : IsProdForm sz F C y) (hy : ∀ a j, Continuous (y a j)) (Ls : ∀ i, List (Slot (sz i))) :
    ∀ l : List (Fin c), l.Nodup →
      IsProdForm sz (coeffs (globalSlots Ls l) F) C
        (fun a j => if j ∈ l then coeffs (Ls j) (y a j) else y a j)
  | [], _ => by
    intro κ hκ
    simp only [globalSlots, List.map_nil, List.flatten_nil, coeffs, List.not_mem_nil,
      ↓reduceIte]
    exact hF κ hκ
  | i :: l, hl => by
    have hl' := List.nodup_cons.mp hl
    have ih := isProdForm_globalSlots hF hy Ls l hl'.2
    have hy' : ∀ a j, Continuous (if j ∈ l then coeffs (Ls j) (y a j) else y a j) := by
      intro a j
      split_ifs
      · exact continuous_coeffs (hy a j) _
      · exact hy a j
    have step := isProdForm_coeffs ih hy' i (Ls i)
    have e : (fun a => Function.update (fun j => if j ∈ l then coeffs (Ls j) (y a j) else y a j) i
        (coeffs (Ls i) (if i ∈ l then coeffs (Ls i) (y a i) else y a i))) =
        fun a j => if j ∈ i :: l then coeffs (Ls j) (y a j) else y a j := by
      funext a j
      by_cases hj : j = i
      · subst hj
        simp [hl'.1]
      · simp [hj]
    rw [e] at step
    simpa only [globalSlots, List.map_cons, List.flatten_cons, coeffs_append] using step

/-- **Product coefficients.** For `F` of product form, the coefficients along the global list
of the class lists `Ls i` at `diag(κ)` are the corresponding sums of products of the class
coefficients. -/
theorem coeffs_globalSlots {F : Langlands.GeneralLinear (∑ j, sz j) ℝ → ℂ} {ι : Type*}
    [Fintype ι] {C : ι → ℂ} {y : ι → ∀ j, Langlands.GeneralLinear (sz j) ℝ → ℂ}
    (hF : IsProdForm sz F C y) (hy : ∀ a j, Continuous (y a j)) (Ls : ∀ i, List (Slot (sz i)))
    {κ : ∀ j, Langlands.GeneralLinear (sz j) ℝ} (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz j)) :
    coeffs (globalSlots Ls (List.finRange c)) F (blockDiagGL sz κ) =
      ∑ a, C a * ∏ j, coeffs (Ls j) (y a j) (κ j) := by
  rw [isProdForm_globalSlots hF hy Ls _ (List.nodup_finRange c) κ hκ]
  simp only [List.mem_finRange, ↓reduceIte]

end Prod

/-! ## Spans of products -/

section Dec

universe u

/-- A finite-dimensional space of functions has an interpolation formula `v = ∑_g v(x_g) f_g`
with finitely many points `x_g` and functions `f_g` of the space. -/
theorem exists_interp {α : Type u} (W : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → α) (f : ι → α → ℂ), (∀ g, f g ∈ W) ∧
      ∀ v ∈ W, v = ∑ g, v (x g) • f g := by
  classical
  let b := Module.finBasis ℂ W
  have hsep : ∀ s ∈ W, (∀ y : α, (LinearMap.proj y : (α → ℂ) →ₗ[ℂ] ℂ) s = 0) → s = 0 :=
    fun s _ h => funext h
  have hL : ∀ l, ∃ L : (α → ℂ) →ₗ[ℂ] ℂ, L.comp W.subtype = b.coord l :=
    fun l => LinearMap.exists_extend (b.coord l)
  choose L hL using hL
  have hc := fun l => exists_sum_of_separating
    (fun y : α => (LinearMap.proj y : (α → ℂ) →ₗ[ℂ] ℂ)) W hsep (L l)
  choose m p c hc using hc
  refine ⟨Σ l, Fin (m l), inferInstance, fun g => p g.1 g.2,
    fun g => c g.1 g.2 • (b g.1 : α → ℂ), fun g => W.smul_mem _ (b g.1).2, fun v hv => ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  rw [Fintype.sum_sigma]
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h3 : b.repr ⟨v, hv⟩ l = ∑ g, c l g * v (p l g) := by
    have e := congrArg (fun T : W →ₗ[ℂ] ℂ => T ⟨v, hv⟩) (hL l)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at e
    rw [← e, hc l v hv]
    rfl
  rw [h3, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [smul_smul, mul_comm]

variable {c : ℕ}

/-- The span of the functions `κ ↦ ∏_j f_j(κ_j)` with `f_j ∈ W_j`. -/
def prodSpan {α : Fin c → Type u} (W : ∀ j, Submodule ℂ (α j → ℂ)) :
    Submodule ℂ ((∀ j, α j) → ℂ) :=
  Submodule.span ℂ {F | ∃ f : ∀ j, α j → ℂ, (∀ j, f j ∈ W j) ∧ F = fun κ => ∏ j, f j (κ j)}

theorem consMul_mem {α : Fin (c + 1) → Type u} {W : ∀ j, Submodule ℂ (α j → ℂ)}
    {h : α 0 → ℂ} (hh : h ∈ W 0) {G : (∀ j : Fin c, α j.succ) → ℂ}
    (hG : G ∈ prodSpan fun j => W j.succ) :
    (fun κ : ∀ j, α j => h (κ 0) * G (Fin.tail κ)) ∈ prodSpan W := by
  let Φ : ((∀ j : Fin c, α j.succ) → ℂ) →ₗ[ℂ] ((∀ j, α j) → ℂ) :=
    { toFun := fun G κ => h (κ 0) * G (Fin.tail κ)
      map_add' := fun G G' => by
        funext κ
        simp only [Pi.add_apply, mul_add]
      map_smul' := fun r G => by
        funext κ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hle : (prodSpan fun j => W j.succ) ≤ (prodSpan W).comap Φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    refine Submodule.subset_span ⟨Fin.cons (α := fun j => α j → ℂ) h f, fun j => ?_, ?_⟩
    · induction j using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using hh
      | succ j => simpa only [Fin.cons_succ] using hf j
    · funext κ
      show h (κ 0) * ∏ j, f j (Fin.tail κ j) =
        ∏ j, Fin.cons (α := fun j => α j → ℂ) h f j (κ j)
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
  exact hle hG

/-- **Span of products.** A function on `∏_j α_j` all of whose coordinate slices lie in
finite-dimensional spaces `W_j` lies in the span of the products of elements of the `W_j`. -/
theorem mem_prodSpan : ∀ {c : ℕ} {α : Fin c → Type u} (W : ∀ j, Submodule ℂ (α j → ℂ))
    [∀ j, FiniteDimensional ℂ (W j)] (F : (∀ j, α j) → ℂ),
    (∀ κ j, (fun x => F (Function.update κ j x)) ∈ W j) → F ∈ prodSpan W
  | 0, α, W, _, F, _ => by
    have hκ : ∀ κ : ∀ j : Fin 0, α j, κ = fun j => j.elim0 := fun κ => funext fun j => j.elim0
    have e : F = F (fun j => j.elim0) • fun κ : ∀ j : Fin 0, α j =>
        ∏ j, (fun j : Fin 0 => j.elim0 : ∀ j, α j → ℂ) j (κ j) := by
      funext κ
      rw [hκ κ]
      simp
    rw [e]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun j => j.elim0, fun j => j.elim0, rfl⟩)
  | c + 1, α, W, _, F, hF => by
    obtain ⟨ι, _, x, f, hf, hv⟩ := exists_interp (W 0)
    have hG : ∀ g, (fun t : ∀ j : Fin c, α j.succ => F (Fin.cons (x g) t)) ∈
        prodSpan fun j => W j.succ := by
      intro g
      refine mem_prodSpan (fun j => W j.succ) _ fun t j => ?_
      have h := hF (Fin.cons (x g) t) j.succ
      simpa only [Fin.cons_update] using h
    have hF' : F = ∑ g, fun κ : ∀ j, α j => f g (κ 0) * F (Fin.cons (x g) (Fin.tail κ)) := by
      funext κ
      have h0 : (fun y => F (Fin.cons y (Fin.tail κ))) ∈ W 0 := by
        have h := hF (Fin.cons (κ 0) (Fin.tail κ)) 0
        simpa only [Fin.update_cons_zero] using h
      have h1 := congrFun (hv _ h0) (κ 0)
      simp only [Fin.cons_self_tail] at h1
      rw [h1, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hF']
    exact Submodule.sum_mem _ fun g _ => consMul_mem (hf g) (hG g)

end Dec

/-! ## Product form of the dual space on the compact Levi subgroup -/

section App

open RealPrincipalSeriesDuality RealLeviDuality

variable {c : ℕ} {dss : Fin c → List RealBlock}

theorem blockDiagGL_update_mem_unitaryCompact {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) (i : Fin c) :
    blockDiagGL (sz dss) (Function.update κ i 1) ∈ unitaryCompact ℝ (∑ j, sz dss j) :=
  blockDiagGL_mem_unitaryCompact (sz := sz dss)
    (fun j => ⟨Function.update κ i 1 j, update_mem_unitaryCompact hκ (one_mem _) j⟩)

/-- `diag(κ_0, …, 1, …, κ_{c-1})` (with `1` in the block `i`) as an element of `O(N)`. -/
def mK {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) (i : Fin c) :
    Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ :=
  ⟨(blockDiagGL (sz dss) (Function.update κ i 1) : Matrix _ _ ℝ),
    blockDiagGL_update_mem_unitaryCompact hκ i⟩

theorem toUnits_mK {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) (i : Fin c) :
    (Unitary.toUnits (mK hκ i) : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) =
      blockDiagGL (sz dss) (Function.update κ i 1) :=
  toUnits_mk _ (blockDiagGL_update_mem_unitaryCompact hκ i)

/-- The values `x ↦ u(diag(κ_0, …, x, …, κ_{c-1}))` are the slice of a translate of `u`. -/
theorem apply_blockDiagGL_update (u : DualSpace (∑ j, sz dss j) (flat dss))
    {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) (i : Fin c)
    (x : Langlands.GeneralLinear (sz dss i) ℝ) :
    (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
        (blockDiagGL (sz dss) (Function.update κ i x)) =
      (slice dss i (repG dss (mK hκ i) u) : Langlands.GeneralLinear (sz dss i) ℝ → ℂ) x := by
  show _ = (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
    (emb (sz dss) i x * (Unitary.toUnits (mK hκ i) : Langlands.GeneralLinear (∑ j, sz dss j) ℝ))
  rw [toUnits_mK, emb_mul_blockDiagGL_update]

/-- Restriction of functions to `O(n)`. -/
def resK (n : ℕ) (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) :
    V →ₗ[ℂ] (unitaryCompact ℝ n → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (Subtype.val : unitaryCompact ℝ n → Langlands.GeneralLinear n ℝ)).comp
    V.subtype

/-- **Product form.** On `K_M = ∏_j O(sz_j)` every element of the global dual space is a finite
sum of products of elements of the class dual spaces. -/
theorem exists_isProdForm (u : DualSpace (∑ j, sz dss j) (flat dss)) :
    ∃ (n : ℕ) (C : Fin n → ℂ) (w : Fin n → ∀ j, DualSpace (sz dss j) (cl dss j)),
      IsProdForm (sz dss) u C fun a j => (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) := by
  classical
  let O := FiniteVectors.orbitSpan (repG dss) u
  have : FiniteDimensional ℂ O := kFiniteRep_isFiniteVector _ _ u
  let W : ∀ j, Submodule ℂ (unitaryCompact ℝ (sz dss j) → ℂ) := fun j =>
    O.map ((resK (sz dss j) (DualSpace (sz dss j) (cl dss j))).comp (slice dss j))
  have hW : ∀ j, FiniteDimensional ℂ (W j) := fun j => inferInstance
  let F : (∀ j, unitaryCompact ℝ (sz dss j)) → ℂ := fun κ =>
    (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (blockDiagGL (sz dss) fun j => (κ j : Langlands.GeneralLinear (sz dss j) ℝ))
  have hF : ∀ κ j, (fun x => F (Function.update κ j x)) ∈ W j := by
    intro κ j
    refine ⟨repG dss (mK (κ := fun j => (κ j : Langlands.GeneralLinear (sz dss j) ℝ))
      (fun j => (κ j).2) j) u, FiniteVectors.action_mem_orbitSpan _ _ _, ?_⟩
    funext x
    show (slice dss j (repG dss _ u) : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) x =
      F (Function.update κ j x)
    rw [← apply_blockDiagGL_update]
    show _ = (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (blockDiagGL (sz dss) fun i => (Function.update κ j x i : Langlands.GeneralLinear (sz dss i) ℝ))
    refine congrArg (fun g => (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (blockDiagGL (sz dss) g)) (funext fun i => ?_)
    by_cases hi : i = j
    · subst hi
      simp
    · simp [hi]
  obtain ⟨n, C, g, hg⟩ := Submodule.mem_span_set'.mp (mem_prodSpan W F hF)
  choose y hy hgy using fun a => (g a).2
  choose v _ hvy using fun a j => (Submodule.mem_map.mp (hy a j))
  refine ⟨n, C, fun a j => slice dss j (v a j), fun κ hκ => ?_⟩
  have e := congrFun hg (fun j => ⟨κ j, hκ j⟩)
  show F (fun j => ⟨κ j, hκ j⟩) = _
  rw [← e, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.smul_apply, hgy a, smul_eq_mul]
  refine congrArg (C a * ·) (Finset.prod_congr rfl fun j _ => ?_)
  rw [← hvy a j]
  rfl

end App

/-! ## Acting in one class -/

section Step

open RealPrincipalSeriesDuality RealLeviDuality

variable {c : ℕ} {dss : Fin c → List RealBlock}

/-- The free algebra generators of the class `i`. -/
abbrev Gens (dss : Fin c → List RealBlock) (i : Fin c) : Type :=
  Matrix.unitaryGroup (Fin (sz dss i)) ℝ ⊕ (ℂ ⊗[ℝ] Matrix (Fin (sz dss i)) (Fin (sz dss i)) ℝ)

theorem slice_repG_eq_sum {u : DualSpace (∑ j, sz dss j) (flat dss)} {n : ℕ} {C : Fin n → ℂ}
    {w : Fin n → ∀ j, DualSpace (sz dss j) (cl dss j)}
    (hu : IsProdForm (sz dss) u C fun a j => (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ))
    {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) (i : Fin c) :
    slice dss i (repG dss (mK hκ i) u) =
      ∑ a, (C a * ∏ j ∈ Finset.univ \ {i},
        (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) (κ j)) • w a i := by
  apply Subtype.ext
  have hmem := (∑ a, (C a * ∏ j ∈ Finset.univ \ {i},
    (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) (κ j)) • w a i :
      DualSpace (sz dss i) (cl dss i)).2.1
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries (slice dss i _).2.1 hmem
    fun x hx => ?_
  have h1 := hu _ (update_mem_unitaryCompact hκ hx)
  beta_reduce at h1
  rw [← apply_blockDiagGL_update, h1, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have e := prod_apply_update (fun j => (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ)) κ i x
  beta_reduce at e
  rw [e]
  ring

/-- Acting by the free algebra of the class `i` on the global dual space acts on the factors of
the class `i` of a product form. -/
theorem isProdForm_lift {u : DualSpace (∑ j, sz dss j) (flat dss)} {n : ℕ} {C : Fin n → ℂ}
    {w : Fin n → ∀ j, DualSpace (sz dss j) (cl dss j)}
    (hu : IsProdForm (sz dss) u C fun a j => (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ))
    (i : Fin c) (b : FreeAlgebra ℂ (Gens dss i)) :
    IsProdForm (sz dss) (FreeAlgebra.lift ℂ (gensG dss i) b u) C fun a j =>
      (Function.update (w a) i (FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss i) (lieC dss i))
        b (w a i)) j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) := by
  intro κ hκ
  beta_reduce
  have h1 := apply_blockDiagGL_update (FreeAlgebra.lift ℂ (gensG dss i) b u) hκ i (κ i)
  rw [Function.update_eq_self] at h1
  rw [h1, repG_comm_lift (toUnits_mK hκ i), slice_lift, slice_repG_eq_sum hu hκ i, map_sum,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have e := prod_apply_update
    (fun j (h : DualSpace (sz dss j) (cl dss j)) => (h : Langlands.GeneralLinear (sz dss j) ℝ → ℂ)
      (κ j)) (w a) i
    (FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss i) (lieC dss i)) b (w a i))
  beta_reduce at e
  rw [e]
  ring

/-- Apply `b_i` in each class `i` of the list `l` (the last class of `l` first). -/
def applyAll (b : ∀ i, FreeAlgebra ℂ (Gens dss i)) :
    List (Fin c) → DualSpace (∑ j, sz dss j) (flat dss) → DualSpace (∑ j, sz dss j) (flat dss)
  | [], u => u
  | i :: l, u => FreeAlgebra.lift ℂ (gensG dss i) (b i) (applyAll b l u)

theorem isProdForm_applyAll {u : DualSpace (∑ j, sz dss j) (flat dss)} {n : ℕ} {C : Fin n → ℂ}
    {w : Fin n → ∀ j, DualSpace (sz dss j) (cl dss j)}
    (hu : IsProdForm (sz dss) u C fun a j => (w a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ))
    (b : ∀ i, FreeAlgebra ℂ (Gens dss i)) :
    ∀ l : List (Fin c), l.Nodup →
      IsProdForm (sz dss) (applyAll b l u) C fun a j =>
        ((if j ∈ l then FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss j) (lieC dss j)) (b j)
          (w a j) else w a j : DualSpace (sz dss j) (cl dss j)) :
            Langlands.GeneralLinear (sz dss j) ℝ → ℂ)
  | [], _ => by
    simpa only [applyAll, List.not_mem_nil, ↓reduceIte] using hu
  | i :: l, hl => by
    have hl' := List.nodup_cons.mp hl
    have step := isProdForm_lift (isProdForm_applyAll hu b l hl'.2) i (b i)
    have e : ∀ a, Function.update (fun j => if j ∈ l then FreeAlgebra.lift ℂ
        (GKModuleDensity.gens (repC dss j) (lieC dss j)) (b j) (w a j) else w a j) i
        (FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss i) (lieC dss i)) (b i)
          (if i ∈ l then FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss i) (lieC dss i)) (b i)
            (w a i) else w a i)) =
        fun j => if j ∈ i :: l then FreeAlgebra.lift ℂ
          (GKModuleDensity.gens (repC dss j) (lieC dss j)) (b j) (w a j) else w a j := by
      intro a
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hl'.1]
      · simp [hj]
    simp only [e] at step
    exact step

theorem applyAll_mem (b : ∀ i, FreeAlgebra ℂ (Gens dss i))
    (U : Submodule ℂ (DualSpace (∑ j, sz dss j) (flat dss)))
    (hU : ∀ i x, ∀ v ∈ U, gensG dss i x v ∈ U) :
    ∀ (l : List (Fin c)) {u : DualSpace (∑ j, sz dss j) (flat dss)}, u ∈ U → applyAll b l u ∈ U
  | [], _, hu => hu
  | i :: l, _, hu => lift_mem _ U (hU i) (b i) (applyAll_mem b U hU l hu)

end Step

end RealLeviProducts

end Langlands.Archimedean
