import Langlands.WeilDeligne.BlockStatements
import Langlands.WeilDeligne.BlockEquivalences
import Langlands.WeilDeligne.BlockMatching
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Uniqueness of block decompositions over `ℂ`

Proof of `Langlands.WeilDeligneRepresentation.Blocks.DecompositionUniqueness`.
-/

noncomputable section

open scoped TensorProduct DirectSum

namespace Langlands.WeilDeligneRepresentation.Blocks.DecompositionUniquenessProof

universe uG uP uU uV uW uι

open Representation

variable {G : Type uG} [Group G]

section HomInto

variable {P : Type uP} {V : Type uV} {W : Type uW}
  [AddCommGroup P] [Module ℂ P] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Intertwiners from `π` to `ρ` whose image lies in `S`. -/
def homInto (π : Representation ℂ G P) (ρ : Representation ℂ G V) (S : Submodule ℂ V) :
    Submodule ℂ (π.IntertwiningMap ρ) where
  carrier := {f | ∀ v, f v ∈ S}
  add_mem' hf hg v := S.add_mem (hf v) (hg v)
  zero_mem' _ := S.zero_mem
  smul_mem' c _ hf v := S.smul_mem c (hf v)

theorem mem_homInto {π : Representation ℂ G P} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    (f : π.IntertwiningMap ρ) : f ∈ homInto π ρ S ↔ ∀ v, f v ∈ S :=
  Iff.rfl

/-- An intertwiner from a linear map commuting with the actions. -/
def mkIntertwining {π : Representation ℂ G P} {ρ : Representation ℂ G V} (f : P →ₗ[ℂ] V)
    (hf : ∀ g v, f (π g v) = ρ g (f v)) : π.IntertwiningMap ρ :=
  ⟨f, fun g => LinearMap.ext (hf g)⟩

@[simp]
theorem mkIntertwining_apply {π : Representation ℂ G P} {ρ : Representation ℂ G V}
    (f : P →ₗ[ℂ] V) (hf : ∀ g v, f (π g v) = ρ g (f v)) (v : P) :
    mkIntertwining f hf v = f v :=
  rfl

/-- The layer `ker N ⊓ range N^j` of an endomorphism. -/
def layer (N : Module.End ℂ V) (j : ℕ) : Submodule ℂ V :=
  LinearMap.ker N ⊓ LinearMap.range (N ^ j)

/-- The dimension of the space of intertwiners from `π` into the `j`-th layer of `N`. -/
def count (π : Representation ℂ G P) (ρ : Representation ℂ G V) (N : Module.End ℂ V)
    (j : ℕ) : ℕ :=
  Module.finrank ℂ (homInto π ρ (layer N j))

/-- Postcomposition with an equivalence of representations. -/
def postcomp (π : Representation ℂ G P) {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    π.IntertwiningMap ρ ≃ₗ[ℂ] π.IntertwiningMap σ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- Postcomposition with an equivalence matching `S` with `T` identifies intertwiners
into `S` with intertwiners into `T`. -/
def homIntoCongr (π : Representation ℂ G P) {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : ρ.Equiv σ) {S : Submodule ℂ V} {T : Submodule ℂ W}
    (h : ∀ v, v ∈ S ↔ e v ∈ T) : homInto π ρ S ≃ₗ[ℂ] homInto π σ T where
  toFun f := ⟨postcomp π e f.1, fun v => (h _).1 (f.2 v)⟩
  invFun f := ⟨(postcomp π e).symm f.1, fun v => (h _).2 (by
    simpa [postcomp, IntertwiningMap.comp_apply] using f.2 v)⟩
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- An equivalence commuting with two endomorphisms commutes with their powers. -/
theorem equiv_pow_apply {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) {N : Module.End ℂ V} {N' : Module.End ℂ W}
    (hN : ∀ v, e (N v) = N' (e v)) (j : ℕ) (v : V) :
    e ((N ^ j) v) = (N' ^ j) (e v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, hN, ← Module.End.mul_apply, ← pow_succ]

theorem mem_layer_congr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) {N : Module.End ℂ V} {N' : Module.End ℂ W}
    (hN : ∀ v, e (N v) = N' (e v)) (j : ℕ) (v : V) :
    v ∈ layer N j ↔ e v ∈ layer N' j := by
  simp only [layer, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · rintro ⟨h0, w, rfl⟩
    refine ⟨?_, e w, (equiv_pow_apply e hN j w).symm⟩
    rw [← hN, h0, map_zero]
  · rintro ⟨h0, w, hw⟩
    refine ⟨?_, e.symm w, ?_⟩
    · apply EquivLike.injective e
      rw [hN, h0, map_zero]
    · apply EquivLike.injective e
      rw [equiv_pow_apply e hN, Representation.Equiv.apply_symm_apply, hw]

/-- The count is invariant under equivalences commuting with the endomorphisms. -/
theorem count_congr (π : Representation ℂ G P) {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : ρ.Equiv σ) {N : Module.End ℂ V} {N' : Module.End ℂ W}
    (hN : ∀ v, e (N v) = N' (e v)) (j : ℕ) : count π ρ N j = count π σ N' j :=
  (homIntoCongr π e (mem_layer_congr e hN j)).finrank_eq

open Classical in
/-- Schur's lemma over `ℂ`, for irreducible representations on possibly different
carrier universes. -/
theorem finrank_intertwiningMap_irreducible [FiniteDimensional ℂ P]
    (π : Representation ℂ G P) (ρ : Representation ℂ G V) [π.IsIrreducible]
    [ρ.IsIrreducible] :
    Module.finrank ℂ (π.IntertwiningMap ρ) = if Nonempty (π.Equiv ρ) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨e⟩ := h
    rw [← Representation.IsIrreducible.finrank_intertwiningMap_self π]
    exact (postcomp π e.symm).finrank_eq
  · have : IsEmpty (π.Equiv ρ) := not_nonempty_iff.mp h
    exact Module.finrank_zero_of_subsingleton

end HomInto

section PiModel

variable {P : Type uP} {U : Type uU} [AddCommGroup P] [Module ℂ P] [AddCommGroup U] [Module ℂ U]

/-- The coordinate model of a block: weight `ν^k` on the `k`-th copy of `σ`. -/
def piAction (ν : G →* ℂˣ) (σ : Representation ℂ G U) (m : ℕ) :
    Representation ℂ G (Fin m → U) where
  toFun g := LinearMap.pi fun k => ((ν g : ℂ) ^ k.val) • (σ g ∘ₗ LinearMap.proj k)
  map_one' := by
    apply LinearMap.ext
    intro y
    funext k
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro y
    funext k
    simp [mul_pow, smul_smul, Module.End.mul_apply]

@[simp]
theorem piAction_apply (ν : G →* ℂˣ) (σ : Representation ℂ G U) (m : ℕ) (g : G)
    (y : Fin m → U) (k : Fin m) : piAction ν σ m g y k = (ν g : ℂ) ^ k.val • σ g (y k) :=
  rfl

variable (U) in
/-- The coordinate model of the raising monodromy. -/
def piShift (m : ℕ) : Module.End ℂ (Fin m → U) :=
  LinearMap.pi fun j =>
    if h : 0 < j.val then LinearMap.proj ⟨j.val - 1, by omega⟩ else 0

theorem piShift_apply (m : ℕ) (y : Fin m → U) (j : Fin m) :
    piShift U m y j = if h : 0 < j.val then y ⟨j.val - 1, by omega⟩ else 0 := by
  by_cases h : 0 < j.val <;> simp [piShift, h]

theorem piShift_pow_apply (m j : ℕ) (y : Fin m → U) (k : Fin m) :
    (piShift U m ^ j) y k = if h : j ≤ k.val then y ⟨k.val - j, by omega⟩ else 0 := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, piShift_apply]
    by_cases hk : 0 < k.val
    · rw [dite_eq_left hk, ih]
      by_cases hj : j + 1 ≤ k.val
      · rw [dite_eq_left (show j ≤ k.val - 1 by omega), dite_eq_left hj]
        congr 1
        ext
        change k.val - 1 - j = k.val - (j + 1)
        omega
      · rw [dite_eq_right (show ¬ j ≤ k.val - 1 by omega), dite_eq_right hj]
    · rw [dite_eq_right hk, dite_eq_right (show ¬ j + 1 ≤ k.val by omega)]

theorem piShift_eq_zero_iff (n : ℕ) (y : Fin (n + 1) → U) :
    piShift U (n + 1) y = 0 ↔ ∀ k : Fin (n + 1), k.val < n → y k = 0 := by
  constructor
  · intro h k hk
    have hv := congrFun h (⟨k.val + 1, by omega⟩ : Fin (n + 1))
    simpa [piShift_apply] using hv
  · intro h
    funext k
    rw [piShift_apply]
    split
    · exact h _ (by change k.val - 1 < n; omega)
    · rfl

/-- In length `n + 1`, the `j`-th layer is the kernel for `j ≤ n`. -/
theorem layer_piShift_of_le (n j : ℕ) (hj : j ≤ n) :
    layer (piShift U (n + 1)) j = LinearMap.ker (piShift U (n + 1)) := by
  apply inf_eq_left.mpr
  intro y hy
  rw [LinearMap.mem_ker, piShift_eq_zero_iff] at hy
  refine ⟨fun k => if k.val = n - j then y (Fin.last n) else 0, ?_⟩
  funext k
  rw [piShift_pow_apply]
  by_cases hk : k.val < n
  · rw [hy k hk]
    split
    · rw [ite_eq_right (show ¬ (k.val - j = n - j) by omega)]
    · rfl
  · have hkl : k = Fin.last n := Fin.ext (by simp; omega)
    subst hkl
    rw [dite_eq_left (show j ≤ (Fin.last n).val by simp; omega)]
    rw [ite_eq_left (by simp)]

/-- In length `n + 1`, the `j`-th layer vanishes for `j > n`. -/
theorem layer_piShift_of_lt (n j : ℕ) (hj : n < j) :
    layer (piShift U (n + 1)) j = ⊥ := by
  apply eq_bot_iff.mpr
  rintro y ⟨-, z, rfl⟩
  rw [Submodule.mem_bot]
  funext k
  rw [piShift_pow_apply, dite_eq_right (by omega)]
  rfl

theorem twist_apply (χ : G →* ℂˣ) (σ : Representation ℂ G U) (g : G) (u : U) :
    Langlands.twist χ σ g u = (χ g : ℂ) • σ g u :=
  rfl

/-- Intertwiners into the kernel of the shift are intertwiners into the top
coordinate, which carries the twist by `ν^n`. -/
def topEquiv (ν : G →* ℂˣ) (π : Representation ℂ G P) (σ : Representation ℂ G U) (n : ℕ) :
    homInto π (piAction ν σ (n + 1)) (LinearMap.ker (piShift U (n + 1))) ≃ₗ[ℂ]
      π.IntertwiningMap (Langlands.twist (ν ^ n) σ) where
  toFun f := mkIntertwining (LinearMap.proj (Fin.last n) ∘ₗ f.1.toLinearMap) (fun g v => by
      simp [twist_apply, IntertwiningMap.isIntertwining])
  invFun φ := ⟨mkIntertwining (LinearMap.single ℂ (fun _ => U) (Fin.last n) ∘ₗ φ.toLinearMap)
      (fun g v => by
        funext k
        by_cases hk : k = Fin.last n
        · subst hk
          simp [IntertwiningMap.isIntertwining, twist_apply]
        · simp [hk]), fun v => by
        rw [LinearMap.mem_ker, piShift_eq_zero_iff]
        intro k hk
        have hne : k ≠ Fin.last n := by
          intro h
          rw [h] at hk
          simp at hk
        simp [hne]⟩
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl
  left_inv f := by
    apply Subtype.ext
    ext v k
    have hf := f.2 v
    rw [LinearMap.mem_ker, piShift_eq_zero_iff] at hf
    change Pi.single (M := fun _ : Fin (n + 1) => U) (Fin.last n) (f.1 v (Fin.last n)) k =
      f.1 v k
    by_cases hk : k = Fin.last n
    · subst hk
      exact Pi.single_eq_same _ _
    · have hk' : k.val < n := by
        have := k.isLt
        have h2 : k.val ≠ n := fun h => hk (Fin.ext (by simpa using h))
        omega
      rw [Pi.single_eq_of_ne hk, hf k hk']
  right_inv φ := by
    ext v
    exact Pi.single_eq_same (M := fun _ => U) (Fin.last n) (φ v)

end PiModel

section Block

variable (ν : G →* ℂˣ)

section Coordinates

variable {U : Type uU} [AddCommGroup U] [Module ℂ U]

theorem piScalarRight_tmul_apply (m : ℕ) (x : U) (f : Fin m → ℂ) (k : Fin m) :
    TensorProduct.piScalarRight ℂ ℂ U (Fin m) (x ⊗ₜ[ℂ] f) k = f k • x := by
  simp

theorem piScalarRight_action (σ : Representation ℂ G U) (m : ℕ) (g : G) (x : U)
    (f : Fin m → ℂ) :
    TensorProduct.piScalarRight ℂ ℂ U (Fin m) (σ g x ⊗ₜ[ℂ] Special.action ν m g f) =
      piAction ν σ m g (TensorProduct.piScalarRight ℂ ℂ U (Fin m) (x ⊗ₜ[ℂ] f)) := by
  funext k
  simp only [piScalarRight_tmul_apply, piAction_apply, Special.action_apply, map_smul, smul_smul]

theorem piScalarRight_raising (m : ℕ) (x : U) (f : Fin m → ℂ) :
    TensorProduct.piScalarRight ℂ ℂ U (Fin m) (x ⊗ₜ[ℂ] Special.raising ℂ m f) =
      piShift U m (TensorProduct.piScalarRight ℂ ℂ U (Fin m) (x ⊗ₜ[ℂ] f)) := by
  funext k
  rw [piShift_apply, piScalarRight_tmul_apply, Special.raising_apply]
  split
  · rw [piScalarRight_tmul_apply]
  · simp

end Coordinates

/-- The block `σ ⊗ S_m` is equivalent to its coordinate model. -/
def blockEquivPi (σ : FiniteRepresentation.{0, uG, uV} ℂ G) (m : ℕ) :
    (block ν σ m).representation.Equiv (piAction ν σ.representation m) :=
  Representation.Equiv.mk (TensorProduct.piScalarRight ℂ ℂ σ (Fin m)) (fun g =>
    TensorProduct.ext' (M := σ) (N := Fin m → ℂ) fun x f =>
      piScalarRight_action ν σ.representation m g x f)

theorem blockEquivPi_monodromy (σ : FiniteRepresentation.{0, uG, uV} ℂ G) (m : ℕ)
    (v : block ν σ m) :
    blockEquivPi ν σ m ((block ν σ m).monodromy v) = piShift σ m (blockEquivPi ν σ m v) := by
  have h : (TensorProduct.piScalarRight ℂ ℂ σ (Fin m)).toLinearMap ∘ₗ
      (block ν σ m).monodromy =
      piShift σ m ∘ₗ (TensorProduct.piScalarRight ℂ ℂ σ (Fin m)).toLinearMap :=
    TensorProduct.ext' (M := σ) (N := Fin m → ℂ) fun x f =>
      (congrArg (TensorProduct.piScalarRight ℂ ℂ σ (Fin m))
        (block_monodromy_tmul ν σ m x f)).trans (piScalarRight_raising m x f)
  exact LinearMap.congr_fun h v

end Block


section DirectSumCount

variable {P : Type uP} [AddCommGroup P] [Module ℂ P]
  {ι : Type uι} [Fintype ι] [DecidableEq ι] {V : ι → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem homInto_bot (π : Representation ℂ G P) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : homInto π ρ ⊥ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  rw [Submodule.mem_bot]
  ext v
  exact (Submodule.mem_bot ℂ).mp (hf v)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_layer_lmap (N : ∀ i, Module.End ℂ (V i)) (j : ℕ) (x : ⨁ i, V i) :
    x ∈ layer (DirectSum.lmap N) j ↔ ∀ i, x i ∈ layer (N i) j := by
  simp only [layer, Submodule.mem_inf, lmap_pow, DirectSum.ker_lmap, DirectSum.range_lmap,
    Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
    DirectSum.coeFnLinearMap_apply]
  exact forall_and.symm

omit [DecidableEq ι] in
theorem linearEquivFunOnFintype_symm_apply' (y : ∀ i, V i) (i : ι) :
    (DirectSum.linearEquivFunOnFintype ℂ ι V).symm y i = y i := by
  simpa using congrFun ((DirectSum.linearEquivFunOnFintype ℂ ι V).apply_symm_apply y) i

/-- Intertwiners into a direct sum are families of intertwiners into the summands. -/
def homIntoDirectSum (π : Representation ℂ G P) (ρ : ∀ i, Representation ℂ G (V i))
    (S : ∀ i, Submodule ℂ (V i)) (T : Submodule ℂ (⨁ i, V i))
    (hT : ∀ x, x ∈ T ↔ ∀ i, x i ∈ S i) :
    homInto π (Representation.directSum ρ) T ≃ₗ[ℂ] ∀ i, homInto π (ρ i) (S i) where
  toFun f i := ⟨mkIntertwining (DirectSum.component ℂ ι V i ∘ₗ f.1.toLinearMap)
      (fun g v => by
        change f.1 (π g v) i = ρ i g (f.1 v i)
        rw [IntertwiningMap.isIntertwining]
        rfl), fun v => (hT _).1 (f.2 v) i⟩
  invFun φ := ⟨mkIntertwining ((DirectSum.linearEquivFunOnFintype ℂ ι V).symm.toLinearMap ∘ₗ
      LinearMap.pi fun i => (φ i).1.toLinearMap) (fun g v => by
        apply DirectSum.ext
        intro i
        change (DirectSum.linearEquivFunOnFintype ℂ ι V).symm (fun i => (φ i).1 (π g v)) i =
          ρ i g ((DirectSum.linearEquivFunOnFintype ℂ ι V).symm (fun i => (φ i).1 v) i)
        rw [linearEquivFunOnFintype_symm_apply', linearEquivFunOnFintype_symm_apply',
          IntertwiningMap.isIntertwining]),
    fun v => (hT _).2 fun i => by
      change (DirectSum.linearEquivFunOnFintype ℂ ι V).symm (fun i => (φ i).1 v) i ∈ S i
      rw [linearEquivFunOnFintype_symm_apply']
      exact (φ i).2 v⟩
  map_add' f g := by
    funext i
    apply Subtype.ext
    ext v
    rfl
  map_smul' c f := by
    funext i
    apply Subtype.ext
    ext v
    rfl
  left_inv f := by
    apply Subtype.ext
    ext v i
    change (DirectSum.linearEquivFunOnFintype ℂ ι V).symm (fun i => f.1 v i) i = f.1 v i
    rw [linearEquivFunOnFintype_symm_apply']
  right_inv φ := by
    funext i
    apply Subtype.ext
    ext v
    change (DirectSum.linearEquivFunOnFintype ℂ ι V).symm (fun i => (φ i).1 v) i = (φ i).1 v
    rw [linearEquivFunOnFintype_symm_apply']

omit [DecidableEq ι] in
/-- The count is additive over finite direct sums. -/
theorem count_directSum (π : Representation ℂ G P) [FiniteDimensional ℂ P]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, FiniteDimensional ℂ (V i)]
    (N : ∀ i, Module.End ℂ (V i)) (j : ℕ) :
    count π (Representation.directSum ρ) (DirectSum.lmap N) j = ∑ i, count π (ρ i) (N i) j := by
  unfold count
  rw [(homIntoDirectSum π ρ _ _ (mem_layer_lmap N j)).finrank_eq, Module.finrank_pi_fintype]

end DirectSumCount

section Counting

variable (ν : G →* ℂˣ) {P : Type uP} [AddCommGroup P] [Module ℂ P]

/-- The count of a block of length `n + 1`: the Hom-dimension into the top twist in
layers `j ≤ n`, and zero above. -/
theorem count_block (π : Representation ℂ G P) [FiniteDimensional ℂ P]
    (σ : FiniteRepresentation.{0, uG, uV} ℂ G) (n j : ℕ) :
    count π (block ν σ (n + 1)).representation (block ν σ (n + 1)).monodromy j =
      if j ≤ n then
        Module.finrank ℂ (π.IntertwiningMap (Langlands.twist (ν ^ n) σ.representation))
      else 0 := by
  rw [count_congr π (blockEquivPi ν σ (n + 1)) (blockEquivPi_monodromy ν σ (n + 1)) j]
  unfold count
  split_ifs with hj
  · rw [layer_piShift_of_le n j hj]
    exact (topEquiv ν π σ.representation n).finrank_eq
  · rw [layer_piShift_of_lt n j (by omega), homInto_bot, finrank_bot]

theorem count_pair (π : Representation ℂ G P) [FiniteDimensional ℂ P]
    (d : BlockDatum.{0, uG, uV} ℂ G) (j : ℕ) :
    count π (d.pair ν).representation (d.pair ν).monodromy j =
      if j < d.length then
        Module.finrank ℂ (π.IntertwiningMap
          (Langlands.twist (ν ^ (d.length - 1)) d.representation.representation))
      else 0 := by
  obtain ⟨σ, m, hm⟩ := d
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h := count_block ν π σ n j
  simp only [Nat.lt_succ_iff]
  exact h

theorem count_directSum_pairs (π : Representation ℂ G P) [FiniteDimensional ℂ P] {k : ℕ}
    (d : Fin k → BlockDatum.{0, uG, uV} ℂ G) (j : ℕ) :
    count π (directSum fun i => (d i).pair ν).representation
        (directSum fun i => (d i).pair ν).monodromy j =
      ∑ i, count π ((d i).pair ν).representation ((d i).pair ν).monodromy j :=
  count_directSum π (fun i => ((d i).pair ν).representation) (fun i => ((d i).pair ν).monodromy) j

/-- Passing from layer `j` to layer `j + 1` drops exactly the blocks of length `j + 1`. -/
theorem count_succ (π : Representation ℂ G P) [FiniteDimensional ℂ P] {k : ℕ}
    (d : Fin k → BlockDatum.{0, uG, uV} ℂ G) (j : ℕ) :
    count π (directSum fun i => (d i).pair ν).representation
        (directSum fun i => (d i).pair ν).monodromy j =
      count π (directSum fun i => (d i).pair ν).representation
        (directSum fun i => (d i).pair ν).monodromy (j + 1) +
      ∑ i, if (d i).length = j + 1 then
        Module.finrank ℂ (π.IntertwiningMap
          (Langlands.twist (ν ^ j) (d i).representation.representation))
      else 0 := by
  rw [count_directSum_pairs, count_directSum_pairs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [count_pair, count_pair]
  by_cases h : (d i).length = j + 1
  · rw [h]
    simp
  · rw [ite_eq_right h, add_zero]
    by_cases h2 : j + 1 < (d i).length
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

open Classical in
/-- The multiplicity of `τ` among the blocks of length `j + 1`. -/
def mult {k : ℕ} (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (τ : FiniteRepresentation.{0, uG, uP} ℂ G) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (d i).length = j + 1 ∧
    Nonempty (FiniteRepresentation.Equiv τ (d i).representation)).card

open Classical in
theorem sum_finrank_eq_mult {k : ℕ} (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (hd : ∀ i, (d i).IsIrreducible) (τ : FiniteRepresentation.{0, uG, uP} ℂ G)
    [τ.representation.IsIrreducible] (j : ℕ) :
    (∑ i, if (d i).length = j + 1 then
        Module.finrank ℂ ((Langlands.twist (ν ^ j) τ.representation).IntertwiningMap
          (Langlands.twist (ν ^ j) (d i).representation.representation))
      else 0) = mult d τ j := by
  rw [mult, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (d i).representation.representation.IsIrreducible := hd i
  rw [← (Langlands.twistIntertwiningEquiv (ν ^ j) τ.representation
    (d i).representation.representation).finrank_eq, finrank_intertwiningMap_irreducible]
  by_cases h : (d i).length = j + 1 <;> simp [h]

/-- Equivalent sums of blocks have the same multiplicities. -/
theorem mult_eq_of_equiv {k l : ℕ} (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (d' : Fin l → BlockDatum.{0, uG, uW} ℂ G) (hd : ∀ i, (d i).IsIrreducible)
    (hd' : ∀ i, (d' i).IsIrreducible)
    (E : WeilDeligneRepresentation.Equiv (directSum fun i => (d i).pair ν)
      (directSum fun i => (d' i).pair ν))
    (τ : FiniteRepresentation.{0, uG, uP} ℂ G) [τ.representation.IsIrreducible] (j : ℕ) :
    mult d τ j = mult d' τ j := by
  have hN : ∀ v, E.representationEquiv ((directSum fun i => (d i).pair ν).monodromy v) =
      (directSum fun i => (d' i).pair ν).monodromy (E.representationEquiv v) :=
    fun v => LinearMap.congr_fun E.comm_monodromy v
  have h0 := count_congr (Langlands.twist (ν ^ j) τ.representation) E.representationEquiv hN j
  have h1 := count_congr (Langlands.twist (ν ^ j) τ.representation) E.representationEquiv hN
    (j + 1)
  rw [count_succ ν _ d j, count_succ ν _ d' j, h1, sum_finrank_eq_mult ν d hd,
    sum_finrank_eq_mult ν d' hd'] at h0
  omega

end Counting

/-- The number of blocks matching an irreducible datum `b` is a multiplicity. -/
theorem card_match_eq_mult {k : ℕ} (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (b : BlockDatum.{0, uG, uP} ℂ G) :
    Nat.card {i // BlockDataMatch (d i) b} = mult d b.representation (b.length - 1) := by
  classical
  have hlen : b.length - 1 + 1 = b.length := by
    have := b.length_pos
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, mult, hlen]
  refine congrArg Finset.card (Finset.ext fun i => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨h, ⟨e⟩⟩ => ⟨h, ⟨e.symm⟩⟩, fun ⟨h, ⟨e⟩⟩ => ⟨h, ⟨e.symm⟩⟩⟩

/-- Equivalent sums of irreducible blocks have equally many blocks matching any
irreducible datum. -/
theorem card_match_eq_of_equiv (ν : G →* ℂˣ) {k l : ℕ}
    (d : Fin k → BlockDatum.{0, uG, uV} ℂ G) (d' : Fin l → BlockDatum.{0, uG, uW} ℂ G)
    (hd : ∀ i, (d i).IsIrreducible) (hd' : ∀ i, (d' i).IsIrreducible)
    (E : WeilDeligneRepresentation.Equiv (directSum fun i => (d i).pair ν)
      (directSum fun i => (d' i).pair ν))
    (b : BlockDatum.{0, uG, uP} ℂ G) (hb : b.IsIrreducible) :
    Nat.card {i // BlockDataMatch (d i) b} = Nat.card {j // BlockDataMatch (d' j) b} := by
  have : b.representation.representation.IsIrreducible := hb
  rw [card_match_eq_mult, card_match_eq_mult]
  exact mult_eq_of_equiv ν d d' hd hd' E b.representation (b.length - 1)

/-- The forward implication: equivalent sums of irreducible blocks have matching data. -/
theorem forward (ν : G →* ℂˣ) {k l : ℕ} (d : Fin k → BlockDatum.{0, uG, uV} ℂ G)
    (d' : Fin l → BlockDatum.{0, uG, uW} ℂ G) (hd : ∀ i, (d i).IsIrreducible)
    (hd' : ∀ i, (d' i).IsIrreducible)
    (E : WeilDeligneRepresentation.Equiv (directSum fun i => (d i).pair ν)
      (directSum fun i => (d' i).pair ν)) :
    ∃ e : Fin k ≃ Fin l, ∀ i, (d i).length = (d' (e i)).length ∧
      Nonempty (FiniteRepresentation.Equiv (d i).representation (d' (e i)).representation) :=
  matching_of_class_counts d d'
    (fun a => card_match_eq_of_equiv ν d d' hd hd' E (d a) (hd a))
    (fun b => card_match_eq_of_equiv ν d d' hd hd' E (d' b) (hd' b))

end Langlands.WeilDeligneRepresentation.Blocks.DecompositionUniquenessProof

namespace Langlands.WeilDeligneRepresentation.Blocks

universe uG uV uW

open DecompositionUniquenessProof

/-- Uniqueness of block decompositions: two finite sums of irreducible blocks are
equivalent exactly when a bijection of summands matches lengths and Weil factors. -/
theorem decompositionUniqueness : DecompositionUniqueness.{uG, uV, uW} :=
  fun _ _ ν k l d d' hd hd' =>
    ⟨fun ⟨E⟩ => forward ν d d' hd hd' E,
      fun ⟨e, h⟩ => decompositionEquiv_of_matching k l d d' e h⟩

end Langlands.WeilDeligneRepresentation.Blocks
