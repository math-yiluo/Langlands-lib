import Mathlib.LinearAlgebra.Eigenspace.Basic
import Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter

/-!
# Central elements act by scalars on a lowest-weight functional

Let `π` be a representation of a complex Lie algebra `L` on `V`, and let `ℓ : V → ℂ` be a
linear functional. Suppose that `L` is spanned, as far as `ℓ` can see, by elements acting on `ℓ`
by scalars together with a set `N` of "lowering" elements, and that some `H ∈ L` acts on `ℓ` by
a scalar and lowers every element of `N` by a positive integer. Then every central element `z`
of `U(L)` acts on `ℓ` by a scalar: `ℓ ∘ π(z) = c ℓ`
(`exists_comp_envelopingAction_eq_smul`).

This is the algebraic core of Harish-Chandra's computation of the infinitesimal character of a
principal series: `ℓ` is evaluation at the identity, the elements acting by scalars are those of
the Borel subalgebra, and `N` is a set of root vectors of the opposite nilradical.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace JacquetCenter

open InfinitesimalCharacter

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The product `ι y₁ ⋯ ι y_k` in `U(L)` of the word `w = [y₁, …, y_k]`. -/
def wordProd (w : List L) : UniversalEnvelopingAlgebra ℂ L :=
  (w.map (UniversalEnvelopingAlgebra.ι ℂ)).prod

@[simp]
theorem wordProd_nil : wordProd ([] : List L) = 1 :=
  rfl

theorem wordProd_append_singleton (w : List L) (y : L) :
    wordProd (w ++ [y]) = wordProd w * UniversalEnvelopingAlgebra.ι ℂ y := by
  simp [wordProd, List.map_append, List.prod_append]

theorem envelopingAction_ι (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (x : L) :
    envelopingAction π (UniversalEnvelopingAlgebra.ι ℂ x) = π x := by
  rw [envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply]

theorem comp_envelopingAction_mul (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ)
    (a b : UniversalEnvelopingAlgebra ℂ L) :
    φ ∘ₗ envelopingAction π (a * b) = (φ ∘ₗ envelopingAction π a) ∘ₗ envelopingAction π b := by
  rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc]

variable (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (N : Set L)

/-- The span of the functionals `ℓ ∘ π(ι y₁ ⋯ ι y_k)` for the words `[y₁, …, y_k]` with letters
in `N` (including the empty word, which gives `ℓ`). -/
def nbarSpan : Submodule ℂ (V →ₗ[ℂ] ℂ) :=
  Submodule.span ℂ
    {φ | ∃ w : List L, (∀ y ∈ w, y ∈ N) ∧ φ = ℓ ∘ₗ envelopingAction π (wordProd w)}

theorem word_mem_nbarSpan {w : List L} (hw : ∀ y ∈ w, y ∈ N) :
    ℓ ∘ₗ envelopingAction π (wordProd w) ∈ nbarSpan π ℓ N :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem self_mem_nbarSpan : ℓ ∈ nbarSpan π ℓ N := by
  have h := word_mem_nbarSpan π ℓ N (w := []) (by simp)
  rwa [wordProd_nil, map_one, Module.End.one_eq_id, LinearMap.comp_id] at h

/-- Appending a letter of `N` keeps a functional in `nbarSpan`. -/
theorem comp_mem_nbarSpan {φ : V →ₗ[ℂ] ℂ} (hφ : φ ∈ nbarSpan π ℓ N) {y : L} (hy : y ∈ N) :
    φ ∘ₗ π y ∈ nbarSpan π ℓ N := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨w, hw, rfl⟩ := h
    have h1 : (ℓ ∘ₗ envelopingAction π (wordProd w)) ∘ₗ π y =
        ℓ ∘ₗ envelopingAction π (wordProd (w ++ [y])) := by
      rw [wordProd_append_singleton, comp_envelopingAction_mul, envelopingAction_ι]
    rw [h1]
    refine word_mem_nbarSpan π ℓ N fun z hz => ?_
    rcases List.mem_append.1 hz with hz | hz
    · exact hw z hz
    · rw [List.mem_singleton.1 hz]
      exact hy
  | zero => rw [LinearMap.zero_comp]; exact zero_mem _
  | add φ ψ _ _ hφ hψ => rw [LinearMap.add_comp]; exact add_mem hφ hψ
  | smul c φ _ hφ => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ c hφ

/-- `ℓ ∘ π(y)` lies in `nbarSpan` for `y` in the span of `N`. -/
theorem comp_span_mem_nbarSpan {y : L} (hy : y ∈ Submodule.span ℂ N) :
    ℓ ∘ₗ π y ∈ nbarSpan π ℓ N := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact comp_mem_nbarSpan π ℓ N (self_mem_nbarSpan π ℓ N) hy
  | zero => rw [map_zero, LinearMap.comp_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [map_add, LinearMap.comp_add]; exact add_mem h h'
  | smul c y _ h => rw [map_smul, LinearMap.comp_smul]; exact Submodule.smul_mem _ c h

/-- The elements `x ∈ L` with `ℓ ∘ π(x)` a scalar multiple of `ℓ`. -/
def scalarSubmodule : Submodule ℂ L where
  carrier := {x | ∃ c : ℂ, ℓ ∘ₗ π x = c • ℓ}
  zero_mem' := ⟨0, by rw [map_zero, LinearMap.comp_zero, zero_smul]⟩
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, LinearMap.comp_add, hc, hd, add_smul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a * c, by rw [map_smul, LinearMap.comp_smul, hc, smul_smul]⟩

theorem mem_scalarSubmodule {x : L} : x ∈ scalarSubmodule π ℓ ↔ ∃ c : ℂ, ℓ ∘ₗ π x = c • ℓ :=
  Iff.rfl

/-- The elements `x ∈ L` with `ℓ ∘ π(x) = c ℓ + ℓ ∘ π(y)` for some `c ∈ ℂ` and some `y` in the
span of `N`. -/
def decSubmodule : Submodule ℂ L where
  carrier := {x | ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y}
  zero_mem' := ⟨0, 0, zero_mem _, by rw [map_zero, LinearMap.comp_zero, zero_smul, zero_add]⟩
  add_mem' := by
    rintro x x' ⟨c, y, hy, h⟩ ⟨c', y', hy', h'⟩
    refine ⟨c + c', y + y', add_mem hy hy', ?_⟩
    rw [map_add, LinearMap.comp_add, h, h', map_add, LinearMap.comp_add, add_smul]
    abel
  smul_mem' := by
    rintro a x ⟨c, y, hy, h⟩
    refine ⟨a * c, a • y, Submodule.smul_mem _ a hy, ?_⟩
    rw [map_smul, LinearMap.comp_smul, h, map_smul, LinearMap.comp_smul, smul_add, smul_smul]

theorem mem_decSubmodule {x : L} : x ∈ decSubmodule π ℓ N ↔
    ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y :=
  Iff.rfl

theorem scalarSubmodule_le_decSubmodule : scalarSubmodule π ℓ ≤ decSubmodule π ℓ N := by
  rintro x ⟨c, hc⟩
  exact ⟨c, 0, zero_mem _, by rw [hc, map_zero, LinearMap.comp_zero, add_zero]⟩

theorem subset_decSubmodule : N ⊆ decSubmodule π ℓ N := fun y hy =>
  ⟨0, y, Submodule.subset_span hy, by rw [zero_smul, zero_add]⟩

variable {π ℓ N}

/-- The key step: if `ℓ ∘ π(x)` lies in `nbarSpan` for every `x ∈ L`, then so does
`ℓ ∘ π(w) ∘ π(x)` for every word `w` in `N`. Write `w = w' y`; then
`π(y) π(x) = π(x) π(y) + π⁅y, x⁆`, and induction on the length of `w` applies to `x` and
`⁅y, x⁆`. -/
theorem word_comp_mem_nbarSpan
    (hdec : ∀ x : L, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y)
    (w : List L) (hw : ∀ y ∈ w, y ∈ N) (x : L) :
    (ℓ ∘ₗ envelopingAction π (wordProd w)) ∘ₗ π x ∈ nbarSpan π ℓ N := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
    obtain ⟨c, y, hy, h⟩ := hdec x
    rw [wordProd_nil, map_one, Module.End.one_eq_id, LinearMap.comp_id, h]
    exact add_mem (Submodule.smul_mem _ c (self_mem_nbarSpan π ℓ N))
      (comp_span_mem_nbarSpan π ℓ N hy)
  | append_singleton w y ih =>
    have hw' : ∀ z ∈ w, z ∈ N := fun z hz => hw z (List.mem_append_left _ hz)
    have hy : y ∈ N := hw y (List.mem_append_right _ (List.mem_singleton_self y))
    have hbr : π y * π x = π x * π y + π ⁅y, x⁆ := by
      rw [LieHom.map_lie, Ring.lie_def]
      abel
    have h1 : (ℓ ∘ₗ envelopingAction π (wordProd (w ++ [y]))) ∘ₗ π x =
        ((ℓ ∘ₗ envelopingAction π (wordProd w)) ∘ₗ π x) ∘ₗ π y +
          (ℓ ∘ₗ envelopingAction π (wordProd w)) ∘ₗ π ⁅y, x⁆ := by
      rw [wordProd_append_singleton, comp_envelopingAction_mul, envelopingAction_ι,
        LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hbr, LinearMap.comp_add,
        Module.End.mul_eq_comp]
      simp only [LinearMap.comp_assoc]
    rw [h1]
    exact add_mem (comp_mem_nbarSpan π ℓ N (ih hw' x) hy) (ih hw' ⁅y, x⁆)

/-- `nbarSpan` is stable under every `π(x)`, `x ∈ L`. -/
theorem comp_lie_mem_nbarSpan
    (hdec : ∀ x : L, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y)
    {φ : V →ₗ[ℂ] ℂ} (hφ : φ ∈ nbarSpan π ℓ N) (x : L) : φ ∘ₗ π x ∈ nbarSpan π ℓ N := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨w, hw, rfl⟩ := h
    exact word_comp_mem_nbarSpan hdec w hw x
  | zero => rw [LinearMap.zero_comp]; exact zero_mem _
  | add φ ψ _ _ hφ hψ => rw [LinearMap.add_comp]; exact add_mem hφ hψ
  | smul c φ _ hφ => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ c hφ

/-- `nbarSpan` is stable under the action of `U(L)`; in particular it contains `ℓ ∘ π(u)` for
every `u ∈ U(L)`. -/
theorem comp_envelopingAction_mem_nbarSpan
    (hdec : ∀ x : L, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y)
    (u : UniversalEnvelopingAlgebra ℂ L) :
    ∀ φ ∈ nbarSpan π ℓ N, φ ∘ₗ envelopingAction π u ∈ nbarSpan π ℓ N := by
  induction u using envInduction with
  | algebraMap r =>
    intro φ hφ
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      Module.End.one_eq_id, LinearMap.comp_id]
    exact Submodule.smul_mem _ r hφ
  | ι x =>
    intro φ hφ
    rw [envelopingAction_ι]
    exact comp_lie_mem_nbarSpan hdec hφ x
  | mul a b ha hb =>
    intro φ hφ
    rw [comp_envelopingAction_mul]
    exact hb _ (ha φ hφ)
  | add a b ha hb =>
    intro φ hφ
    rw [map_add, LinearMap.comp_add]
    exact add_mem (ha φ hφ) (hb φ hφ)

/-- A word in `N` is an eigenvector of `ad(ι H)` with eigenvalue `-k`, `k > 0` unless the word
is empty. -/
theorem exists_mul_wordProd (H : L) (hN : ∀ y ∈ N, ∃ k : ℕ, 0 < k ∧ ⁅H, y⁆ = -((k : ℂ) • y))
    (w : List L) (hw : ∀ y ∈ w, y ∈ N) :
    ∃ k : ℕ, (w ≠ [] → 0 < k) ∧
      UniversalEnvelopingAlgebra.ι ℂ H * wordProd w =
        wordProd w * UniversalEnvelopingAlgebra.ι ℂ H - (k : ℂ) • wordProd w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨0, by simp, by simp⟩
  | append_singleton w y ih =>
    obtain ⟨k, -, hk⟩ := ih fun z hz => hw z (List.mem_append_left _ hz)
    obtain ⟨m, hm, hy⟩ := hN y (hw y (List.mem_append_right _ (List.mem_singleton_self y)))
    refine ⟨k + m, fun _ => by omega, ?_⟩
    have hιy : UniversalEnvelopingAlgebra.ι ℂ H * UniversalEnvelopingAlgebra.ι ℂ y =
        UniversalEnvelopingAlgebra.ι ℂ y * UniversalEnvelopingAlgebra.ι ℂ H -
          (m : ℂ) • UniversalEnvelopingAlgebra.ι ℂ y := by
      have h := (UniversalEnvelopingAlgebra.ι ℂ (L := L)).map_lie H y
      rw [hy, map_neg, map_smul, Ring.lie_def] at h
      rw [sub_eq_add_neg (UniversalEnvelopingAlgebra.ι ℂ y * UniversalEnvelopingAlgebra.ι ℂ H), h]
      abel
    rw [wordProd_append_singleton, ← mul_assoc, hk, sub_mul, mul_assoc, hιy, mul_sub,
      ← mul_assoc, smul_mul_assoc, mul_smul_comm, Nat.cast_add, add_smul]
    abel

/-- **Central elements act by scalars on `ℓ`.** Let `H ∈ L` act on `ℓ` by the scalar `μ`, let
every element of `N` be an eigenvector of `ad H` with a negative integral eigenvalue, and let
every `ℓ ∘ π(x)` be a scalar multiple of `ℓ` plus `ℓ ∘ π(y)` with `y` in the span of `N`. Then
every central `z ∈ U(L)` satisfies `ℓ ∘ π(z) = c ℓ` for some `c ∈ ℂ`.

Proof: `ℓ ∘ π(z)` lies in `nbarSpan` (`comp_envelopingAction_mem_nbarSpan`). The operator
`T φ = φ ∘ π(H) - μ φ` kills `ℓ` and `ℓ ∘ π(z)` (as `z` commutes with `ι H`), and acts on
`ℓ ∘ π(w)` for a nonempty word `w` in `N` by a positive integer (`exists_mul_wordProd`).
Eigenspaces of `T` are independent, so the component of `ℓ ∘ π(z)` outside `ℂ ℓ` vanishes. -/
theorem exists_comp_envelopingAction_eq_smul (H : L) (μ : ℂ) (hH : ℓ ∘ₗ π H = μ • ℓ)
    (hN : ∀ y ∈ N, ∃ k : ℕ, 0 < k ∧ ⁅H, y⁆ = -((k : ℂ) • y))
    (hdec : ∀ x : L, ∃ c : ℂ, ∃ y ∈ Submodule.span ℂ N, ℓ ∘ₗ π x = c • ℓ + ℓ ∘ₗ π y)
    {z : UniversalEnvelopingAlgebra ℂ L}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L)) :
    ∃ c : ℂ, ℓ ∘ₗ envelopingAction π z = c • ℓ := by
  -- the operator `T φ = φ ∘ π(H) - μ φ`
  let T : Module.End ℂ (V →ₗ[ℂ] ℂ) :=
    { toFun := fun φ => φ ∘ₗ π H - μ • φ
      map_add' := fun φ ψ => by rw [LinearMap.add_comp, smul_add]; abel
      map_smul' := fun c φ => by
        rw [LinearMap.smul_comp, RingHom.id_apply, smul_sub, smul_comm c μ φ] }
  have hT : ∀ φ, T φ = φ ∘ₗ π H - μ • φ := fun _ => rfl
  set B : Submodule ℂ (V →ₗ[ℂ] ℂ) := ⨆ (j : ℂ) (_ : j ≠ 0), T.eigenspace j with hBdef
  -- `nbarSpan` lies in `ℂ ℓ ⊔ B`
  have hle : nbarSpan π ℓ N ≤ Submodule.span ℂ {ℓ} ⊔ B := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨w, hw, rfl⟩
    rcases eq_or_ne w [] with rfl | hne
    · refine Submodule.mem_sup_left (Submodule.subset_span ?_)
      rw [wordProd_nil, map_one, Module.End.one_eq_id, LinearMap.comp_id]
      rfl
    · obtain ⟨k, hk, hkw⟩ := exists_mul_wordProd H hN w hw
      have hk0 : ((k : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (hk hne).ne'
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem (k : ℂ)
        (Submodule.mem_iSup_of_mem hk0 ?_))
      rw [Module.End.mem_eigenspace_iff, hT]
      have h2 : wordProd w * UniversalEnvelopingAlgebra.ι ℂ H =
          UniversalEnvelopingAlgebra.ι ℂ H * wordProd w + (k : ℂ) • wordProd w := by
        rw [hkw]; abel
      rw [LinearMap.comp_assoc, ← envelopingAction_ι π H, ← Module.End.mul_eq_comp, ← map_mul,
        h2, map_add, map_mul, envelopingAction_ι, map_smul, LinearMap.comp_add,
        LinearMap.comp_smul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hH,
        LinearMap.smul_comp]
      abel
  -- `ℓ ∘ π(z)` is killed by `T`
  have hTz : T (ℓ ∘ₗ envelopingAction π z) = 0 := by
    rw [hT, sub_eq_zero, LinearMap.comp_assoc, ← envelopingAction_ι π H,
      ← Module.End.mul_eq_comp, ← map_mul,
      (Subalgebra.mem_center_iff.1 hz (UniversalEnvelopingAlgebra.ι ℂ H)).symm, map_mul,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, envelopingAction_ι, hH,
      LinearMap.smul_comp]
  have hTℓ : T ℓ = 0 := by rw [hT, hH, sub_self]
  have hmem := hle (comp_envelopingAction_mem_nbarSpan hdec z ℓ (self_mem_nbarSpan π ℓ N))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  have hTb : T b = 0 := by
    have h := hTz
    rw [← hab, map_add, map_smul, hTℓ, smul_zero, zero_add] at h
    exact h
  have hb0 : b ∈ T.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, hTb, zero_smul]
  have hdisj := (Module.End.eigenspaces_iSupIndep T) 0
  have hb : b = 0 := Submodule.disjoint_def.1 hdisj b hb0 hb
  exact ⟨c, by rw [← hab, hb, add_zero]⟩

end JacquetCenter

end Langlands.Archimedean
