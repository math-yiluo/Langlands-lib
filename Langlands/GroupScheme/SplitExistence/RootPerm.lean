import Langlands.GroupScheme.SplitExistence.Triangular

/-! # The subgroup `N` permutes the root groups and normalizes the torus

Every element `g` of `N = ⟨T, n_i⟩` conjugates each root group `U_j` into a root group `U_{j'}`
with `root j' = w (root j)` for an additive endomorphism `w` of `X` depending only on `g`,
and conjugates the torus into itself. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [Field K]

/-- `g` conjugates every root group into a root group, through an additive map of `X`. -/
def IsRootPerm (g : GL (Fin D.n) K) : Prop :=
  ∃ w : X →+ X, ∀ j : J, ∃ j' : J, P.root j' = w (P.root j) ∧
    ∀ s : K, ∃ s' : K, g * D.x j s * g⁻¹ = D.x j' s'

theorem IsRootPerm.mul {g h : GL (Fin D.n) K} (hg : D.IsRootPerm g) (hh : D.IsRootPerm h) :
    D.IsRootPerm (g * h) := by
  obtain ⟨w, hw⟩ := hg
  obtain ⟨w', hw'⟩ := hh
  refine ⟨w.comp w', fun j => ?_⟩
  obtain ⟨j₁, hj₁, hs₁⟩ := hw' j
  obtain ⟨j₂, hj₂, hs₂⟩ := hw j₁
  refine ⟨j₂, by rw [hj₂, hj₁]; rfl, fun s => ?_⟩
  obtain ⟨s₁, h₁⟩ := hs₁ s
  obtain ⟨s₂, h₂⟩ := hs₂ s₁
  refine ⟨s₂, ?_⟩
  rw [← h₂, ← h₁]
  group

theorem isRootPerm_torusHom (χ : Multiplicative X →* Kˣ) : D.IsRootPerm (D.torusHom χ) :=
  ⟨AddMonoidHom.id X, fun j => ⟨j, rfl, fun s => ⟨_, D.torusHom_conj_x χ j s⟩⟩⟩

theorem isRootPerm_wn (i : b.support) : D.IsRootPerm (D.wn (K := K) i) := by
  refine ⟨(P.reflection i).toLinearMap.toAddMonoidHom, fun j => ?_⟩
  obtain ⟨ε, -, h⟩ := D.wn_conj_x (K := K) i j
  exact ⟨P.reflectionPerm i j, RootPairing.root_reflectionPerm _ _ _, fun s => ⟨_, h s⟩⟩

theorem isRootPerm_wn_inv (i : b.support) : D.IsRootPerm (D.wn (K := K) i)⁻¹ := by
  refine ⟨(P.reflection i).toLinearMap.toAddMonoidHom, fun j => ?_⟩
  obtain ⟨ε, hε, h⟩ := D.wn_conj_x (K := K) i (P.reflectionPerm i j)
  rw [RootPairing.reflectionPerm_self] at h
  have hεε : (ε : K) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  refine ⟨P.reflectionPerm i j, RootPairing.root_reflectionPerm _ _ _, fun s => ⟨ε * s, ?_⟩⟩
  have h' := h (ε * s)
  rw [← mul_assoc, hεε, one_mul] at h'
  rw [← h', inv_inv]
  group

theorem isRootPerm_of_mem_weylSub {g : GL (Fin D.n) K} (hg : g ∈ D.weylSub K) :
    D.IsRootPerm g := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with ⟨χ, rfl⟩ | ⟨i, rfl⟩
    · exact D.isRootPerm_torusHom χ
    · exact D.isRootPerm_wn i
  | inv_mem x hx =>
    rcases hx with ⟨χ, rfl⟩ | ⟨i, rfl⟩
    · rw [← map_inv]
      exact D.isRootPerm_torusHom _
    · exact D.isRootPerm_wn_inv i
  | one => exact ⟨AddMonoidHom.id X, fun j => ⟨j, rfl, fun s => ⟨s, by group⟩⟩⟩
  | mul x y _ _ hx hy => exact hx.mul D hy

/-! ### `N` normalizes the torus -/

theorem reflectChar_reflectChar (i : J) (χ : Multiplicative X →* Kˣ) :
    reflectChar (P := P) i (reflectChar (P := P) i χ) = χ := by
  refine MonoidHom.ext fun x => ?_
  change χ (Multiplicative.ofAdd (P.reflection i (P.reflection i (Multiplicative.toAdd x)))) = χ x
  rw [RootPairing.reflection_same]
  rfl

/-- `g` conjugates the torus into itself. -/
def NormalizesTorus (g : GL (Fin D.n) K) : Prop :=
  ∀ χ : Multiplicative X →* Kˣ, ∃ ψ, g * D.torusHom χ * g⁻¹ = D.torusHom ψ

theorem normalizesTorus_of_mem_weylSub {g : GL (Fin D.n) K} (hg : g ∈ D.weylSub K) :
    D.NormalizesTorus g := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with ⟨φ, rfl⟩ | ⟨i, rfl⟩
    · intro χ
      refine ⟨χ, ?_⟩
      rw [show D.torusHom φ * D.torusHom χ = D.torusHom χ * D.torusHom φ by
        rw [← map_mul, ← map_mul]; exact congrArg _ (MonoidHom.ext fun x => mul_comm _ _)]
      group
    · intro χ
      refine ⟨reflectChar (P := P) (i : J) χ, ?_⟩
      rw [D.wn_mul_torusHom, mul_assoc, mul_inv_cancel, mul_one]
  | inv_mem x hx =>
    rcases hx with ⟨φ, rfl⟩ | ⟨i, rfl⟩
    · intro χ
      refine ⟨χ, ?_⟩
      rw [show (D.torusHom φ)⁻¹ * D.torusHom χ = D.torusHom χ * (D.torusHom φ)⁻¹ by
        rw [← map_inv, ← map_mul, ← map_mul]; exact congrArg _ (MonoidHom.ext fun x => mul_comm _ _)]
      group
    · intro χ
      refine ⟨reflectChar (P := P) (i : J) χ, ?_⟩
      have h := D.wn_mul_torusHom (K := K) i (reflectChar (P := P) (i : J) χ)
      rw [reflectChar_reflectChar] at h
      rw [inv_inv, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  | one => exact fun χ => ⟨χ, by group⟩
  | mul x y _ _ hx hy =>
    intro χ
    obtain ⟨ψ, hψ⟩ := hy χ
    obtain ⟨ψ', hψ'⟩ := hx ψ
    refine ⟨ψ', ?_⟩
    rw [← hψ', ← hψ]
    group

theorem conj_mem_torusSub_of_mem_weylSub {g : GL (Fin D.n) K} (hg : g ∈ D.weylSub K)
    {t : GL (Fin D.n) K} (ht : t ∈ D.torusSub K) : g * t * g⁻¹ ∈ D.torusSub K := by
  obtain ⟨χ, rfl⟩ := ht
  obtain ⟨ψ, hψ⟩ := D.normalizesTorus_of_mem_weylSub hg χ
  rw [hψ]
  exact torusHom_mem_torusSub ψ

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
