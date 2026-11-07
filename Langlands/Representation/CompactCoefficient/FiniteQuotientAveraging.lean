import Langlands.Representation.Category.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RepresentationTheory.Intertwining

/-!
# Averaging equivariant linear maps over a finite quotient

Let `N` be a subgroup of a group `G` with finitely many left cosets. A linear map
`φ` between two complex representations of `G` that commutes with the action of
`N` becomes a `G`-intertwiner after averaging its conjugates `σ g ∘ φ ∘ ρ g⁻¹` over
representatives `g` of the cosets `G ⧸ N`. The average fixes intertwiners and
commutes with composition by intertwiners on either side. When the centre of `G`
acts on both representations through the same character, commuting with `H`
implies commuting with `H ⊔ center G`.
-/

noncomputable section

namespace Langlands.FiniteQuotientAveraging

universe uG uV uW uU

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]

section Conjugate

variable (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

/-- The conjugate `σ g ∘ φ ∘ ρ g⁻¹` of a linear map by a group element. -/
def conj (φ : V →ₗ[ℂ] W) (g : G) : V →ₗ[ℂ] W :=
  σ g ∘ₗ φ ∘ₗ ρ g⁻¹

theorem conj_apply (φ : V →ₗ[ℂ] W) (g : G) (v : V) :
    conj ρ σ φ g v = σ g (φ (ρ g⁻¹ v)) := rfl

/-- A linear map commutes with the actions of the elements of the subgroup `N`. -/
def IsEquivariantOn (N : Subgroup G) (φ : V →ₗ[ℂ] W) : Prop :=
  ∀ n ∈ N, ∀ v, φ (ρ n v) = σ n (φ v)

variable {ρ σ}

theorem rep_mul_inv_apply (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- Conjugation by `g * n` equals conjugation by `g` for `n ∈ N`. -/
theorem conj_mul_of_mem {N : Subgroup G} {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ N φ)
    (g : G) {n : G} (hn : n ∈ N) : conj ρ σ φ (g * n) = conj ρ σ φ g := by
  ext v
  have h := hφ n hn (ρ n⁻¹ (ρ g⁻¹ v))
  rw [rep_mul_inv_apply] at h
  simp only [conj_apply, mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [← h]

/-- Conjugation depends only on the left coset. -/
theorem conj_eq_of_mk_eq {N : Subgroup G} {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ N φ)
    {g g' : G} (h : (g : G ⧸ N) = g') : conj ρ σ φ g = conj ρ σ φ g' := by
  have hm : g⁻¹ * g' ∈ N := QuotientGroup.eq.mp h
  calc conj ρ σ φ g = conj ρ σ φ (g * (g⁻¹ * g')) := (conj_mul_of_mem hφ g hm).symm
    _ = conj ρ σ φ g' := by rw [mul_inv_cancel_left]

/-- Conjugation fixes intertwiners. -/
theorem conj_intertwiningMap (f : ρ.IntertwiningMap σ) (g : G) :
    conj ρ σ f.toLinearMap g = f.toLinearMap := by
  ext v
  change σ g (f (ρ g⁻¹ v)) = f v
  rw [← f.isIntertwining, rep_mul_inv_apply]

/-- Translating the conjugation parameter on the left. -/
theorem conj_mul_apply (φ : V →ₗ[ℂ] W) (h g : G) (v : V) :
    conj ρ σ φ (h * g) (ρ h v) = σ h (conj ρ σ φ g v) := by
  simp only [conj_apply, mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [show ρ h⁻¹ (ρ h v) = v by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]]

end Conjugate

section Average

variable (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
  [Fintype (G ⧸ N)]

/-- The average of the conjugates of `φ` over chosen representatives of `G ⧸ N`. -/
def average (φ : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card (G ⧸ N) : ℂ)⁻¹ • ∑ q : G ⧸ N, conj ρ σ φ q.out

theorem average_apply (φ : V →ₗ[ℂ] W) (v : V) :
    average ρ σ N φ v =
      (Fintype.card (G ⧸ N) : ℂ)⁻¹ • ∑ q : G ⧸ N, σ q.out (φ (ρ q.out⁻¹ v)) := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, conj_apply]

variable {ρ σ N}

/-- The average of an `N`-equivariant map is `G`-equivariant. -/
theorem average_isIntertwining {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ N φ) (h : G)
    (v : V) : average ρ σ N φ (ρ h v) = σ h (average ρ σ N φ v) := by
  have hsum : ∑ q : G ⧸ N, conj ρ σ φ q.out (ρ h v) =
      ∑ q : G ⧸ N, σ h (conj ρ σ φ q.out v) := by
    calc ∑ q : G ⧸ N, conj ρ σ φ q.out (ρ h v)
        = ∑ q : G ⧸ N, conj ρ σ φ (h • q).out (ρ h v) :=
          (Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun _ => rfl)).symm
      _ = ∑ q : G ⧸ N, conj ρ σ φ (h * q.out) (ρ h v) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [conj_eq_of_mk_eq hφ (g := (h • q).out) (g' := h * q.out)]
          rw [QuotientGroup.out_eq']
          exact (MulAction.Quotient.mk_smul_out N h q).symm
      _ = ∑ q : G ⧸ N, σ h (conj ρ σ φ q.out v) := by
          simp only [conj_mul_apply]
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [hsum, map_smul, map_sum]

/-- The average of an `N`-equivariant map, as an intertwiner. -/
def averageMap {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ N φ) : ρ.IntertwiningMap σ :=
  (average ρ σ N φ).intertwiningMap_of_isIntertwiningMap ρ σ (average_isIntertwining hφ)

theorem averageMap_apply {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ N φ) (v : V) :
    averageMap hφ v = average ρ σ N φ v := rfl

/-- Averaging fixes intertwiners. -/
theorem average_intertwiningMap (f : ρ.IntertwiningMap σ) :
    average ρ σ N f.toLinearMap = f.toLinearMap := by
  have hcard : (Fintype.card (G ⧸ N) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := G ⧸ N)).ne'
  simp only [average, conj_intertwiningMap, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Averaging commutes with composition by an intertwiner on the left. -/
theorem average_comp_left {τ : Representation ℂ G U} (ψ : σ.IntertwiningMap τ)
    (φ : V →ₗ[ℂ] W) (v : V) :
    average ρ τ N (ψ.toLinearMap ∘ₗ φ) v = ψ (average ρ σ N φ v) := by
  simp only [average_apply, LinearMap.comp_apply, map_smul, map_sum,
    Representation.IntertwiningMap.toLinearMap_apply, ψ.isIntertwining]

/-- Averaging commutes with composition by an intertwiner on the right. -/
theorem average_comp_right {τ : Representation ℂ G U} (φ : V →ₗ[ℂ] W)
    (ψ : τ.IntertwiningMap ρ) (u : U) :
    average τ σ N (φ ∘ₗ ψ.toLinearMap) u = average ρ σ N φ (ψ u) := by
  simp only [average_apply, LinearMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_apply, ψ.isIntertwining]

end Average

section Center

variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- If the centre acts on both representations through the same character, a map
commuting with `H` commutes with `H ⊔ center G`. -/
theorem isEquivariantOn_sup_center (χ : Subgroup.center G →* ℂˣ)
    (hρ : ∀ (z : Subgroup.center G) (v : V), ρ z v = (χ z : ℂ) • v)
    (hσ : ∀ (z : Subgroup.center G) (w : W), σ z w = (χ z : ℂ) • w)
    {H : Subgroup G} {φ : V →ₗ[ℂ] W} (hφ : IsEquivariantOn ρ σ H φ) :
    IsEquivariantOn ρ σ (H ⊔ Subgroup.center G) φ := by
  intro g hg v
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hρz := hρ ⟨z, hz⟩ v
  have hσz := hσ ⟨z, hz⟩ (φ v)
  simp only [map_mul, Module.End.mul_apply]
  change φ (ρ h (ρ (⟨z, hz⟩ : Subgroup.center G) v)) =
    σ h (σ (⟨z, hz⟩ : Subgroup.center G) (φ v))
  rw [hρz, hσz, map_smul, map_smul, hφ h hh, map_smul]

end Center

end Langlands.FiniteQuotientAveraging
