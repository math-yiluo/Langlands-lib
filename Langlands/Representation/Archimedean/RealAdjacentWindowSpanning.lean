import Langlands.Representation.Archimedean.RealBlockCompactAdjoint
import Langlands.Representation.Archimedean.RealAmbientOrthogonalUncertainty

/-! # Spanning by a low window and an adjacent high window -/

noncomputable section

open scoped ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealAdjacentWindowSpanning

open PrincipalSeriesAnnihilator RealBlockCompactAdjoint RealBlockFourierFinite

variable {n : ℕ} {χ : ℕ → ℝˣ → ℂ}

/-- The indicator of the strict low Fourier window. -/
def lowMultiplier (m : ℕ) (j : ℤ) : ℂ := if |j| < (m : ℤ) then 1 else 0

/-- The indicator of the complementary high Fourier window. -/
def highMultiplier (m : ℕ) (j : ℤ) : ℂ := 1 - lowMultiplier m j

@[simp] theorem conj_lowMultiplier (m : ℕ) (j : ℤ) :
    conj (lowMultiplier m j) = lowMultiplier m j := by
  unfold lowMultiplier
  split <;> simp

@[simp] theorem conj_highMultiplier (m : ℕ) (j : ℤ) :
    conj (highMultiplier m j) = highMultiplier m j := by
  simp [highMultiplier]

/-- Ranges of compact-equivariant maps are compact-stable. -/
theorem isStable_range (T : KFin n χ →ₗ[ℂ] KFin n χ)
    (hT : ∀ k x, T (rho k x) = rho k (T x)) :
    IsStable (rho (n := n) (χ := χ)) (LinearMap.range T) := by
  rintro k _ ⟨x, rfl⟩
  exact ⟨rho k x, hT k x⟩

/-- A vector orthogonal to the range of a self-adjoint map belongs to its kernel. -/
theorem map_eq_zero_of_orthogonal (T : KFin n χ →ₗ[ℂ] KFin n χ)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {w : KFin n χ} (hw : ∀ v ∈ LinearMap.range T, ⟪w, v⟫_ℂ = 0) :
    T w = 0 := by
  have h : ⟪T w, T w⟫_ℂ = 0 := by
    rw [hT]
    exact hw _ ⟨T w, rfl⟩
  exact inner_self_eq_zero.mp h

/-- If the low cutoff is larger, the low range and the adjacent high range span the
entire compact-finite principal series. -/
theorem range_low_sup_range_high (p : ℕ) (hp : p + 3 ≤ n)
    (m h : ℕ) (hhm : h < m)
    (P Q : KFin n χ →ₗ[ℂ] KFin n χ)
    (hPK : ∀ k x, P (rho k x) = rho k (P x))
    (hQK : ∀ k x, Q (rho k x) = rho k (Q x))
    (hP : ∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j (P x).toFun k =
        lowMultiplier m j * blockFourierCoefficient n p j x.toFun k)
    (hQ : ∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n (p + 1) j (Q x).toFun k =
        highMultiplier h j * blockFourierCoefficient n (p + 1) j x.toFun k) :
    LinearMap.range P ⊔ LinearMap.range Q = ⊤ := by
  classical
  have hPs := inner_eq_of_real_multiplier (show p + 1 < n by omega)
    P (lowMultiplier m) (conj_lowMultiplier m) hP
  have hQs := inner_eq_of_real_multiplier (show (p + 1) + 1 < n by omega)
    Q (highMultiplier h) (conj_highMultiplier h) hQ
  let W := LinearMap.range P ⊔ LinearMap.range Q
  have hW : IsStable (rho (n := n) (χ := χ)) W := by
    intro k x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem _
      ((le_sup_left : LinearMap.range P ≤ W) (isStable_range P hPK k a ha))
      ((le_sup_right : LinearMap.range Q ≤ W) (isStable_range Q hQK k b hb))
  apply eq_top_iff.mpr
  intro x _
  by_contra hx
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_inner_eq_zero_kfin W hW hx
  have hPw : P w = 0 :=
    map_eq_zero_of_orthogonal P hPs fun v hv =>
      hw v ((le_sup_left : LinearMap.range P ≤ W) hv)
  have hQw : Q w = 0 :=
    map_eq_zero_of_orthogonal Q hQs fun v hv =>
      hw v ((le_sup_right : LinearMap.range Q ≤ W) hv)
  apply hw0
  refine KFin.eq_zero_of_restrict w fun k => ?_
  apply RealOrthogonalBlock.adjacent_uncertainty p hp
    (r := 0) (s := 1) (m := m) (m' := h)
    (Or.inl ⟨rfl, rfl⟩) hhm w.continuous_toFun w.toFun_mem.2 ?_ ?_ k k.2
  · intro g hg j hj
    have hj' := hP w j g hg
    rw [hPw, KFin.toFun_zero, RealBlockJacquet.blockFourierCoefficient_zero_fun,
      show lowMultiplier m j = 1 by simp [lowMultiplier, hj], one_mul] at hj'
    exact hj'.symm
  · intro g hg j hj
    have hj' := hQ w j g hg
    rw [hQw, KFin.toFun_zero, RealBlockJacquet.blockFourierCoefficient_zero_fun,
      show highMultiplier h j = 1 by
        simp [highMultiplier, lowMultiplier, not_lt.mpr hj], one_mul] at hj'
    exact hj'.symm

/-- A surjective map that kills the low range remains surjective on the high range. -/
theorem surjective_comp_of_range_sup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (P Q : KFin n χ →ₗ[ℂ] KFin n χ) (T : KFin n χ →ₗ[ℂ] E)
    (hPQ : LinearMap.range P ⊔ LinearMap.range Q = ⊤)
    (hT : Function.Surjective T) (hTP : ∀ x, T (P x) = 0) :
    Function.Surjective (T.comp Q) := by
  intro y
  obtain ⟨x, rfl⟩ := hT y
  have hx : x ∈ LinearMap.range P ⊔ LinearMap.range Q := by rw [hPQ]; trivial
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨b, by simp [hTP]⟩

end RealAdjacentWindowSpanning

/-- Adjacent low and high Fourier windows with strictly decreasing cutoffs span the
compact-finite principal series when realized by compact-equivariant endomorphisms. -/
def RealAdjacentWindowSpanningStatement : Prop :=
  ∀ (n p m h : ℕ) (χ : ℕ → ℝˣ → ℂ)
    (P Q : PrincipalSeriesAnnihilator.KFin n χ →ₗ[ℂ] PrincipalSeriesAnnihilator.KFin n χ),
    p + 3 ≤ n → h < m →
    (∀ k x, P (PrincipalSeriesAnnihilator.rho k x) =
      PrincipalSeriesAnnihilator.rho k (P x)) →
    (∀ k x, Q (PrincipalSeriesAnnihilator.rho k x) =
      PrincipalSeriesAnnihilator.rho k (Q x)) →
    (∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j (P x).toFun k =
        RealAdjacentWindowSpanning.lowMultiplier m j *
          blockFourierCoefficient n p j x.toFun k) →
    (∀ x j k, k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n (p + 1) j (Q x).toFun k =
        RealAdjacentWindowSpanning.highMultiplier h j *
          blockFourierCoefficient n (p + 1) j x.toFun k) →
    LinearMap.range P ⊔ LinearMap.range Q = ⊤

theorem realAdjacentWindowSpanning : RealAdjacentWindowSpanningStatement :=
  fun _ p m h _ P Q hp hhm hPK hQK hP hQ =>
    RealAdjacentWindowSpanning.range_low_sup_range_high p hp m h hhm P Q hPK hQK hP hQ

end Langlands.Archimedean
