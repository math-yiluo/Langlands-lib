import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Bounded operators from inner-product-preserving relations

If a set `S` of pairs `(x, y)` in `H × H'` of complex Hilbert spaces satisfies
`⟪y, y'⟫ = ⟪x, x'⟫` for all `(x, y), (x', y') ∈ S`, then some continuous linear operator
`T : H → H'` maps `x` to `y` for every `(x, y) ∈ S`: the relation spanned by `S` is the graph of an
isometry, which extends to the closure of its domain and is composed with the orthogonal
projection onto that closure. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis

open scoped InnerProductSpace

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

/-- Inner products of second components agree with those of first components on the span of a
set of pairs on which they agree. -/
theorem inner_snd_eq_inner_fst_of_mem_span {S : Set (H × H')}
    (hS : ∀ s ∈ S, ∀ t ∈ S, ⟪s.2, t.2⟫_ℂ = ⟪s.1, t.1⟫_ℂ) {γ γ' : H × H'}
    (hγ : γ ∈ Submodule.span ℂ S) (hγ' : γ' ∈ Submodule.span ℂ S) :
    ⟪γ.2, γ'.2⟫_ℂ = ⟪γ.1, γ'.1⟫_ℂ := by
  have h₁ : ∀ s ∈ S, ∀ γ' ∈ Submodule.span ℂ S, ⟪s.2, γ'.2⟫_ℂ = ⟪s.1, γ'.1⟫_ℂ := by
    intro s hs γ' hγ'
    induction hγ' using Submodule.span_induction with
    | mem t ht => exact hS s hs t ht
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
    | smul c x _ hx => simp [inner_smul_right, hx]
  induction hγ using Submodule.span_induction with
  | mem s hs => exact h₁ s hs γ' hγ'
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | smul c x _ hx => simp [inner_smul_left, hx]

variable [CompleteSpace H] [CompleteSpace H']

/-- A set of pairs preserving inner products lies in the graph of a continuous linear operator. -/
theorem exists_continuousLinearMap_of_inner_eq (S : Set (H × H'))
    (hS : ∀ s ∈ S, ∀ t ∈ S, ⟪s.2, t.2⟫_ℂ = ⟪s.1, t.1⟫_ℂ) :
    ∃ T : H →L[ℂ] H', ∀ s ∈ S, T s.1 = s.2 := by
  set Γ : Submodule ℂ (H × H') := Submodule.span ℂ S
  set D : Submodule ℂ H := (Γ.map (LinearMap.fst ℂ H H')).topologicalClosure
  have : IsClosed (D : Set H) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace D := IsClosed.completeSpace_coe
  have hmemD : ∀ γ ∈ Γ, γ.1 ∈ D := fun γ hγ =>
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hγ)
  let e : Γ →ₗ[ℂ] D :=
    { toFun := fun γ => ⟨(γ : H × H').1, hmemD γ γ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f : Γ →ₗ[ℂ] H' := (LinearMap.snd ℂ H H').comp Γ.subtype
  have hnorm : ∀ γ : Γ, ‖f γ‖ = ‖e γ‖ := by
    intro γ
    have h := inner_snd_eq_inner_fst_of_mem_span hS γ.2 γ.2
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖(γ : H × H').2‖ ^ 2 = ‖(γ : H × H').1‖ ^ 2 := by exact_mod_cast h
    have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
    simpa [f, e] using this
  have hdense : DenseRange e := by
    have himg : Subtype.val '' Set.range e = (Γ.map (LinearMap.fst ℂ H H') : Set H) := by
      ext x
      constructor
      · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
        exact Submodule.mem_map_of_mem γ.2
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨_, ⟨⟨γ, hγ⟩, rfl⟩, rfl⟩
    rw [DenseRange, dense_iff_closure_eq,
      Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    erw [himg]
    rw [
      ← Submodule.topologicalClosure_coe]
    exact Set.eq_univ_of_forall fun y => y.2
  let T₀ : D →L[ℂ] H' := (f.extendOfIsometry hdense hnorm).toContinuousLinearMap
  refine ⟨T₀ ∘L D.orthogonalProjectionOnto, fun s hs => ?_⟩
  have hs' : s ∈ Γ := Submodule.subset_span hs
  have hproj : D.orthogonalProjectionOnto s.1 = e ⟨s, hs'⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := D) ⟨s.1, hmemD s hs'⟩
  simp only [ContinuousLinearMap.comp_apply, hproj, T₀,
    LinearIsometry.coe_toContinuousLinearMap, LinearMap.extendOfIsometry_eq]
  rfl

end Langlands.Analysis
