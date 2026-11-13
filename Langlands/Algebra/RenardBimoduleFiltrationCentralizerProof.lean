import Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement

/-! Proof of Renard VI.10.4, the Lemma on centralizers of filtered bimodules. -/

open scoped TensorProduct

namespace Langlands.Algebra

universe u v

/-- Renard VI.10.4, Lemma: the centralizer of a filtered bimodule whose
successive quotients admit no nonzero bimodule morphisms between distinct ones
is the intersection of the centralizers of the quotients. -/
theorem renardBimoduleFiltrationCentralizer :
    RenardBimoduleFiltrationCentralizerStatement.{u, v} := by
  intro A _ M _ _ n F h0 hn _hmono hhom
  let _ : ∀ i, AddCommGroup ↥(F i) := fun i => (F i).addCommGroup
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
  constructor
  · -- `𝒞(M) ⊆ 𝒞(Q_i)`.
    intro ha i _ x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
      congr 1
      exact Subtype.ext (ha (y : M))
  · -- `⋂ 𝒞(Q_i) ⊆ 𝒞(M)`.
    intro ha
    -- The difference of the two actions of `a`, a linear endomorphism of `M`.
    let D : M →ₗ[A ⊗[ℕ] Aᵐᵒᵖ] M :=
      { toFun := fun x => (a ⊗ₜ[ℕ] (1 : Aᵐᵒᵖ)) • x - ((1 : A) ⊗ₜ[ℕ] MulOpposite.op a) • x
        map_add' := fun x y => by
          simp only [smul_add]
          abel
        map_smul' := fun r x => by
          simp only [RingHom.id_apply, smul_sub]
          rw [smul_comm r (a ⊗ₜ[ℕ] (1 : Aᵐᵒᵖ)) x, smul_comm r ((1 : A) ⊗ₜ[ℕ] MulOpposite.op a) x] }
    have hDapp : ∀ x, D x =
        (a ⊗ₜ[ℕ] (1 : Aᵐᵒᵖ)) • x - ((1 : A) ⊗ₜ[ℕ] MulOpposite.op a) • x := fun _ => rfl
    -- `D` maps `F i` into `F (i + 1)`, because `a` centralizes `Q_i`.
    have hDstep : ∀ i ≤ n, ∀ y ∈ F i, D y ∈ F (i + 1) := by
      intro i hi y hy
      have h := ha i (Nat.lt_succ_of_le hi)
        (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(F i)))
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
        ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
      simpa [hDapp] using h
    -- No nonzero morphism `Q_k → M` has image inside `F j` for `k < j`.
    have hvanish : ∀ k ≤ n, ∀ m j, j + m = n + 1 → k < j →
        ∀ g : (↥(F k) ⧸ (F (k + 1)).comap (F k).subtype) →ₗ[A ⊗[ℕ] Aᵐᵒᵖ] M,
          (∀ x, g x ∈ F j) → g = 0 := by
      intro k hk m
      induction m with
      | zero =>
        intro j hj _ g hg
        refine LinearMap.ext fun x => ?_
        have hx := hg x
        rw [show j = n + 1 by omega, hn, Submodule.mem_bot] at hx
        exact hx
      | succ m ih =>
        intro j hj hkj g hg
        let g' : (↥(F k) ⧸ (F (k + 1)).comap (F k).subtype) →ₗ[A ⊗[ℕ] Aᵐᵒᵖ]
            (↥(F j) ⧸ (F (j + 1)).comap (F j).subtype) :=
          ((F (j + 1)).comap (F j).subtype).mkQ ∘ₗ g.codRestrict (F j) hg
        have hg' : g' = 0 := hhom k hk j (by omega) (by omega) g'
        refine ih (j + 1) (by omega) (by omega) g fun x => ?_
        have hx : g' x = 0 := by rw [hg']; rfl
        simp only [g', LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
        simpa using hx
    -- `D` vanishes on every `F k`, by descending induction on `k`.
    have hzero : ∀ m k, k + m = n + 1 → ∀ y ∈ F k, D y = 0 := by
      intro m
      induction m with
      | zero =>
        intro k hk y hy
        rw [show k = n + 1 by omega, hn, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      | succ m ih =>
        intro k hk y hy
        have hkn : k ≤ n := by omega
        let g : (↥(F k) ⧸ (F (k + 1)).comap (F k).subtype) →ₗ[A ⊗[ℕ] Aᵐᵒᵖ] M :=
          ((F (k + 1)).comap (F k).subtype).liftQ (D ∘ₗ (F k).subtype) (by
            intro z hz
            rw [Submodule.mem_comap] at hz
            exact ih (k + 1) (by omega) _ hz)
        have hg : g = 0 := hvanish k hkn m (k + 1) (by omega) (by omega) g (by
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H z => exact hDstep k hkn z z.2)
        have := LinearMap.congr_fun hg (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(F k)))
        exact this
    intro x
    have hx := hzero (n + 1) 0 (by omega) x (by rw [h0]; exact Submodule.mem_top)
    rw [hDapp, sub_eq_zero] at hx
    exact hx

end Langlands.Algebra
