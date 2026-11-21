import Langlands.Correspondence.HenniartUnramified.Coinduction

/-! # Schur lemmas for block representations and properties of the explicit coinduction -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV uW

section Schur

variable {J : Type*} [Group J]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A finite-dimensional complex irreducible representation has only scalar endomorphisms. -/
theorem end_scalar [FiniteDimensional ℂ V] (ρ : Representation ℂ J V) (hi : ρ.IsIrreducible)
    (T : ρ.IntertwiningMap ρ) : ∃ c : ℂ, T.toLinearMap = c • (1 : Module.End ℂ V) := by
  let := hi
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective T
  exact ⟨c, (congrArg IntertwiningMap.toLinearMap hc).symm⟩

/-- A nonzero intertwiner between irreducible representations is an equivalence. -/
theorem nonempty_equiv_of_ne_zero (ρ : Representation ℂ J V) (σ : Representation ℂ J W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (T : ρ.IntertwiningMap σ) (hT : T ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  let := hρ
  let := hσ
  exact ⟨T.ofBijective ((IsIrreducible.bijective_or_eq_zero T).resolve_right hT)⟩

/-- Precomposition with a surjective homomorphism preserves irreducibility. -/
theorem isIrreducible_comp_surjective {J' : Type*} [Group J'] (ρ : Representation ℂ J V)
    (c : J' →* J) (hc : Function.Surjective c) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp c) := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp c) :=
    { toFun := fun S => ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (c h) hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g _ hv => by
        obtain ⟨h, rfl⟩ := hc g
        exact S.apply_mem_toSubmodule h hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mp hρ

end Schur

section BlockSchur

variable {J : Type*} [Group J] {I : Type*} [Fintype I] [DecidableEq I]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : I → Representation ℂ J V)

omit [Fintype I] in
theorem blockRep_single (n : J) (k : I) (w : V) :
    blockRep ρ n (Pi.single k w) = Pi.single k (ρ k n w) := by
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

/-- The `(j,k)` matrix entry of an inertia-equivariant endomorphism of the block representation. -/
def entry (T : (I → V) →ₗ[ℂ] (I → V)) (hT : ∀ n, T ∘ₗ blockRep ρ n = blockRep ρ n ∘ₗ T)
    (j k : I) : (ρ k).IntertwiningMap (ρ j) where
  toLinearMap := (LinearMap.proj j) ∘ₗ T ∘ₗ LinearMap.single ℂ (fun _ => V) k
  isIntertwining' n := by
    apply LinearMap.ext
    intro w
    have h := LinearMap.congr_fun (hT n) (Pi.single k w)
    simp only [LinearMap.comp_apply, blockRep_single] at h
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.coe_proj,
      Function.eval]
    rw [h]
    rfl

variable [FiniteDimensional ℂ V]

/-- With irreducible pairwise unrelated blocks, every equivariant endomorphism is diagonal. -/
theorem blockRep_endo_diag (hirr : ∀ k, (ρ k).IsIrreducible)
    (hdist : ∀ j k, j ≠ k → ∀ T : (ρ j).IntertwiningMap (ρ k), T = 0)
    (T : (I → V) →ₗ[ℂ] (I → V)) (hT : ∀ n, T ∘ₗ blockRep ρ n = blockRep ρ n ∘ₗ T) :
    ∃ c : I → ℂ, ∀ v k, T v k = c k • v k := by
  choose c hc using fun k => end_scalar (ρ k) (hirr k) (entry ρ T hT k k)
  refine ⟨c, fun v k => ?_⟩
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · have h := LinearMap.congr_fun (hc k) (v k)
    simpa [entry] using h
  · intro i _ hik
    have h0 := hdist i k hik (entry ρ T hT k i)
    have h := congrArg (fun F : (ρ i).IntertwiningMap (ρ k) => F (v i)) h0
    simpa [entry] using h
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [FiniteDimensional ℂ V] in
/-- A nonzero equivariant map from the block representation to an irreducible representation
identifies the target with one of the blocks. -/
theorem exists_block_equiv {Y : Type uW} [AddCommGroup Y] [Module ℂ Y]
    (y : Representation ℂ J Y) (hy : y.IsIrreducible) (hirr : ∀ k, (ρ k).IsIrreducible)
    (P : (I → V) →ₗ[ℂ] Y) (hP : ∀ n, P ∘ₗ blockRep ρ n = y n ∘ₗ P) (hP0 : P ≠ 0) :
    ∃ k, Nonempty ((ρ k).Equiv y) := by
  by_contra! hnone
  apply hP0
  apply LinearMap.ext
  intro v
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  let F : (ρ i).IntertwiningMap y :=
    { toLinearMap := P ∘ₗ LinearMap.single ℂ (fun _ => V) i
      isIntertwining' := fun n => by
        apply LinearMap.ext
        intro w
        have h := LinearMap.congr_fun (hP n) (Pi.single i w)
        simp only [LinearMap.comp_apply, blockRep_single] at h
        simpa using h }
  have hF : F = 0 := by
    by_contra hF
    exact (hnone i).false (nonempty_equiv_of_ne_zero _ _ (hirr i) hy F hF).some
  have := congrArg (fun F : (ρ i).IntertwiningMap y => F (v i)) hF
  simpa [F] using this

end BlockSchur

end Langlands.FiniteRepresentation.SplitDegree
