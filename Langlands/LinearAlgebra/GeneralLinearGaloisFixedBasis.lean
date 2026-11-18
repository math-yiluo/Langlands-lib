import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Galois-fixed bases for `GL_n`-valued cocycles (Hilbert 90 for `GL_n`) -/

noncomputable section

universe u

open Module Matrix

namespace Langlands.LinearAlgebra.GaloisFixedBasis

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Dedekind's lemma for the automorphisms of `L` over `K`. -/
theorem linearIndependent_automorphisms :
    LinearIndependent L (fun τ : L ≃ₐ[K] L => (τ : L → L)) :=
  LinearIndependent.comp (ι' := L ≃ₐ[K] L)
    (linearIndependent_monoidHom L L) (fun f => f)
    (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)

variable [FiniteDimensional K L] (g : (L ≃ₐ[K] L) → GL n L)

/-- The twisted Galois average `∑_τ g_τ τ(v)` of a vector `v`. -/
def average (v : n → L) : n → L :=
  ∑ τ, (g τ : Matrix n n L) *ᵥ (fun i => τ (v i))

omit [FiniteDimensional K L] in
/-- A cocycle takes the value one at the identity. -/
theorem cocycle_one
    (hg : ∀ σ τ, g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ)) :
    g 1 = 1 := by
  have h := hg 1 1
  have hid : ((1 : L ≃ₐ[K] L) : L →+* L) = RingHom.id L := RingHom.ext fun _ => rfl
  rw [hid, GeneralLinearGroup.map_id, MonoidHom.id_apply, mul_one] at h
  exact left_eq_mul.mp h

variable {g}

/-- Twisted Galois averages are fixed by the twisted Galois action. -/
theorem average_fixed
    (hg : ∀ σ τ, g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ))
    (σ : L ≃ₐ[K] L) (v : n → L) :
    (g σ : Matrix n n L) *ᵥ (fun i => σ (average g v i)) = average g v := by
  have h1 : (fun i => σ (average g v i)) =
      ∑ τ, ((g τ : Matrix n n L).map (σ : L →+* L)) *ᵥ (fun i => σ (τ (v i))) := by
    funext i
    simp only [average, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h := RingHom.map_mulVec (σ : L →+* L) (g τ : Matrix n n L) (fun i => τ (v i)) i
    exact h
  have h2 : ∀ τ, (g σ : Matrix n n L) *ᵥ (((g τ : Matrix n n L).map (σ : L →+* L)) *ᵥ
      (fun i => σ (τ (v i)))) = (g (σ * τ) : Matrix n n L) *ᵥ (fun i => (σ * τ) (v i)) := by
    intro τ
    rw [Matrix.mulVec_mulVec, hg σ τ, Units.val_mul]
    congr 1
  rw [h1, Matrix.mulVec_sum]
  rw [Finset.sum_congr rfl fun τ _ => h2 τ]
  exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => (g τ : Matrix n n L) *ᵥ fun i => τ (v i))

/-- A linear functional killing every twisted Galois average vanishes. -/
theorem dual_eq_zero
    (hg : ∀ σ τ, g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ))
    (f : Module.Dual L (n → L)) (hfa : ∀ v, f (average g v) = 0) : f = 0 := by
  apply (Pi.basisFun L n).ext
  intro i
  rw [Pi.basisFun_apply, LinearMap.zero_apply]
  let c : (L ≃ₐ[K] L) → L := fun τ => f ((g τ : Matrix n n L) *ᵥ Pi.single i 1)
  have hav : ∀ l : L, average g (Pi.single i l) =
      ∑ τ, τ l • ((g τ : Matrix n n L) *ᵥ Pi.single i 1) := by
    intro l
    simp only [average]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hs : (fun k => τ ((Pi.single i l : n → L) k)) = τ l • Pi.single i (1 : L) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [hs, Matrix.mulVec_smul]
  have hc : ∑ τ, c τ • (τ : L → L) = 0 := by
    funext l
    have hv := hfa (Pi.single i l)
    rw [hav, map_sum] at hv
    simp only [map_smul, smul_eq_mul] at hv
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hv]
    exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have hli : LinearIndependent L (fun τ : L ≃ₐ[K] L => (τ : L → L)) :=
    linearIndependent_automorphisms
  rw [Fintype.linearIndependent_iff] at hli
  have h1 := hli c hc 1
  have hg1 := cocycle_one g hg
  simp only [c, hg1, Units.val_one, Matrix.one_mulVec] at h1
  exact h1

/-- The twisted Galois averages span `Lⁿ`. -/
theorem span_range_average
    (hg : ∀ σ τ, g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ)) :
    ⊤ ≤ Submodule.span L (Set.range (average g)) := by
  rw [top_le_iff]
  by_contra hne
  have hlt : Submodule.span L (Set.range (average g)) < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt
    (Module.Projective.of_free)
  apply hf0
  apply dual_eq_zero hg f
  intro v
  have hv : f (average g v) ∈ (Submodule.span L (Set.range (average g))).map f :=
    Submodule.mem_map_of_mem (Submodule.subset_span ⟨v, rfl⟩)
  rw [hfS] at hv
  exact (Submodule.mem_bot L).1 hv

/-- **Hilbert 90 for `GL_n`.** Every `GL_n(L)`-valued cocycle of the automorphism group of a
finite extension `L/K` is a coboundary: there is an invertible matrix `P` with
`g_σ σ(P) = P` for every automorphism `σ`. -/
theorem exists_fixed
    (hg : ∀ σ τ, g (σ * τ) = g σ * GeneralLinearGroup.map (σ : L →+* L) (g τ)) :
    ∃ P : GL n L, ∀ σ, g σ * GeneralLinearGroup.map (σ : L →+* L) P = P := by
  let b₀ := Basis.ofSpan (span_range_average hg)
  let b : Basis n L (n → L) := b₀.reindex (b₀.indexEquiv (Pi.basisFun L n))
  have hb : ∀ j, ∃ v, average g v = b j := by
    intro j
    have hmem : b j ∈ Set.range b₀ := by
      simp only [b, Basis.reindex_apply]
      exact Set.mem_range_self _
    obtain ⟨v, hv⟩ := Basis.ofSpan_subset (span_range_average hg) hmem
    exact ⟨v, hv⟩
  have hfix : ∀ σ j, (g σ : Matrix n n L) *ᵥ (fun i => σ (b j i)) = b j := by
    intro σ j
    obtain ⟨v, hv⟩ := hb j
    rw [← hv]
    exact average_fixed hg σ v
  let P : GL n L :=
    ⟨(Pi.basisFun L n).toMatrix b, b.toMatrix (Pi.basisFun L n),
      Basis.toMatrix_mul_toMatrix_flip _ _, Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨P, fun σ => ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul]
  change ((g σ : Matrix n n L) * ((Pi.basisFun L n).toMatrix b).map (σ : L →+* L)) i j =
    (Pi.basisFun L n).toMatrix b i j
  have h := congrFun (hfix σ j) i
  rw [Matrix.mul_apply, Basis.toMatrix_apply, Pi.basisFun_repr, ← h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Basis.toMatrix_apply,
    Pi.basisFun_repr]
  rfl

end Langlands.LinearAlgebra.GaloisFixedBasis
