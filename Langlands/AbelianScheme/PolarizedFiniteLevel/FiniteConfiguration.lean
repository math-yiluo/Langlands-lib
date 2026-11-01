import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Projectivization.Action

/-! # Rigidity of finite configurations with sparse hyperplane intersections -/

noncomputable section

universe u v w z

open Module
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {I : Type w} [Fintype I]

/-- At most `q` entries of the indexed configuration lie in any linear hyperplane.
The count includes repeated entries. -/
def HyperplaneBound (v : I → V) (q : ℕ) : Prop :=
  ∀ (ℓ : V →ₗ[K] K), ℓ ≠ 0 → Nat.card {i : I // ℓ (v i) = 0} ≤ q

/-- Fewer than all configuration entries lie in a union of sufficiently few
hyperplanes. -/
theorem HyperplaneBound.exists_avoiding {v : I → V} {q : ℕ}
    (h : HyperplaneBound (K := K) v q) {J : Type z} [Fintype J]
    (ℓ : J → V →ₗ[K] K) (hℓ : ∀ j, ℓ j ≠ 0)
    (hsize : Fintype.card J * q < Fintype.card I) :
    ∃ i, ∀ j, ℓ j (v i) ≠ 0 := by
  classical
  let bad (j : J) : Finset I := Finset.univ.filter fun i => ℓ j (v i) = 0
  have hbad (j : J) : (bad j).card ≤ q := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h (ℓ j) (hℓ j)
  have hcard :
      (Finset.univ.biUnion bad).card ≤ Fintype.card J * q := by
    simpa using Finset.card_biUnion_le_card_mul Finset.univ bad q (fun j _ => hbad j)
  by_contra! hn
  have hunion : Finset.univ.biUnion bad = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨j, hj⟩ := hn i
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa [bad] using hj⟩
  rw [hunion, Finset.card_univ] at hcard
  exact (Nat.not_lt_of_ge hcard) hsize

/-- A configuration too large for one hyperplane spans the ambient vector space. -/
theorem HyperplaneBound.span_eq_top {v : I → V} {q : ℕ}
    (h : HyperplaneBound (K := K) v q) (hsize : q < Fintype.card I) :
    Submodule.span K (Set.range v) = ⊤ := by
  classical
  by_contra hn
  obtain ⟨ℓ, hℓ, hker⟩ :=
    (Submodule.span K (Set.range v)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
  have hall (i : I) : ℓ (v i) = 0 :=
    hker (Submodule.subset_span (Set.mem_range_self i))
  have hcard := h ℓ hℓ
  have : Nat.card {i : I // ℓ (v i) = 0} = Fintype.card I := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
  rw [this] at hcard
  exact (Nat.not_lt_of_ge hcard) hsize

/-- Fixing the lines of a basis and the line of a vector with every coordinate
nonzero forces a linear map to be scalar. -/
theorem scalar_of_basis_and_full_support {J : Type z} (b : Basis J K V)
    (f : V →ₗ[K] V) (hb : ∀ j, ∃ a : K, f (b j) = a • b j)
    {x : V} (hx : ∀ j, b.coord j x ≠ 0) {a : K} (hfx : f x = a • x) :
    f = a • LinearMap.id := by
  classical
  choose c hc using hb
  have hdiag (j : J) : (b.coord j).comp f = c j • b.coord j := by
    apply b.ext
    intro k
    by_cases hkj : k = j
    · subst k
      simp [hc, Basis.coord_apply]
    · simp [hc, Basis.coord_apply, Ne.symm hkj]
  have hca (j : J) : c j = a := by
    apply mul_right_cancel₀ (hx j)
    calc
      c j * b.coord j x = b.coord j (f x) := by
        simpa using (congrArg (fun L : V →ₗ[K] K => L x) (hdiag j)).symm
      _ = a * b.coord j x := by rw [hfx]; simp
  apply b.ext
  intro j
  simp [hc, hca]

/-- Under the hyperplane bound and its strict size inequality, a linear map
preserving every configuration line is scalar. -/
theorem HyperplaneBound.scalar_of_preserves_lines [FiniteDimensional K V]
    {v : I → V} {q : ℕ} (h : HyperplaneBound (K := K) v q)
    (hdim : 0 < finrank K V) (hsize : finrank K V * q < Fintype.card I)
    (f : V →ₗ[K] V) (hf : ∀ i, ∃ a : K, f (v i) = a • v i) :
    ∃ a : K, f = a • LinearMap.id := by
  classical
  have hq : q < Fintype.card I := calc
    q = 1 * q := by simp
    _ ≤ finrank K V * q := Nat.mul_le_mul_right q hdim
    _ < Fintype.card I := hsize
  have hspan := h.span_eq_top hq
  let J : Set V :=
    (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range v))
  let b : Basis J K V := Basis.ofSpan hspan.ge
  let : Finite J := Module.Finite.finite_basis b
  let : Fintype J := Fintype.ofFinite J
  have hb (j : J) : ∃ a : K, f (b j) = a • b j := by
    have hj : b j ∈ Set.range v := Basis.ofSpan_subset hspan.ge (Set.mem_range_self j)
    obtain ⟨i, hi⟩ := hj
    rw [← hi]
    exact hf i
  have hcoord (j : J) : b.coord j ≠ 0 := by
    intro hj
    have := congrArg (fun L : V →ₗ[K] K => L (b j)) hj
    simp [Basis.coord_apply] at this
  have hsize' : Fintype.card J * q < Fintype.card I := by
    rwa [← Module.finrank_eq_card_basis b]
  obtain ⟨i, hi⟩ := h.exists_avoiding (fun j => b.coord j) hcoord hsize'
  obtain ⟨a, ha⟩ := hf i
  exact ⟨a, scalar_of_basis_and_full_support b f hb hi ha⟩

/-- An ordered projective configuration satisfying the hyperplane size bound
has trivial pointwise stabilizer in the actual projective general linear group. -/
theorem HyperplaneBound.pgl_eq_one {J : Type z} [Fintype J] [DecidableEq J]
    [Nonempty J] (p : I → ℙ K (J → K)) {q : ℕ}
    (h : HyperplaneBound (K := K) (fun i => (p i).rep) q)
    (hsize : Fintype.card J * q < Fintype.card I)
    (e : PGL(J, K)) (he : ∀ i, e • p i = p i) : e = 1 := by
  induction e using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    let f : (J → K) →ₗ[K] J → K := DistribMulAction.toModuleEnd K (J → K) g
    have hf (i : I) : ∃ a : K, f (p i).rep = a • (p i).rep := by
      have hi := he i
      rw [← Projectivization.mk_rep (p i), Projectivization.PGL.mk_smul_mk,
        Projectivization.mk_eq_mk_iff'] at hi
      obtain ⟨a, ha⟩ := hi
      exact ⟨a, ha.symm⟩
    have hdim : 0 < finrank K (J → K) := by
      simpa only [Module.finrank_fintype_fun_eq_card] using Fintype.card_pos
    have hsize' : finrank K (J → K) * q < Fintype.card I := by
      simpa only [Module.finrank_fintype_fun_eq_card] using hsize
    obtain ⟨a, ha⟩ := h.scalar_of_preserves_lines hdim hsize' f hf
    have hscalar : (g : Matrix J J K) = Matrix.scalar J a := calc
      (g : Matrix J J K) = LinearMap.toMatrix' f := by
        change (g : Matrix J J K) =
          LinearMap.toMatrix' (Matrix.toLin' (g : Matrix J J K))
        exact (LinearMap.toMatrix'_toLin' _).symm
      _ = LinearMap.toMatrix' (a • LinearMap.id) := congrArg LinearMap.toMatrix' ha
      _ = Matrix.scalar J a := by
        exact LinearMap.toMatrix'_algebraMap a
    exact Matrix.ProjGenLinGroup.mk_eq_one.mpr
      (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, hscalar.symm⟩)

end Langlands.AbelianScheme.PolarizedFiniteLevel
