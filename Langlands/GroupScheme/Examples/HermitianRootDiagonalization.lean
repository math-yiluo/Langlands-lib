/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser

Worker 98 adapted the orthogonal-basis induction below from Mathlib's
LinearMap.BilinForm.exists_orthogonal_basis.
-/
import Langlands.GroupScheme.Examples.HermitianRootReflectionAction
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Diagonal coordinates for anisotropic Hermitian spaces -/

noncomputable section

universe u v

namespace Langlands.Sesquilinear

open Module LinearMap

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {I : K →+* K}

/-- A nonisotropic line has its right orthogonal subspace as a complement. -/
theorem isCompl_span_orthogonal {B : V →ₛₗ[I] V →ₗ[K] K} {x : V}
    (hx : B x x ≠ 0) : IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B) where
  disjoint := disjoint_iff.2 (LinearMap.span_singleton_inf_orthogonal_eq_bot B x hx)
  codisjoint := codisjoint_iff.2 (by
    rw [Submodule.orthogonalBilin_span_singleton]
    exact LinearMap.span_singleton_sup_ker_eq_top (B x) hx)

/-- An anisotropic reflexive sesquilinear form admits an orthogonal basis in every
characteristic. The second argument of the form is linear. -/
theorem exists_orthogonal_basis [FiniteDimensional K V] {B : V →ₛₗ[I] V →ₗ[K] K}
    (hB : B.IsRefl) (ha : ∀ x, B x x = 0 → x = 0) :
    ∃ b : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ b := by
  suffices ∀ d, finrank K V = d → ∃ b : Basis (Fin d) K V, B.IsOrthoᵢ b by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
    have : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp (by omega)
    obtain ⟨x, hx0⟩ := exists_ne (0 : V)
    have hx : B x x ≠ 0 := fun h => hx0 (ha x h)
    rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_orthogonal hx).symm,
      finrank_span_singleton hx0] at hd
    let N := (K ∙ x).orthogonalBilin B
    let B' := B.domRestrict₁₂ N N
    have ha' : ∀ y : N, B' y y = 0 → y = 0 := by
      intro y hy
      exact Subtype.ext (ha y hy)
    obtain ⟨b', hb'⟩ := ih (hB.domRestrict N : B'.IsRefl) ha' (Nat.succ.inj hd)
    let b := Basis.mkFinCons x b'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have hdj := (isCompl_span_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at hdj
        have hz := hdj (c • x)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hy
        exact (smul_eq_zero.mp hz).resolve_right hx0)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        rw [map_smulₛₗ, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hx, add_neg_cancel, mul_zero])
    refine ⟨b, ?_⟩
    rw [Basis.coe_mkFinCons]
    intro j i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
      simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
    · exact (hij rfl).elim
    · exact hB _ _ ((b' j).prop _ (Submodule.mem_span_singleton_self x))
    · exact (b' i).prop _ (Submodule.mem_span_singleton_self x)
    · exact hb' (ne_of_apply_ne _ hij)

end Langlands.Sesquilinear

namespace Langlands.GroupScheme.HermitianRoot

open Module SU3Root

variable {L : Type u} {V : Type v} [Field L] [AddCommGroup V] [Module L V]
  {c : RingInvolution L}
  (h : V →ₗ[L] V →ₛₗ[c.bar.toRingHom] L)
  (hbar : ∀ x y, c.bar (h x y) = h y x)
  (ha : ∀ x, h x x = 0 → x = 0)

/-- A chosen orthogonal basis for an anisotropic Hermitian space. -/
def orthogonalBasisOfAnisotropic [FiniteDimensional L V] :
    Basis (Fin (finrank L V)) L V :=
  Classical.choose (Sesquilinear.exists_orthogonal_basis (B := h.flip)
    (fun x y hz => by
      change h x y = 0
      change h y x = 0 at hz
      rw [← hbar y x, hz, map_zero]) ha)

theorem orthogonalBasisOfAnisotropic_isOrtho [FiniteDimensional L V] :
    h.IsOrthoᵢ (orthogonalBasisOfAnisotropic h hbar ha) := by
  apply (LinearMap.isOrthoᵢ_flip h).mpr
  exact Classical.choose_spec (Sesquilinear.exists_orthogonal_basis (B := h.flip)
    (fun x y hz => by
      change h x y = 0
      change h y x = 0 at hz
      rw [← hbar y x, hz, map_zero]) ha)

/-- The actual diagonal form in the chosen orthogonal basis. -/
def diagonalFormOfAnisotropic [FiniteDimensional L V] :
    DiagonalForm c (Fin (finrank L V)) where
  weight i := h (orthogonalBasisOfAnisotropic h hbar ha i)
    (orthogonalBasisOfAnisotropic h hbar ha i)
  bar_weight _i := hbar _ _

/-- The coordinates are an equivalence of vector spaces over the extension field. -/
def diagonalCoordinatesOfAnisotropic [FiniteDimensional L V] :
    V ≃ₗ[L] (Fin (finrank L V) → L) :=
  (orthogonalBasisOfAnisotropic h hbar ha).equivFun

omit hbar ha in
/-- Expansion in an orthogonal basis gives precisely the diagonal Hermitian sum. -/
theorem pairing_eq_diagonal_sum {ι : Type*} [Fintype ι] (b : Basis ι L V)
    (hb : h.IsOrthoᵢ b) (x y : V) :
    h x y = ∑ i, h (b i) (b i) * b.equivFun x i * c.bar (b.equivFun y i) := by
  classical
  conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · change c.bar (b.equivFun y i) * (b.equivFun x i * h (b i) (b i)) =
      h (b i) (b i) * b.equivFun x i * c.bar (b.equivFun y i)
    ring
  · intro j _ hji
    rw [hb hji]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coordinate equivalence preserves the entire Hermitian pairing. -/
theorem diagonalFormOfAnisotropic_pairing [FiniteDimensional L V] (x y : V) :
    (diagonalFormOfAnisotropic h hbar ha).pairing
      (diagonalCoordinatesOfAnisotropic h hbar ha x)
      (diagonalCoordinatesOfAnisotropic h hbar ha y) = h x y := by
  exact (pairing_eq_diagonal_sum h (orthogonalBasisOfAnisotropic h hbar ha)
    (orthogonalBasisOfAnisotropic_isOrtho h hbar ha) x y).symm

/-- The resulting diagonal model remains anisotropic. -/
theorem diagonalFormOfAnisotropic_isAnisotropic [FiniteDimensional L V] :
    (diagonalFormOfAnisotropic h hbar ha).IsAnisotropic := by
  intro x hx
  let e := diagonalCoordinatesOfAnisotropic h hbar ha
  have he := diagonalFormOfAnisotropic_pairing h hbar ha (e.symm x) (e.symm x)
  change (diagonalFormOfAnisotropic h hbar ha).pairing (e (e.symm x)) (e (e.symm x)) =
    h (e.symm x) (e.symm x) at he
  rw [e.apply_symm_apply] at he
  have hz := he.symm.trans hx
  have hv := ha (e.symm x) hz
  have := congrArg e hv
  simpa using this

/-- Every chosen diagonal weight is nonzero. -/
theorem diagonalFormOfAnisotropic_weight_ne_zero [FiniteDimensional L V]
    (i : Fin (finrank L V)) : (diagonalFormOfAnisotropic h hbar ha).weight i ≠ 0 := by
  intro hi
  exact (orthogonalBasisOfAnisotropic h hbar ha).ne_zero i (ha _ hi)

include hbar ha in
/-- An actual anisotropic diagonal form and pairing-preserving linear coordinates. -/
theorem exists_anisotropic_diagonal_coordinates [FiniteDimensional L V] :
    ∃ H : DiagonalForm c (Fin (finrank L V)), H.IsAnisotropic ∧
      ∃ e : V ≃ₗ[L] (Fin (finrank L V) → L), ∀ x y, H.pairing (e x) (e y) = h x y :=
  ⟨diagonalFormOfAnisotropic h hbar ha, diagonalFormOfAnisotropic_isAnisotropic h hbar ha,
    diagonalCoordinatesOfAnisotropic h hbar ha, diagonalFormOfAnisotropic_pairing h hbar ha⟩

end Langlands.GroupScheme.HermitianRoot
