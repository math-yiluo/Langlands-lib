import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Whittaker.UpperUnipotentCoinvariantReduction

/-! # Standard block shapes for a pair of complementary idempotents

For complementary nonzero idempotents `e₁, e₂` of `End_F(F^n)` with `e₂ e₁ = 0`, a basis
adapted to `F^n = e₁ F^n ⊕ e₂ F^n` conjugates the standard two-block upper unipotent radical
into the group `1 + e₁ A e₂`.
-/

noncomputable section

namespace Langlands.BushnellKutzko.SplitBlocks

open GeneralLinear

universe uF

variable {F : Type uF} [Field F] {n : ℕ}

local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- A block unipotent matrix for the cut at `a` is `1 + d (x − 1) (1 − d)`, where `d` is the
diagonal idempotent of the first `a` coordinates. -/
theorem diagonal_mul_sub_one_mul {a : ℕ} {x : GeneralLinear n F}
    (hx : Classification.SupercuspidalDerivativeVanishing.IsBlockUnipotent a x) :
    Matrix.diagonal (fun i : Fin n => if (i : ℕ) < a then (1 : F) else 0) * (x.val - 1) *
      (1 - Matrix.diagonal (fun i : Fin n => if (i : ℕ) < a then (1 : F) else 0)) =
      x.val - 1 := by
  classical
  ext i j
  have hdiag : (1 : Matrix (Fin n) (Fin n) F) -
      Matrix.diagonal (fun i : Fin n => if (i : ℕ) < a then (1 : F) else 0) =
      Matrix.diagonal (fun i : Fin n => 1 - if (i : ℕ) < a then (1 : F) else 0) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · have h := hx i j (Or.inl hj)
    simp only [hi, hj, ↓reduceIte, sub_self, mul_zero]
    rw [Matrix.sub_apply, h, Matrix.one_apply, sub_self]
  · simp [hi, hj]
  · have h := hx i j (Or.inr (Nat.le_of_not_lt hi))
    simp only [hi, hj, ↓reduceIte, sub_self, mul_zero, zero_mul]
    rw [Matrix.sub_apply, h, Matrix.one_apply, sub_self]
  · have h := hx i j (Or.inr (Nat.le_of_not_lt hi))
    simp only [hi, hj, ↓reduceIte, zero_mul]
    rw [Matrix.sub_apply, h, Matrix.one_apply, sub_self]

/-- **The standard block shape of a splitting.** For complementary nonzero idempotents
`e₁, e₂` of `End_F(F^n)` with `e₁ e₂ = e₂ e₁ = 0`, some proper two-block shape `B` and some
`g ∈ GL_n(F)` satisfy `g U_B g⁻¹ ⊆ 1 + e₁ A e₂` in matrix coordinates. -/
theorem exists_blockShape_conjugateUnipotent_le {e₁ e₂ : A} (hsum : e₁ + e₂ = 1)
    (h12 : e₁ * e₂ = 0) (h21 : e₂ * e₁ = 0) (hne₁ : e₁ ≠ 0) (hne₂ : e₂ ≠ 0) :
    ∃ B : BlockShape n, B.parabolic F ≠ ⊤ ∧ ∃ g : GeneralLinear n F,
      B.conjugateUnipotent g ≤ (blockUnipotent e₁ e₂ h21 ⊤).map (toAut).symm.toMonoidHom := by
  classical
  have h11 : e₁ * e₁ = e₁ := by
    calc e₁ * e₁ = e₁ * (e₁ + e₂) := by rw [mul_add, h12, add_zero]
      _ = e₁ := by rw [hsum, mul_one]
  have h22 : e₂ * e₂ = e₂ := by
    calc e₂ * e₂ = (e₁ + e₂) * e₂ := by rw [add_mul, h12, zero_add]
      _ = e₂ := by rw [hsum, one_mul]
  set V₁ := LinearMap.range e₁ with hV₁
  set V₂ := LinearMap.range e₂ with hV₂
  have he₁V₁ : ∀ v ∈ V₁, e₁ v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, h11]
  have he₁V₂ : ∀ v ∈ V₂, e₁ v = 0 := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, h12, LinearMap.zero_apply]
  have hc : IsCompl V₁ V₂ := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv₁ hv₂
      rw [← he₁V₁ v hv₁, he₁V₂ v hv₂]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v = e₁ v + e₂ v := by
        rw [← LinearMap.add_apply, hsum, Module.End.one_apply]
      rw [hv]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  set a := Module.finrank F V₁ with ha_def
  have hdim : a + Module.finrank F V₂ = n := by
    rw [ha_def, Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]
  have ha : 0 < a := by
    rw [ha_def, Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨v, hv⟩ : ∃ v, e₁ v ≠ 0 := by
      by_contra! h
      exact hne₁ (LinearMap.ext h)
    exact ⟨⟨e₁ v, v, rfl⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hb : 0 < Module.finrank F V₂ := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨v, hv⟩ : ∃ v, e₂ v ≠ 0 := by
      by_contra! h
      exact hne₂ (LinearMap.ext h)
    exact ⟨⟨e₂ v, v, rfl⟩, fun h => hv (congrArg Subtype.val h)⟩
  have haN : a < n := by omega
  let b₁ : Module.Basis (Fin a) F V₁ := Module.finBasisOfFinrankEq F V₁ rfl
  let b₂ : Module.Basis (Fin (n - a)) F V₂ := Module.finBasisOfFinrankEq F V₂ (by omega)
  let bs : Module.Basis (Fin a ⊕ Fin (n - a)) F (Fin n → F) :=
    (b₁.prod b₂).map (Submodule.prodEquivOfIsCompl V₁ V₂ hc)
  let σ : Fin a ⊕ Fin (n - a) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  let bb := bs.reindex σ
  let φ : (Fin n → F) ≃ₗ[F] (Fin n → F) := (Pi.basisFun F (Fin n)).equiv bb (Equiv.refl _)
  let u : Aut := ⟨(φ : A), (φ.symm : A), by ext v; simp, by ext v; simp⟩
  -- the diagonal idempotent of the first `a` coordinates
  let d : Fin n → F := fun i => if (i : ℕ) < a then 1 else 0
  let E₁ : A := Matrix.toLinAlgEquiv' (Matrix.diagonal d)
  have hbb : ∀ s, bb (σ s) = Sum.elim (fun j => ((b₁ j : V₁) : Fin n → F))
      (fun j => ((b₂ j : V₂) : Fin n → F)) s := by
    intro s
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply,
      Submodule.coe_prodEquivOfIsCompl']
    cases s with
    | inl j => simp
    | inr j => simp
  have hσ : ∀ s, ((σ s : Fin n) : ℕ) < a ↔ s.isLeft := by
    intro s
    cases s with
    | inl j => simp [σ, j.isLt]
    | inr j => simp [σ]
  have hPE : (u : A) * E₁ = e₁ * (u : A) := by
    apply (Pi.basisFun F (Fin n)).ext
    intro i
    obtain ⟨s, rfl⟩ := σ.surjective i
    have hφ : (u : A) (Pi.basisFun F (Fin n) (σ s)) = bb (σ s) := by
      change φ (Pi.basisFun F (Fin n) (σ s)) = _
      simp only [φ, Module.Basis.equiv_apply, Equiv.refl_apply]
    have hE : E₁ (Pi.basisFun F (Fin n) (σ s)) = d (σ s) • Pi.basisFun F (Fin n) (σ s) := by
      simp only [E₁, Matrix.toLinAlgEquiv'_apply, Pi.basisFun_apply,
        Matrix.diagonal_mulVec_single, mul_one]
      ext k
      simp [Pi.single_apply]
    rw [Module.End.mul_apply, Module.End.mul_apply, hE, map_smul, hφ, hbb]
    cases s with
    | inl j =>
      have hd : d (σ (Sum.inl j)) = 1 := by simp [d, (hσ (Sum.inl j)).mpr rfl]
      rw [hd, one_smul]
      exact (he₁V₁ _ (b₁ j).2).symm
    | inr j =>
      have hd : d (σ (Sum.inr j)) = 0 := by
        have := (hσ (Sum.inr j)).not.mpr (by simp)
        simp [d, this]
      rw [hd, zero_smul]
      exact (he₁V₂ _ (b₂ j).2).symm
  have hu : (u : A) * ((u⁻¹ : Aut) : A) = 1 := Units.mul_inv u
  have hu' : ((u⁻¹ : Aut) : A) * (u : A) = 1 := Units.inv_mul u
  have hEP : E₁ * ((u⁻¹ : Aut) : A) = ((u⁻¹ : Aut) : A) * e₁ := by
    calc E₁ * ((u⁻¹ : Aut) : A) = (((u⁻¹ : Aut) : A) * (u : A)) * E₁ * ((u⁻¹ : Aut) : A) := by
          rw [hu', one_mul]
      _ = ((u⁻¹ : Aut) : A) * ((u : A) * E₁) * ((u⁻¹ : Aut) : A) := by noncomm_ring
      _ = ((u⁻¹ : Aut) : A) * (e₁ * (u : A)) * ((u⁻¹ : Aut) : A) := by rw [hPE]
      _ = ((u⁻¹ : Aut) : A) * e₁ * ((u : A) * ((u⁻¹ : Aut) : A)) := by noncomm_ring
      _ = ((u⁻¹ : Aut) : A) * e₁ := by rw [hu, mul_one]
  refine ⟨ProductLeviChamber.twoBlock n a ha haN,
    Whittaker.UpperUnipotentCoinvariant.cutShape_parabolic_ne_top (F := F) n a ha haN,
    (toAut).symm u, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hbu := Whittaker.UpperUnipotentCoinvariant.isBlockUnipotent_of_mem_cutShape ha haN hx
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨?_, AddSubgroup.mem_top _⟩
  -- the conjugate in `Aut`
  have hconj : toAut ((MulAut.conj ((toAut).symm u)).toMonoidHom x) = u * toAut x * u⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hconj]
  set N : A := ((toAut x : Aut) : A) - 1 with hN
  have hNE : N = E₁ * N * (1 - E₁) := by
    have hx' : ((toAut x : Aut) : A) = Matrix.toLinAlgEquiv' x.val := rfl
    rw [hN, hx', show (1 : A) = Matrix.toLinAlgEquiv' 1 from (map_one _).symm, ← map_sub,
      show E₁ = Matrix.toLinAlgEquiv' (Matrix.diagonal d) from rfl, ← map_sub, ← map_mul,
      ← map_mul, diagonal_mul_sub_one_mul hbu]
  have hX : ((u * toAut x * u⁻¹ : Aut) : A) - 1 = (u : A) * N * ((u⁻¹ : Aut) : A) := by
    rw [Units.val_mul, Units.val_mul, hN, mul_sub, sub_mul, mul_one, hu]
  rw [hX]
  have he₂ : e₂ = 1 - e₁ := by rw [← hsum]; abel
  have hXe : (u : A) * N * ((u⁻¹ : Aut) : A) =
      e₁ * ((u : A) * N * ((u⁻¹ : Aut) : A)) * e₂ := by
    conv_lhs => rw [hNE]
    rw [he₂]
    calc (u : A) * (E₁ * N * (1 - E₁)) * ((u⁻¹ : Aut) : A)
        = ((u : A) * E₁) * N * (((u⁻¹ : Aut) : A) - E₁ * ((u⁻¹ : Aut) : A)) := by
          simp only [mul_sub, sub_mul, mul_one, mul_assoc]
      _ = (e₁ * (u : A)) * N * (((u⁻¹ : Aut) : A) - ((u⁻¹ : Aut) : A) * e₁) := by
          rw [hPE, hEP]
      _ = e₁ * ((u : A) * N * ((u⁻¹ : Aut) : A)) * (1 - e₁) := by
          simp only [mul_sub, mul_one, mul_assoc]
  exact hXe.symm

end Langlands.BushnellKutzko.SplitBlocks
