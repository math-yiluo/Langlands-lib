import Langlands.GroupScheme.SplitExistence.Points

/-! # Weyl elements of the Chevalley group over a field

For a simple root `i`, the Weyl element `n_i = φ_i([[0, 1], [-1, 0]])`. It moves the basis vectors
of weight `μ` into the span of those of weight `s_i μ`; it normalizes the torus through `s_i`; its square lies in the torus; and the rank-one identity
`x_{-i}(u) = x_i(u⁻¹) α_i^∨(-u⁻¹) n_i x_i(u⁻¹)` holds for units `u`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

/-! ### Identities in `SL₂` -/

section SL2

variable {R : Type*} [CommRing R]

theorem sl2Weyl_eq : (sl2Weyl : SpecialLinearGroup (Fin 2) R) =
    sl2Upper 1 * sl2Lower (-1) * sl2Upper 1 := by
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] = !![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]
  simp

theorem sl2Weyl_mul_diag (t : Rˣ) :
    (sl2Weyl : SpecialLinearGroup (Fin 2) R) * sl2Diag t = sl2Diag t⁻¹ * sl2Weyl := by
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] * !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)] =
    !![((t⁻¹ : Rˣ) : R), 0; 0, (((t⁻¹)⁻¹ : Rˣ) : R)] * !![(0 : R), 1; -1, 0]
  simp

theorem sl2Weyl_mul_self :
    (sl2Weyl : SpecialLinearGroup (Fin 2) R) * sl2Weyl = sl2Diag (-1) := by
  apply Subtype.ext
  change !![(0 : R), 1; -1, 0] * !![(0 : R), 1; -1, 0] =
    !![(((-1 : Rˣ)) : R), 0; 0, (((-1 : Rˣ)⁻¹ : Rˣ) : R)]
  simp

theorem sl2Lower_eq (u : Rˣ) :
    (sl2Lower (u : R) : SpecialLinearGroup (Fin 2) R) =
      sl2Upper ((u⁻¹ : Rˣ) : R) * sl2Diag (-u⁻¹) * sl2Weyl * sl2Upper ((u⁻¹ : Rˣ) : R) := by
  apply Subtype.ext
  change !![(1 : R), 0; (u : R), 1] =
    !![1, ((u⁻¹ : Rˣ) : R); 0, 1] * !![(((-u⁻¹ : Rˣ)) : R), 0; 0, (((-u⁻¹ : Rˣ)⁻¹ : Rˣ) : R)] *
      !![(0 : R), 1; -1, 0] * !![1, ((u⁻¹ : Rˣ) : R); 0, 1]
  simp only [Matrix.mul_fin_two, Units.val_neg, inv_neg, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end SL2

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [Field K]

/-- The character `x ↦ t ^ ⟨x, coroot i⟩` of `X`: the coroot of `i` evaluated at `t`. -/
def corootChar (i : J) (t : Kˣ) : Multiplicative X →* Kˣ where
  toFun x := t ^ P.toLinearMap x.toAdd (P.coroot i)
  map_one' := by simp
  map_mul' x y := by simp [zpow_add]

/-- The Weyl element `n_i = φ_i([[0, 1], [-1, 0]])` of a simple root `i`. -/
def wn (i : b.support) : GL (Fin D.n) K :=
  D.φ i K sl2Weyl

theorem φ_sl2Upper (i : b.support) (s : K) : D.φ i K (sl2Upper s) = D.x i s :=
  Units.ext (D.φ_upper i K s)

theorem φ_sl2Lower (i : b.support) (s : K) :
    D.φ i K (sl2Lower s) = D.x (P.reflectionPerm i i) s :=
  Units.ext (D.φ_lower i K s)

theorem φ_sl2Diag (i : b.support) (t : Kˣ) :
    D.φ i K (sl2Diag t) = D.torusHom (corootChar (P := P) (i : J) t) := by
  apply Units.ext
  rw [D.φ_diag i K t, coe_torusHom]
  rfl

theorem wn_eq (i : b.support) :
    D.wn i = D.x i 1 * D.x (P.reflectionPerm i i) (-1) * D.x i (1 : K) := by
  rw [wn, sl2Weyl_eq, map_mul, map_mul, φ_sl2Upper, φ_sl2Lower]

theorem wn_mul_torus_coroot (i : b.support) (t : Kˣ) :
    D.wn i * D.torusHom (corootChar (P := P) (i : J) t) =
      D.torusHom (corootChar (P := P) (i : J) t⁻¹) * D.wn i := by
  rw [wn, ← φ_sl2Diag, ← φ_sl2Diag, ← map_mul, ← map_mul, sl2Weyl_mul_diag]

theorem wn_weight (i : b.support) {c d : Fin D.n}
    (h : ((D.wn i : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) c d ≠ 0) :
    D.wt c = P.reflection i (D.wt d) :=
  D.weyl_weight i K c d h

/-- The character `χ ∘ s_i` of the reflected torus point. -/
def reflectChar (i : J) (χ : Multiplicative X →* Kˣ) : Multiplicative X →* Kˣ :=
  χ.comp (AddMonoidHom.toMultiplicative (P.reflection i).toLinearMap.toAddMonoidHom)

theorem wn_mul_torusHom (i : b.support) (χ : Multiplicative X →* Kˣ) :
    D.wn i * D.torusHom χ =
      D.torusHom (reflectChar (P := P) (i : J) χ) * D.wn i := by
  apply Units.ext
  ext c d
  simp only [Units.val_mul, coe_torusHom, mul_diagonal, diagonal_mul]
  by_cases h : ((D.wn i : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) c d = 0
  · simp [h]
  · have hw := D.wn_weight i h
    have hχ : reflectChar (P := P) (i : J) χ (Multiplicative.ofAdd (D.wt c)) =
        χ (Multiplicative.ofAdd (D.wt d)) := by
      change χ (Multiplicative.ofAdd (P.reflection i (D.wt c))) = _
      rw [hw, RootPairing.reflection_same]
    rw [hχ, mul_comm]

theorem wn_mul_self (i : b.support) :
    D.wn i * D.wn i =
      (D.torusHom (corootChar (P := P) (i : J) (-1)) : GL (Fin D.n) K) := by
  rw [wn, ← map_mul, sl2Weyl_mul_self, φ_sl2Diag]

theorem x_reflectionPerm_self (i : b.support) (u : Kˣ) :
    D.x (P.reflectionPerm i i) (u : K) =
      D.x i ((u⁻¹ : Kˣ) : K) * D.torusHom (corootChar (P := P) (i : J) (-u⁻¹)) *
        D.wn i * D.x i ((u⁻¹ : Kˣ) : K) := by
  rw [← φ_sl2Lower, sl2Lower_eq, map_mul, map_mul, map_mul, φ_sl2Upper, φ_sl2Diag]
  rfl

theorem wn_conj_x (i : b.support) (j : J) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ s : K,
    D.wn i * D.x j s * (D.wn i)⁻¹ = D.x (P.reflectionPerm i j) ((ε : K) * s) := by
  obtain ⟨ε, hε, h⟩ := D.weyl_conj i j
  exact ⟨ε, hε, fun s => Units.ext (h K s)⟩

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
