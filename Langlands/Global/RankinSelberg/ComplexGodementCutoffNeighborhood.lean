import Langlands.Global.RankinSelberg.ComplexGodementUnitaryCutoff
import Mathlib.Topology.Maps.Proper.Basic

/-! # Invariant rectangular neighborhoods for Godement tests -/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "H" => Langlands.GeneralLinear n ℂ
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "Square" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ

private theorem trailingRows_mul (A B : Square) : trailingRows (A * B) = trailingRows A * B :=
  (Matrix.submatrix_mul A B Fin.succ id id Function.bijective_id).symm

private theorem rectRight_mul_inv (X : Rect) (k : K) : (X * k.val.val) * k.val⁻¹.val = X := by
  rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private def compactRectShear : Rect × K ≃ₜ Rect × K where
  toFun p := (p.1 * p.2.val.val, p.2)
  invFun p := (p.1 * p.2.val⁻¹.val, p.2)
  left_inv p := Prod.ext (rectRight_mul_inv p.1 p.2) rfl
  right_inv p := Prod.ext (rectRight_mul_inv p.1 p.2⁻¹) rfl
  continuous_toFun := (continuous_fst.matrix_mul
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd))).prodMk continuous_snd
  continuous_invFun := (continuous_fst.matrix_mul
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd).inv)).prodMk continuous_snd

private theorem isClosedMap_rectRight : IsClosedMap (fun p : Rect × K => p.1 * p.2.val.val) :=
  isClosedMap_fst_of_compactSpace.comp compactRectShear.isClosedMap

private theorem trailingMinor_unitary (k : K) (hzero : ∀ i, trailingRows k.val.val i 0 = 0) :
    (trailingRows k.val.val).submatrix id Fin.succ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let X := trailingRows k.val.val
  have hgram : X * Xᴴ = 1 := by
    have hk : k.val.val * k.val.valᴴ = 1 := Unitary.mul_star_self_of_mem k.2
    calc
      X * Xᴴ = (k.val.val * k.val.valᴴ).submatrix Fin.succ Fin.succ := by
        dsimp only [X, trailingRows]
        rw [conjTranspose_submatrix]
        exact (Matrix.submatrix_mul k.val.val k.val.valᴴ Fin.succ id Fin.succ Function.bijective_id).symm
      _ = 1 := by rw [hk, Matrix.submatrix_one _ (Fin.succ_injective n)]
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  ext i j
  have heq := congrArg (fun Y : Matrix (Fin n) (Fin n) ℂ => Y i j) hgram
  simpa only [X, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
    Fin.sum_univ_succ, hzero, zero_mul, zero_add] using heq

private theorem trailingIdentity_firstColumn (h : H) (i : Fin n) :
    (h.val * trailingRows (1 : Square)) i 0 = 0 := by
  simp [trailingRows, Matrix.mul_apply, Fin.succ_ne_zero]

private theorem trailingIdentity_minor (h : H) :
    (h.val * trailingRows (1 : Square)).submatrix id Fin.succ = h.val := by
  ext i j
  simp [trailingRows, Matrix.mul_apply, Matrix.one_apply, mul_ite]

/-- An open neighborhood of the smaller unitary group pulls back from an invariant
rectangular neighborhood in the sense needed to restrict a Godement cutoff. -/
def ComplexGodementCutoffNeighborhoodStatement : Prop :=
  ∀ V : Set H, IsOpen V → (unitaryCompact ℂ n : Set H) ⊆ V →
    ∃ U : Set Rect, IsOpen U ∧ unitaryTrailingRows n ⊆ U ∧
      (∀ X ∈ U, ∀ k : K, X * k.val.val ∈ U) ∧
      ∀ h : H, h.val * trailingRows (1 : Square) ∈ U → h ∈ V

theorem complexGodementCutoffNeighborhood : ComplexGodementCutoffNeighborhoodStatement (n := n) := by
  intro V hV hsub
  let W : Set (Matrix (Fin n) (Fin n) ℂ) := Units.val '' V
  have hW : IsOpen W := Units.isOpenEmbedding_val.isOpenMap _ hV
  let bad : Set Rect := {X | ∀ i, X i 0 = 0} ∩ (fun X : Rect => X.submatrix id Fin.succ) ⁻¹' Wᶜ
  have hbad : IsClosed bad := by
    have hz : {X : Rect | ∀ i, X i 0 = 0} = ⋂ i : Fin n, {X : Rect | X i 0 = 0} := by
      ext X
      simp
    dsimp only [bad]
    rw [hz]
    exact (isClosed_iInter fun i => isClosed_eq (continuous_id.matrix_elem i 0) continuous_const).inter
      (hW.isClosed_compl.preimage (continuous_id.matrix_submatrix _ _))
  let S := (fun p : Rect × K => p.1 * p.2.val.val) '' (bad ×ˢ (univ : Set K))
  refine ⟨Sᶜ, (isClosedMap_rectRight _ (hbad.prod isClosed_univ)).isOpen_compl, ?_, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩ ⟨⟨X, l⟩, ⟨hX, _⟩, heq⟩
    let u : K := k * l⁻¹
    have hXu : X = trailingRows u.val.val := by
      change X * l.val.val = trailingRows k.val.val at heq
      change X = trailingRows (k.val * l.val⁻¹).val
      rw [Units.val_mul, trailingRows_mul, ← heq, rectRight_mul_inv]
    have hXu₀ : ∀ i, trailingRows u.val.val i 0 = 0 := hXu ▸ hX.1
    let v := Unitary.toUnits (⟨(trailingRows u.val.val).submatrix id Fin.succ, trailingMinor_unitary u hXu₀⟩ :
      Matrix.unitaryGroup (Fin n) ℂ)
    have hv : v ∈ unitaryCompact ℂ n := trailingMinor_unitary u hXu₀
    have hmem : X.submatrix id Fin.succ ∈ W := ⟨v, hsub hv, congrArg (fun Y : Rect => Y.submatrix id Fin.succ) hXu.symm⟩
    exact hX.2 hmem
  · intro X hX k hSat
    obtain ⟨⟨Y, l⟩, ⟨hY, _⟩, heq⟩ := hSat
    apply hX
    refine ⟨(Y, l * k⁻¹), ⟨hY, mem_univ _⟩, ?_⟩
    change Y * (l.val * k.val⁻¹).val = X
    change Y * l.val.val = X * k.val.val at heq
    rw [Units.val_mul, ← Matrix.mul_assoc, heq, rectRight_mul_inv]
  · intro h hh
    by_contra hv
    apply hh
    refine ⟨(h.val * trailingRows (1 : Square), 1), ⟨⟨trailingIdentity_firstColumn h, ?_⟩, mem_univ _⟩, ?_⟩
    · change (h.val * trailingRows (1 : Square)).submatrix id Fin.succ ∉ W
      rw [trailingIdentity_minor]
      rintro ⟨u, hu, heq⟩
      exact hv ((Units.ext heq : u = h) ▸ hu)
    · simp

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
