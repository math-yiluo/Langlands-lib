import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Mathlib.Tactic.Group

/-! # Recovering a lower unitriangular matrix from its compact factor -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexPrincipalSeriesExtension

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexGramFormula

variable {n : ℕ}

local notation "U" => Matrix.unitaryGroup (Fin n) ℂ
local notation "w₀" => weylLong n ℂ
local notation "B" => upperTriangularSubgroup n ℂ
local notation "C" => upperBruhatCell n ℂ Fin.revPerm

/-- The unitary matrices whose right translate by the long Weyl representative
lies in the corresponding Bruhat cell. -/
def longCellUnitary (n : ℕ) : Set (Matrix.unitaryGroup (Fin n) ℂ) :=
  {k | (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) * weylLong n ℂ ∈
    upperBruhatCell n ℂ Fin.revPerm}

private def toLongCell (k : longCellUnitary n) : UpperBruhatCell n ℂ Fin.revPerm :=
  ⟨(Unitary.toUnits k.val : Langlands.GeneralLinear n ℂ) * w₀, k.2⟩

/-- The lower unitriangular coordinate of a unitary matrix in the long cell
chart. -/
def lowerUnitaryCoordinate (k : longCellUnitary n) : Langlands.GeneralLinear n ℂ :=
  let v := ((UpperBruhatCoordinates.cellHomeomorph (K := ℂ) Fin.revPerm).symm (toLongCell k)).2
  w₀ * v.val * w₀⁻¹

theorem continuous_lowerUnitaryCoordinate : Continuous (lowerUnitaryCoordinate (n := n)) := by
  have hcell : Continuous (toLongCell (n := n)) :=
    ((continuous_unitary_toUnits.comp continuous_subtype_val).mul continuous_const).subtype_mk _
  have hcoord := (UpperBruhatCoordinates.cellHomeomorph (K := ℂ)
    (Fin.revPerm : Equiv.Perm (Fin n))).symm.continuous.comp hcell
  exact (continuous_const.mul (continuous_subtype_val.comp (continuous_snd.comp hcoord))).mul
    continuous_const

private theorem lowerUnitaryCoordinate_of_decomposition (k : U) (b : B)
    (v : permutationUnipotentMinus n ℂ Fin.revPerm)
    (h : (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) * w₀ = b.val * w₀ * v.val) :
    ∃ hk : k ∈ longCellUnitary n, lowerUnitaryCoordinate ⟨k, hk⟩ = w₀ * v.val * w₀⁻¹ := by
  have hk : k ∈ longCellUnitary n := by
    change (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) * w₀ ∈ C
    rw [h]
    exact (upperBruhatCellMap n ℂ Fin.revPerm (b, v)).2
  have heq : toLongCell ⟨k, hk⟩ =
      UpperBruhatCoordinates.cellHomeomorph (K := ℂ) (Fin.revPerm : Equiv.Perm (Fin n)) (b, v) :=
    Subtype.ext h
  refine ⟨hk, ?_⟩
  rw [lowerUnitaryCoordinate, heq, Homeomorph.symm_apply_apply]

theorem lowerUnitaryCoordinate_of_upperTriangular (k : U)
    (hk : (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) ∈ B) :
    ∃ h : k ∈ longCellUnitary n, lowerUnitaryCoordinate ⟨k, h⟩ = 1 := by
  obtain ⟨h, hcoord⟩ :=
    lowerUnitaryCoordinate_of_decomposition k ⟨Unitary.toUnits k, hk⟩ 1 (by simp)
  exact ⟨h, by rw [hcoord]; simp⟩

/-- For a lower unitriangular matrix, the compact factor lies in the long cell
chart and recovers exactly the original matrix. -/
theorem lowerUnitaryCoordinate_phaseOrthPart (g : lowerUnipotent n ℂ) :
    ∃ hk : phaseOrthPart g.val ∈ longCellUnitary n,
      lowerUnitaryCoordinate ⟨phaseOrthPart g.val, hk⟩ = g.val := by
  obtain ⟨a, u, k, hk, hg⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g.val
  let a' : Fin n → ℂˣ := fun i => phaseUnit (a i)
  have hphase : (Unitary.toUnits (phaseOrthPart g.val) : Langlands.GeneralLinear n ℂ) =
      Iwasawa.diagonalUnits a' * k := by
    rw [hg, phaseOrthPart_iwasawa a u hk]
    apply Units.ext
    change (phaseMatrix a : Matrix (Fin n) (Fin n) ℂ) * k.val =
      (Iwasawa.diagonalUnits a' * k).val
    rw [phaseMatrix_val, Units.val_mul, Iwasawa.diagonalUnits_val]
  let b := Iwasawa.diagonalUnits a * u.val * (Iwasawa.diagonalUnits a')⁻¹
  have hb : b ∈ B :=
    mul_mem (mul_mem (diagonalUnits_mem_upperTriangular n a)
      (upperUnipotent_le_upperTriangular n ℂ u.2))
      (inv_mem (diagonalUnits_mem_upperTriangular n a'))
  have hbg : b * (Unitary.toUnits (phaseOrthPart g.val) : Langlands.GeneralLinear n ℂ) = g.val := by
    rw [hphase, hg]
    dsimp only [b]
    group
  let v := w₀⁻¹ * g.val * w₀
  have hvupper : v ∈ upperUnipotent n ℂ := by
    have hu' := g.2
    change w₀ * g.val * w₀⁻¹ ∈ upperUnipotent n ℂ at hu'
    simpa only [v, weylLong_inv] using hu'
  have hrecover : w₀ * v * w₀⁻¹ = g.val := by
    dsimp only [v]
    group
  have hv : v ∈ permutationUnipotentMinus n ℂ Fin.revPerm := by
    refine (mem_permutationUnipotentMinus_iff n ℂ Fin.revPerm v).mpr ⟨hvupper, ?_⟩
    change w₀ * v * w₀⁻¹ ∈ lowerUnipotent n ℂ
    rw [hrecover]
    exact g.2
  have hbruhat : (Unitary.toUnits (phaseOrthPart g.val) : Langlands.GeneralLinear n ℂ) * w₀ =
      b⁻¹ * w₀ * v := by
    dsimp only [v]
    conv_rhs => rw [← hbg]
    group
  obtain ⟨h, hcoord⟩ :=
    lowerUnitaryCoordinate_of_decomposition (phaseOrthPart g.val) ⟨b⁻¹, inv_mem hb⟩
      ⟨v, hv⟩ hbruhat
  exact ⟨h, hcoord.trans hrecover⟩

/-- A continuous function on the unitary group whose value one is confined to
the upper triangular subgroup is uniformly below one on the compact factors
of lower unitriangular matrices outside any open neighborhood of the identity. -/
theorem exists_bound_of_lowerUnitaryCoordinate (q : U → ℝ) (hq : Continuous q)
    (hq₁ : ∀ k, q k ≤ 1)
    (hqTri : ∀ k, q k = 1 → (Unitary.toUnits k : Langlands.GeneralLinear n ℂ) ∈ B)
    {S : Set (Langlands.GeneralLinear n ℂ)} (hS : IsOpen S) (h₁ : 1 ∈ S) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ g : lowerUnipotent n ℂ, g.val ∉ S → q (phaseOrthPart g.val) ≤ c := by
  let V : Set (longCellUnitary n) := lowerUnitaryCoordinate ⁻¹' S
  have hV : IsOpen V := hS.preimage continuous_lowerUnitaryCoordinate
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  have hOne (k : U) (hk : q k = 1) : k ∈ W := by
    obtain ⟨hkC, hcoord⟩ := lowerUnitaryCoordinate_of_upperTriangular k (hqTri k hk)
    have h : (⟨k, hkC⟩ : longCellUnitary n) ∈ V := by
      change lowerUnitaryCoordinate ⟨k, hkC⟩ ∈ S
      rw [hcoord]
      exact h₁
    rw [← hWV] at h
    exact h
  have hOutside (g : lowerUnipotent n ℂ) (hg : g.val ∉ S) : phaseOrthPart g.val ∈ Wᶜ := by
    intro hk
    obtain ⟨hkC, hcoord⟩ := lowerUnitaryCoordinate_phaseOrthPart g
    have h : (⟨phaseOrthPart g.val, hkC⟩ : longCellUnitary n) ∈ V := by
      rw [← hWV]
      exact hk
    change lowerUnitaryCoordinate ⟨phaseOrthPart g.val, hkC⟩ ∈ S at h
    rw [hcoord] at h
    exact hg h
  by_cases hne : (Wᶜ).Nonempty
  · have : CompactSpace U := isCompact_iff_compactSpace.mp
      (Langlands.Global.isCompact_unitaryMatrix ℂ n)
    obtain ⟨k, hk, hmax⟩ := hW.isClosed_compl.isCompact.exists_isMaxOn hne hq.continuousOn
    have hqk : q k < 1 := lt_of_le_of_ne (hq₁ k) (fun he => hk (hOne k he))
    exact ⟨max (q k) 0, le_max_right _ _, max_lt hqk zero_lt_one, fun g hg =>
      (hmax (hOutside g hg)).trans (le_max_left _ _)⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun g hg => False.elim (hne ⟨_, hOutside g hg⟩)⟩

end Langlands.Archimedean.ComplexPrincipalSeriesExtension
