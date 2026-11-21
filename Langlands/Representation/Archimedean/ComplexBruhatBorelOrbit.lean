import Langlands.Representation.Archimedean.LongestBruhatCell
import Langlands.Representation.GodementJacquet.ComplexTriangularHaar

/-! # Unipotent and Borel coordinates on the longest complex Bruhat cell -/

noncomputable section

open Set TopologicalSpace
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GodementJacquet (complexTriangularCoordinates complexTriangularCoordinates_apply)

variable (r : ℕ)

local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "U" => upperUnipotent (r + 1) ℂ
local notation "B" => upperTriangularSubgroup (r + 1) ℂ
local notation "D" => Fin (r + 1) → ℂˣ
local notation "P" => U × B
local notation "Cell" => longestBruhatCell ℂ r

/-- Left unipotent multiplication and inverse right Borel multiplication on matrices. -/
@[instance_reducible]
def matrixUnipotentBorelMulAction : MulAction P Mat where
  smul p x := p.1.val.val * x * (p.2⁻¹).val.val
  one_smul x := by
    change (1 : Mat) * x * 1 = x
    simp
  mul_smul p q x := by
    change (p.1 * q.1).val.val * x * ((p.2 * q.2)⁻¹).val.val =
      p.1.val.val * (q.1.val.val * x * (q.2⁻¹).val.val) * (p.2⁻¹).val.val
    simp only [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, mul_assoc]

attribute [local instance] matrixUnipotentBorelMulAction

theorem matrixUnipotentBorel_smul_def (p : P) (x : Mat) :
    p • x = p.1.val.val * x * (p.2⁻¹).val.val :=
  rfl

private def longestBorelReindex : P ≃ₜ ((U × U) × D) where
  toFun p :=
    let b := (complexTriangularCoordinates (r + 1)).symm p.2⁻¹
    ((p.1, b.2⁻¹), b.1)
  invFun q := (q.1.1, (complexTriangularCoordinates (r + 1) (q.2, q.1.2⁻¹))⁻¹)
  left_inv p := by
    simp only [inv_inv, Prod.eta, Homeomorph.apply_symm_apply]
  right_inv q := by
    simp only [inv_inv, Homeomorph.symm_apply_apply]
  continuous_toFun := by
    let c := (complexTriangularCoordinates (r + 1)).symm
    have hc : Continuous fun p : P => c p.2⁻¹ := c.continuous.comp continuous_snd.inv
    exact (continuous_fst.prodMk (continuous_snd.comp hc).inv).prodMk
      (continuous_fst.comp hc)
  continuous_invFun :=
    (continuous_fst.comp continuous_fst).prodMk
      ((complexTriangularCoordinates (r + 1)).continuous.comp
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst).inv)).inv

/-- The orbit map from the upper unipotent and upper Borel groups onto the longest cell. -/
def complexLongestBruhatBorelChart : P ≃ₜ (Cell : Set Mat) :=
  (longestBorelReindex r).trans (longestBruhatCellChart ℂ r)

/-- The coordinates act on the long Weyl representative by the specified left and right actions. -/
theorem complexLongestBruhatBorelChart_val (p : P) :
    (complexLongestBruhatBorelChart r p).val = p • (weylLong (r + 1) ℂ).val := by
  let c := complexTriangularCoordinates (r + 1)
  let b := c.symm p.2⁻¹
  change (longestBruhatCellChart ℂ r ((p.1, b.2⁻¹), b.1)).val = _
  rw [longestBruhatCellChart_val, matrixUnipotentPair_smul_def, matrixUnipotentBorel_smul_def,
    inv_inv]
  have hb : (c b).val = (p.2⁻¹).val :=
    congrArg Subtype.val (c.apply_symm_apply p.2⁻¹)
  rw [complexTriangularCoordinates_apply] at hb
  change p.1.val.val * ((weylLong (r + 1) ℂ).val * (Iwasawa.diagonalUnits b.1).val) *
      b.2.val.val = p.1.val.val * (weylLong (r + 1) ℂ).val * (p.2⁻¹).val.val
  rw [← hb, Units.val_mul]
  simp only [mul_assoc]
  rfl

theorem complexLongestBruhatBorelChart_val_mul (p q : P) :
    (complexLongestBruhatBorelChart r (p * q)).val =
      p • (complexLongestBruhatBorelChart r q).val := by
  rw [complexLongestBruhatBorelChart_val, complexLongestBruhatBorelChart_val, mul_smul]

theorem matrixUnipotentBorel_smul_mem_longestBruhatCell_iff (p : P) (x : Mat) :
    p • x ∈ Cell ↔ x ∈ Cell := by
  have h (q : P) {y : Mat} (hy : y ∈ Cell) : q • y ∈ Cell := by
    let e := complexLongestBruhatBorelChart r
    let a := e.symm ⟨y, hy⟩
    have ha : (e a).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    rw [← ha, ← complexLongestBruhatBorelChart_val_mul]
    exact (e (q * a)).property
  exact ⟨fun hx => by simpa using h p⁻¹ hx, h p⟩

/-- Between compact subsets of the open cell, the transporting parameters lie in a compact set. -/
theorem exists_compact_complexLongestBruhatBorel_transport {K L : Set Mat}
    (hK : IsCompact K) (hL : IsCompact L) (hKC : K ⊆ Cell) (hLC : L ⊆ Cell) :
    ∃ S : Set P, IsCompact S ∧ ∀ p x, x ∈ K → p • x ∈ L → p ∈ S := by
  let e := complexLongestBruhatBorelChart r
  have hpre {C : Set Mat} (hc : IsCompact C) (hC : C ⊆ Cell) :
      IsCompact (Subtype.val ⁻¹' C : Set (Cell : Set Mat)) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc (by simpa using hC)
  let S := (fun z : P × P => z.2 * z.1⁻¹) ''
    ((e.symm '' (Subtype.val ⁻¹' K)) ×ˢ (e.symm '' (Subtype.val ⁻¹' L)))
  refine ⟨S, (((hpre hK hKC).image e.symm.continuous).prod
    ((hpre hL hLC).image e.symm.continuous)).image (continuous_snd.mul continuous_fst.inv), ?_⟩
  intro p x hx hy
  let x' : (Cell : Set Mat) := ⟨x, hKC hx⟩
  let y' : (Cell : Set Mat) := ⟨p • x, hLC hy⟩
  let a := e.symm x'
  let b := e.symm y'
  have ha : (e a).val = x := congrArg Subtype.val (e.apply_symm_apply x')
  have hb : (e b).val = p • x := congrArg Subtype.val (e.apply_symm_apply y')
  have h : p * a = b := e.injective (Subtype.ext (by
    change (complexLongestBruhatBorelChart r (p * a)).val = (e b).val
    rw [complexLongestBruhatBorelChart_val_mul, ha, hb]))
  refine ⟨(a, b), ⟨⟨x', hx, rfl⟩, ⟨y', hy, rfl⟩⟩, ?_⟩
  change b * a⁻¹ = p
  rw [← h, mul_inv_cancel_right]

end Langlands.Archimedean
