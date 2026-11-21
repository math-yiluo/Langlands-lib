import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Langlands.Representation.Whittaker.Distribution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The longest Bruhat cell in the real matrix space -/

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.Whittaker

universe uF

variable (F : Type uF) [RCLike F] (n : ℕ)

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) F
local notation "GL" => Langlands.GeneralLinear (n + 1) F
local notation "U" => upperUnipotent (n + 1) F
local notation "T" => Fin (n + 1) → Fˣ

private theorem inversionCount_le_revPerm (w : Equiv.Perm (Fin (n + 1))) :
    permutationInversionCount (n + 1) w ≤ permutationInversionCount (n + 1) Fin.revPerm := by
  classical
  rw [permutationInversionCount_eq_card, permutationInversionCount_eq_card]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, Fin.rev_lt_rev.mpr hp.1⟩

private theorem isOpen_revCell : IsOpen (upperBruhatCell (n + 1) F Fin.revPerm) := by
  have h : upperBruhatHigherCells (n + 1) F Fin.revPerm = ∅ := by
    ext g
    simp only [mem_upperBruhatHigherCells_iff, mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, _⟩
    exact (not_lt_of_ge (inversionCount_le_revPerm n w)) hw
  simpa only [upperBruhatCellNeighborhood, h, union_empty] using
    (isOpen_upperBruhatCellNeighborhood (K := F) (n := n + 1) Fin.revPerm)

/-- The largest Bruhat cell, viewed as an open subset of the ambient matrix space. -/
def longestBruhatCell : Opens Mat :=
  ⟨(Units.val : GL → Mat) '' upperBruhatCell (n + 1) F Fin.revPerm,
    Units.isOpenEmbedding_val.isOpenMap _ (isOpen_revCell F n)⟩

theorem isUnit_of_mem_longestBruhatCell {x : Mat} (hx : x ∈ longestBruhatCell F n) :
    IsUnit x := by
  obtain ⟨g, -, rfl⟩ := hx
  exact g.isUnit

/-- Left and inverse right multiplication, as an actual action of the product group. -/
@[instance_reducible]
def matrixUnipotentPairMulAction : MulAction (U × U) Mat where
  smul p x := p.1.val.val * x * (p.2⁻¹).val.val
  one_smul x := by
    change (1 : Mat) * x * 1 = x
    simp
  mul_smul p q x := by
    change (p.1 * q.1).val.val * x * ((p.2 * q.2)⁻¹).val.val =
      p.1.val.val * (q.1.val.val * x * (q.2⁻¹).val.val) * (p.2⁻¹).val.val
    simp only [mul_inv_rev, Subgroup.coe_mul, Units.val_mul, mul_assoc]

attribute [local instance] matrixUnipotentPairMulAction

lemma matrixUnipotentPair_smul_def (p : U × U) (x : Mat) :
    p • x = p.1.val.val * x * (p.2⁻¹).val.val := rfl

lemma continuous_matrixUnipotentPair_smul :
    Continuous (fun a : (U × U) × Mat => a.1 • a.2) := by
  have hv : Continuous (fun u : U => u.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  exact ((hv.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
    (hv.comp (continuous_snd.comp continuous_fst).inv)

private lemma revMinus_eq_upper :
    permutationUnipotentMinus (n + 1) F Fin.revPerm = upperUnipotent (n + 1) F := by
  ext g
  rw [mem_permutationUnipotentMinus_iff_entries]
  exact ⟨And.left, fun h => ⟨h, fun i j hij => h.1 (Fin.rev_lt_rev.mp hij)⟩⟩

private lemma exists_longestBruhatCellChart :
    ∃ e : ((U × U) × T) ≃ₜ (longestBruhatCell F n : Set Mat),
      ∀ p d, (e (p, d)).val = p • (weylLong (n + 1) F * Iwasawa.diagonalUnits d).val := by
  obtain ⟨-, eT, heT⟩ := upperBruhatCoordinates F (n + 1) Fin.revPerm
  revert eT
  rw [revMinus_eq_upper F n]
  intro eT heT
  let r : ((U × U) × T) ≃ₜ (U × T × U) := {
    toFun q := (q.1.1, q.2, q.1.2⁻¹)
    invFun q := ((q.1, q.2.2⁻¹), q.2.1)
    left_inv := fun q => by simp
    right_inv := fun q => by simp
    continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst).inv)
    continuous_invFun := (continuous_fst.prodMk (continuous_snd.comp continuous_snd).inv).prodMk
      (continuous_fst.comp continuous_snd) }
  let c := Units.isOpenEmbedding_val.isEmbedding.homeomorphImage
    (upperBruhatCell (n + 1) F Fin.revPerm)
  refine ⟨r.trans (eT.trans c), fun p d => ?_⟩
  change (eT (p.1, d, p.2⁻¹)).val.val = _
  rw [heT]
  simp only [matrixUnipotentPair_smul_def, weylLong, Units.val_mul, mul_assoc]

/-- Coordinates `((u, v), d) ↦ u (w₀ d) v⁻¹` on the longest cell, using the actual
upper unipotent subgroup on both sides. -/
def longestBruhatCellChart : ((U × U) × T) ≃ₜ (longestBruhatCell F n : Set Mat) :=
  (exists_longestBruhatCellChart F n).choose

lemma longestBruhatCellChart_val (p : U × U) (d : T) :
    (longestBruhatCellChart F n (p, d)).val = p • (weylLong (n + 1) F * Iwasawa.diagonalUnits d).val :=
  (exists_longestBruhatCellChart F n).choose_spec p d

lemma matrixUnipotentPair_smul_mem_longestBruhatCell_iff (p : U × U) (x : Mat) :
    p • x ∈ longestBruhatCell F n ↔ x ∈ longestBruhatCell F n := by
  have h (q : U × U) {y : Mat} (hy : y ∈ longestBruhatCell F n) :
      q • y ∈ longestBruhatCell F n := by
    let z := (longestBruhatCellChart F n).symm ⟨y, hy⟩
    have hz : z.1 • (weylLong (n + 1) F * Iwasawa.diagonalUnits z.2).val = y := by
      rw [← longestBruhatCellChart_val]
      exact congrArg Subtype.val ((longestBruhatCellChart F n).apply_symm_apply ⟨y, hy⟩)
    rw [← hz, ← mul_smul, ← longestBruhatCellChart_val]
    exact (longestBruhatCellChart F n (q * z.1, z.2)).property
  exact ⟨fun hx => by simpa using h p⁻¹ hx, h p⟩

/-- Only a compact set of parameters can send any point of `K` into `L` if
both compact sets lie in the longest cell. -/
theorem exists_compact_longestBruhatCell_transport {K L : Set Mat}
    (hK : IsCompact K) (hL : IsCompact L) (hKB : K ⊆ longestBruhatCell F n)
    (hLB : L ⊆ longestBruhatCell F n) :
    ∃ S : Set (U × U), IsCompact S ∧ ∀ p x, x ∈ K → p • x ∈ L → p ∈ S := by
  let B : Set Mat := longestBruhatCell F n
  let e := longestBruhatCellChart F n
  let f : B → (U × U) := Prod.fst ∘ e.symm
  have hf : Continuous f := continuous_fst.comp e.symm.continuous
  have hpre {C : Set Mat} (hc : IsCompact C) (hcb : C ⊆ B) :
      IsCompact (Subtype.val ⁻¹' C : Set B) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc (by simpa using hcb)
  let S := (fun z : (U × U) × (U × U) => z.2 * z.1⁻¹) ''
    ((f '' (Subtype.val ⁻¹' K : Set B)) ×ˢ (f '' (Subtype.val ⁻¹' L : Set B)))
  refine ⟨S, (((hpre hK hKB).image hf).prod ((hpre hL hLB).image hf)).image
    (continuous_snd.mul continuous_fst.inv), ?_⟩
  intro p x hx hy
  let x' : B := ⟨x, hKB hx⟩
  let y' : B := ⟨p • x, hLB hy⟩
  let a := e.symm x'
  let b := e.symm y'
  have ha : a.1 • (weylLong (n + 1) F * Iwasawa.diagonalUnits a.2).val = x := by
    rw [← longestBruhatCellChart_val]
    exact congrArg Subtype.val (e.apply_symm_apply x')
  have h : e (p * a.1, a.2) = e b := by
    apply Subtype.ext
    change (longestBruhatCellChart F n (p * a.1, a.2)).val = (e b).val
    rw [longestBruhatCellChart_val, mul_smul, ha, e.apply_symm_apply y']
  have hp : b.1 * a.1⁻¹ = p := by
    rw [← congrArg Prod.fst (e.injective h), mul_inv_cancel_right]
  exact ⟨(a.1, b.1), ⟨⟨x', hx, rfl⟩, ⟨y', hy, rfl⟩⟩, hp⟩

/-- Weyl-conjugated transpose on all matrices, as a real linear equivalence. -/
def matrixWeylTranspose : Mat ≃L[ℝ] Mat :=
  ((Matrix.transposeLinearEquiv (Fin (n + 1)) (Fin (n + 1)) ℝ F).trans
    (Matrix.reindexLinearEquiv ℝ F Fin.revPerm Fin.revPerm)).toContinuousLinearEquiv

@[simp] lemma matrixWeylTranspose_entry (x : Mat) (i j : Fin (n + 1)) :
    matrixWeylTranspose F n x i j = x j.rev i.rev := rfl

lemma matrixWeylTranspose_involutive : Function.Involutive (matrixWeylTranspose F n) := by
  intro x
  ext i j
  simp only [matrixWeylTranspose_entry, Fin.rev_rev]

lemma matrixWeylTranspose_mul (x y : Mat) :
    matrixWeylTranspose F n (x * y) = matrixWeylTranspose F n y * matrixWeylTranspose F n x := by
  ext i j
  simp only [matrixWeylTranspose_entry, Matrix.mul_apply]
  rw [← Equiv.sum_comp Fin.revPerm (fun k => x j.rev k * y k i.rev)]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

@[simp] lemma matrixWeylTranspose_val (g : GL) :
    matrixWeylTranspose F n g.val = (weylTransposeHomeomorph n F g).val := by
  ext i j
  simp only [matrixWeylTranspose_entry, weylTransposeHomeomorph_entry]

private lemma transposeUnipotent_mul (u v : U) :
    weylTransposeUnipotent n F (u * v) =
      weylTransposeUnipotent n F v * weylTransposeUnipotent n F u :=
  Subtype.ext (weylTransposeHomeomorph_mul n F u.val v.val)

lemma matrixWeylTranspose_unipotent_inv (u : U) :
    weylTransposeUnipotent n F u⁻¹ = (weylTransposeUnipotent n F u)⁻¹ := by
  have h1 : weylTransposeUnipotent n F (1 : U) = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp only [weylTransposeUnipotent_val, weylTransposeHomeomorph_entry]
    change (1 : Mat) j.rev i.rev = (1 : Mat) i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  apply eq_inv_of_mul_eq_one_left
  rw [← transposeUnipotent_mul, mul_inv_cancel, h1]

/-- Transpose lifts to an automorphism of the parameters of the action, swapping the
factors and applying inverse Weyl-conjugated transpose on each. -/
def matrixUnipotentPairTranspose : (U × U) ≃ₜ (U × U) :=
  let s := (Homeomorph.inv U).trans (weylTransposeUnipotent n F)
  (Homeomorph.prodComm U U).trans (s.prodCongr s)

lemma matrixUnipotentPairTranspose_apply (p : U × U) :
    matrixUnipotentPairTranspose F n p =
      (weylTransposeUnipotent n F p.2⁻¹, weylTransposeUnipotent n F p.1⁻¹) := rfl

lemma matrixUnipotentPairTranspose_mul (p q : U × U) :
    matrixUnipotentPairTranspose F n (p * q) =
      matrixUnipotentPairTranspose F n p * matrixUnipotentPairTranspose F n q := by
  simp only [matrixUnipotentPairTranspose_apply, Prod.fst_mul, Prod.snd_mul, mul_inv_rev,
    transposeUnipotent_mul, Prod.mk_mul_mk]

lemma matrixUnipotentPairTranspose_involutive :
    Function.Involutive (matrixUnipotentPairTranspose F n) := by
  intro p
  simp only [matrixUnipotentPairTranspose_apply, matrixWeylTranspose_unipotent_inv,
    inv_inv, weylTransposeUnipotent_involutive, Prod.mk.eta]

lemma matrixWeylTranspose_smul (p : U × U) (x : Mat) :
    matrixWeylTranspose F n (p • x) =
      matrixUnipotentPairTranspose F n p • matrixWeylTranspose F n x := by
  simp only [matrixUnipotentPair_smul_def, matrixUnipotentPairTranspose_apply,
    matrixWeylTranspose_mul, matrixWeylTranspose_val, weylTransposeUnipotent_val,
    matrixWeylTranspose_unipotent_inv, inv_inv, mul_assoc]
  rw [← matrixWeylTranspose_unipotent_inv]
  rfl

private lemma matrixWeylTranspose_weylLong_diagonal (d : T) :
    matrixWeylTranspose F n (weylLong (n + 1) F * Iwasawa.diagonalUnits d).val =
      (weylLong (n + 1) F * Iwasawa.diagonalUnits d).val := by
  ext i j
  simp only [matrixWeylTranspose_entry]
  rw [weylLong_mul_entry, weylLong_mul_entry, Fin.rev_rev]
  change Matrix.diagonal (fun k => (d k : F)) j i.rev = Matrix.diagonal (fun k => (d k : F)) i.rev j
  by_cases h : j = i.rev
  · simp [h]
  · simp [Matrix.diagonal_apply_ne, h, Ne.symm h]

/-- Every orbit in the longest cell contains an element fixed by Weyl-conjugated
transpose; more precisely it contains its diagonal-long-Weyl representative. -/
lemma exists_smul_fixed_of_mem_longestBruhatCell {x : Mat} (hx : x ∈ longestBruhatCell F n) :
    ∃ p : U × U, ∃ y : Mat, y ∈ longestBruhatCell F n ∧
      matrixWeylTranspose F n y = y ∧ x = p • y := by
  let e := longestBruhatCellChart F n
  let z := e.symm ⟨x, hx⟩
  let y := (weylLong (n + 1) F * Iwasawa.diagonalUnits z.2).val
  refine ⟨z.1, y, ?_, matrixWeylTranspose_weylLong_diagonal F n z.2, ?_⟩
  · rw [← one_smul (U × U) y, ← longestBruhatCellChart_val F n 1 z.2]
    exact (e (1, z.2)).property
  · rw [← longestBruhatCellChart_val F n z.1 z.2]
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)).symm

lemma matrixWeylTranspose_mem_longestBruhatCell_iff (x : Mat) :
    matrixWeylTranspose F n x ∈ longestBruhatCell F n ↔ x ∈ longestBruhatCell F n := by
  have h {z : Mat} (hz : z ∈ longestBruhatCell F n) :
      matrixWeylTranspose F n z ∈ longestBruhatCell F n := by
    obtain ⟨p, y, hy, hτ, rfl⟩ := exists_smul_fixed_of_mem_longestBruhatCell F n hz
    rw [matrixWeylTranspose_smul, hτ, matrixUnipotentPair_smul_mem_longestBruhatCell_iff]
    exact hy
  exact ⟨fun hx => by simpa only [matrixWeylTranspose_involutive F n x] using h hx, h⟩

end Langlands.Archimedean
