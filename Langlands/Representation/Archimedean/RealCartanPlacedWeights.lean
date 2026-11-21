import Langlands.Representation.Archimedean.RealCartanPlacedTrace
import Langlands.Representation.Archimedean.RealStandardEllipticCartanWindowNormalization

/-! # The original compact block weights on the fixed real Cartan flags -/

noncomputable section

open Matrix Set MeasureTheory
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanPlacedWeights

open Langlands.LocalFactor.Archimedean RealBlockFourierFinite RealBlockPropagation
  RealCartanBlockLayout RealCartanCompactSupport RealCartanFixedCosets RealCartanFixedFlag RealCartanLowTraceHaar
  RealCartanPlacedTrace RealCartanRadialWeight RealCartanTraceCoordinates RealLeviChart
  RealLeviCompactChart RealPrincipalSeriesDuality RealSmallOrthogonalFourier RealSmallOrthogonalHaar
  RealStandardEllipticCartan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

section Source

variable {r s : ℕ} (x : Coordinates r s)

/-- The source orthogonal block is the rotation on a plane and the sign on a line. -/
def sourceSmall (u : CartanSlot r s) : K (slotSize u) :=
  ⟨orthogonalBlock x u, by
    apply (mem_orthogonalGroup_iff _ _).mpr
    cases u with
    | inl i =>
      rw [orthogonalBlock_inl, ← rotation_val]
      exact (mem_orthogonalGroup_iff _ _).mp (rotation (x.1 i).toAdd.2).2
    | inr i =>
      rw [orthogonalBlock_inr, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
        one_mul, smul_smul, ← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      rw [(show Even ((x.2 i).toAdd.2 + (x.2 i).toAdd.2) from ⟨_, rfl⟩).neg_one_zpow, one_smul]⟩

@[simp]
theorem sourceSmall_inl (i : Fin r) : sourceSmall x (.inl i) = rotation (x.1 i).toAdd.2 := by
  apply Subtype.ext
  change orthogonalBlock x (.inl i) = (rotation (x.1 i).toAdd.2).val
  rw [orthogonalBlock_inl, rotation_val]

theorem sourceOrthogonal_entry {n : ℕ} (h : 2 * r + s = n) (u : CartanSlot r s)
    (i j : Fin (slotSize u)) :
    (sourceOrthogonal h x : M n) (cartanIndexEquiv h ⟨u, i⟩) (cartanIndexEquiv h ⟨u, j⟩) =
      (sourceSmall x u : M (slotSize u)) i j := by
  have he := cartanElement_apply_block h x u i j
  rw [sourceFactorization, diagonal_mul, Function.comp_apply, cartanLabel_apply_indexEquiv,
    sourceRadius, Equiv.symm_apply_apply] at he
  exact mul_left_cancel₀ (Real.exp_ne_zero _) he

end Source

section Matching

variable {r s t : ℕ} {sizes : Fin t → ℕ} (h : 2 * r + s = ∑ i, sizes i)
variable (e : Assignment sizes (cartanLabel h))

/-- The source line or plane matched to a target block. -/
def matchedSlot (i : Fin t) : CartanSlot r s := finSumFinEquiv.symm (e.val.symm i)

theorem matchedSlot_size (i : Fin t) : slotSize (matchedSlot h e i) = sizes i := by
  rw [← cartanFiber_card h (matchedSlot h e i), matchedSlot, Equiv.apply_symm_apply, e.2,
    Equiv.apply_symm_apply, card_cls_fiber]

private def matchedFiberEquiv (i : Fin t) :
    BlockFiber (cartanLabel h) (finSumFinEquiv (matchedSlot h e i)) ≃ BlockFiber (cls sizes) i :=
  (assignmentPerm sizes e).subtypeEquiv (fun p => by
    change cartanLabel h p = finSumFinEquiv (matchedSlot h e i) ↔
      cls sizes (assignmentPerm sizes e p) = i
    rw [matchedSlot, Equiv.apply_symm_apply, cls_assignmentPerm]
    exact e.val.eq_symm_apply)

/-- The actual coordinate permutation restricted to the matched source plane or line. -/
def matchedIndexEquiv (i : Fin t) : Fin (slotSize (matchedSlot h e i)) ≃ Fin (sizes i) :=
  (cartanFiberEquiv h (matchedSlot h e i)).trans
    ((matchedFiberEquiv h e i).trans (posFiberEquiv sizes i).symm)

theorem pos_matchedIndexEquiv (i : Fin t) (p : Fin (slotSize (matchedSlot h e i))) :
    pos sizes i (matchedIndexEquiv h e i p) =
      assignmentPerm sizes e (cartanIndexEquiv h ⟨matchedSlot h e i, p⟩) := by
  change ((posFiberEquiv sizes i) ((posFiberEquiv sizes i).symm
    ((matchedFiberEquiv h e i) ((cartanFiberEquiv h (matchedSlot h e i)) p)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

end Matching

section Frame

variable {r s t : ℕ} (b : Fin t → RealBlock)
variable (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
variable (e : Assignment (blockSizes b) (cartanLabel h))

/-- The placed orthogonal factor at a single target block. -/
def matchedSmall (i : Fin t) : K (blockSizes b i) :=
  compactEquiv (blockSizes b i) (matchedOrthogonal b h x e i)

theorem matchedSmall_val (i : Fin t) : (matchedSmall b h x e i : M (blockSizes b i)) =
    Matrix.reindex (matchedIndexEquiv h e i) (matchedIndexEquiv h e i)
      (sourceSmall x (matchedSlot h e i) : M (slotSize (matchedSlot h e i))) := by
  ext p q
  let sizes := blockSizes b
  let u := matchedSlot h e i
  let m := matchedIndexEquiv h e i
  let π := assignmentPerm sizes e
  have hp : π.symm (pos sizes i p) = cartanIndexEquiv h ⟨u, m.symm p⟩ := by
    apply π.injective
    rw [Equiv.apply_symm_apply, ← pos_matchedIndexEquiv h e i (m.symm p)]
    exact (congrArg (pos sizes i) (m.apply_symm_apply p)).symm
  have hq : π.symm (pos sizes i q) = cartanIndexEquiv h ⟨u, m.symm q⟩ := by
    apply π.injective
    rw [Equiv.apply_symm_apply, ← pos_matchedIndexEquiv h e i (m.symm q)]
    exact (congrArg (pos sizes i) (m.apply_symm_apply q)).symm
  let Q := matchedOrthogonal b h x e
  have he := congrArg (fun z : K (∑ i, sizes i) => (z : M (∑ i, sizes i)) (pos sizes i p) (pos sizes i q))
    (blockFrame_matchedOrthogonal b h x e)
  change blockDiagHom sizes (fun j => (Q j).val.val) (pos sizes i p) (pos sizes i q) =
    ((permutationFrame π : M (∑ i, sizes i)) * (sourceOrthogonal h x : M (∑ i, sizes i)) *
      ((permutationFrame π)⁻¹ : K (∑ i, sizes i)).val) (pos sizes i p) (pos sizes i q) at he
  rw [blockDiagHom_pos_pos_self, conjugate_permutationFrame_apply, hp, hq, sourceOrthogonal_entry] at he
  exact he

end Frame

section Density

variable {r s : ℕ} (x : Coordinates r s)

/-- The within-block compact density at a matched source slot. -/
def slotDensity : RealBlock → CartanSlot r s → ℂ
  | .character a, .inr j => (-1 : ℂ) ^ ((a.parity.val : ℤ) * (x.2 j).toAdd.2)
  | .induced a, .inl j => ∑ m ∈ window a.weight.natAbs, expMode m (x.1 j).toAdd.2
  | _, _ => 0

private theorem blockDensity_conj_inv_source (d : RealBlock) (u : CartanSlot r s)
    (m : Fin (slotSize u) ≃ Fin d.rank) (R κ : K d.rank)
    (hR : (R : M d.rank) = Matrix.reindex m m (sourceSmall x u : M (slotSize u))) :
    blockDensity d (κ * R⁻¹ * κ⁻¹) = slotDensity x d u := by
  cases d with
  | character a =>
    cases u with
    | inl j =>
      have h := Fintype.card_congr m
      simp [slotSize, RealBlock.rank] at h
    | inr j =>
      simp only [slotSize, Sum.elim_inr, RealBlock.rank] at m R κ hR ⊢
      let z : ℤ := (x.2 j).toAdd.2
      have he : m = Equiv.refl (Fin 1) := Equiv.ext fun _ => Subsingleton.elim _ _
      have hv : (R : M 1) = (-1 : ℝ) ^ z • (1 : M 1) := by
        rw [hR, he]
        exact orthogonalBlock_inr x j
      have hdet (k : K 1) (hk : Matrix.det (R : M 1) = (k : M 1).det) :
          ((κ * R⁻¹ * κ⁻¹ : K 1) : M 1).det = (k : M 1).det := by
        rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.det_mul, Matrix.det_mul,
          show ((R⁻¹ : K 1) : M 1) = (R : M 1)ᵀ from rfl,
          show ((κ⁻¹ : K 1) : M 1) = (κ : M 1)ᵀ from rfl,
          Matrix.det_transpose, Matrix.det_transpose, hk]
        rcases RealCartanAngularHaar.det_eq_one_or_neg_one κ with h | h <;> rw [h] <;> ring
      have hd : (R : M 1).det = (-1 : ℝ) ^ z := by rw [hv, Matrix.det_smul]; simp
      have hf : ((κ * R⁻¹ * κ⁻¹ : K 1) : M 1).det = (-1 : ℝ) ^ z := by
        rw [hdet R rfl, hd]
      change determinantWeight ((-1 : ℂ) ^ a.parity.val) (κ * R⁻¹ * κ⁻¹) =
        (-1 : ℂ) ^ ((a.parity.val : ℤ) * z)
      rcases Int.even_or_odd z with hz | hz
      · rw [hz.neg_one_zpow] at hf
        rw [determinantWeight_of_det_one _ hf, mul_comm, _root_.zpow_mul, hz.neg_one_zpow, _root_.one_zpow]
      · rw [hz.neg_one_zpow] at hf
        rw [determinantWeight_of_det_neg_one _ hf, mul_comm, _root_.zpow_mul, hz.neg_one_zpow, zpow_natCast]
  | induced a =>
    cases u with
    | inr j =>
      have h := Fintype.card_congr m
      simp [slotSize, RealBlock.rank] at h
    | inl j =>
      simp only [slotSize, Sum.elim_inl, RealBlock.rank] at m R κ hR ⊢
      let θ : ℝ := (x.1 j).toAdd.2
      let w : K 2 := permutationFrame m
      have hrot : R = w * rotation θ * w⁻¹ := by
        apply Subtype.ext
        ext p q
        rw [hR, sourceSmall_inl]
        change (rotation θ : M 2) (m.symm p) (m.symm q) =
          (((w : M 2) * (rotation θ : M 2)) * (w⁻¹ : K 2).val) p q
        rw [conjugate_permutationFrame_apply]
      change pairDensity a.weight.natAbs (κ * R⁻¹ * κ⁻¹) = _
      rw [hrot, show κ * (w * rotation θ * w⁻¹)⁻¹ * κ⁻¹ = (κ * w) * (rotation θ)⁻¹ * (κ * w)⁻¹ by group]
      exact pairDensity_conj_inv_rotation _ _ _

end Density

/-- The finite block weights at each fixed left factor are constant along the compact flags. -/
def RealCartanPlacedWeightsStatement : Prop :=
  ∀ (r s t : ℕ) (b : Fin t → RealBlock) (h : 2 * r + s = ∑ i, blockSizes b i)
    (x : Coordinates r s) (e : Assignment (blockSizes b) (cartanLabel h))
    (κ : LeviFrame (blockSizes b)) (i : Fin t),
    frameDensity b i (fixedLeftFrame (blockSizes b) (matchedOrthogonal b h x e) κ i) =
      slotDensity x (b i) (matchedSlot h e i)

theorem realCartanPlacedWeights : RealCartanPlacedWeightsStatement := by
  intro r s t b h x e κ i
  let R := matchedSmall b h x e i
  let k := compactEquiv (blockSizes b i) (κ i)
  change blockDensity (b i) (compactEquiv (blockSizes b i)
    (κ i * (matchedOrthogonal b h x e i)⁻¹ * (κ i)⁻¹)) = _
  simp only [map_mul (compactEquiv (blockSizes b i)), map_inv (compactEquiv (blockSizes b i))]
  exact blockDensity_conj_inv_source x (b i) (matchedSlot h e i) (matchedIndexEquiv h e i)
    R k (matchedSmall_val b h x e i)

end Langlands.Archimedean.RealCartanPlacedWeights
