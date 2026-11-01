import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Group.GL.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Compact matrix support on central saturations -/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis
open scoped Topology

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [IsTopologicalDivisionRing F] [T2Space F] {n : ℕ}

/-- All scalar translates of a specified set of invertible matrices. -/
def scalarSaturation (K : Set (Langlands.GeneralLinear (n + 1) F)) :
    Set (Langlands.GeneralLinear (n + 1) F) :=
  {g | ∃ a : Fˣ, ∃ k ∈ K, g = GeneralLinear.scalar a * k}

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F] in
private theorem scalar_mul_val (a : Fˣ)
    (k : Langlands.GeneralLinear (n + 1) F) :
    (GeneralLinear.scalar a * k).val = (a : F) • k.val := by
  change Matrix.scalar (Fin (n + 1)) (a : F) * k.val = _
  ext i j
  simp [Matrix.scalar, Matrix.diagonal_mul]

/-- A compact set of matrices away from zero cuts the scalar saturation of a
compact subset of GL down to a set contained in a compact subset of GL. -/
theorem exists_isCompact_cover_scalarSaturation
    (K : Set (Langlands.GeneralLinear (n + 1) F)) (hK : IsCompact K)
    (S : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hS : IsCompact S) (hS0 : (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) ∉ S) :
    ∃ C : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C ∧
      ∀ g ∈ scalarSaturation K, g.val ∈ S → g ∈ C := by
  let M := Matrix (Fin (n + 1)) (Fin (n + 1)) F
  let G := Langlands.GeneralLinear (n + 1) F
  let a : M × G → F := fun p => (p.1 * (p.2⁻¹).val) 0 0
  have ha : Continuous a := by
    have hi : Continuous (fun p : M × G => (p.2⁻¹).val) :=
      Units.continuous_val.comp (continuous_snd.inv)
    exact (continuous_apply 0).comp
      ((continuous_apply 0).comp (continuous_fst.mul hi))
  let P : Set (M × G) := (S ×ˢ K) ∩ {p | p.1 = a p • p.2.val}
  have hP : IsCompact P :=
    (hS.prod hK).inter_right
      (isClosed_eq continuous_fst (ha.smul (Units.continuous_val.comp continuous_snd)))
  have ha0 (p : P) : a p.val ≠ 0 := by
    intro hz
    have hp : p.val.1 = 0 := by simpa [hz] using p.property.2
    exact hS0 (hp ▸ p.property.1.1)
  let au : P → Fˣ := fun p => Units.mk0 (a p.val) (ha0 p)
  have hau : Continuous au :=
    Units.isEmbedding_val₀.continuous_iff.mpr (ha.comp continuous_subtype_val)
  let f : P → G := fun p => GeneralLinear.scalar (au p) * p.val.2
  have hf : Continuous f :=
    ((GeneralLinear.scalarContinuous (n := n + 1)).continuous.comp hau).mul
      (continuous_snd.comp continuous_subtype_val)
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro g hg hgs
  obtain ⟨b, k, hk, hgb⟩ := hg
  have heq : a (g.val, k) = (b : F) := by
    dsimp [a]
    rw [hgb, scalar_mul_val, smul_mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    change (b : F) * ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) 0 0) = (b : F)
    simp
  have hpair : (g.val, k) ∈ P := by
    refine ⟨⟨hgs, hk⟩, ?_⟩
    change g.val = a (g.val, k) • k.val
    rw [heq, hgb, scalar_mul_val]
  refine ⟨⟨(g.val, k), hpair⟩, ?_⟩
  change GeneralLinear.scalar (au ⟨(g.val, k), hpair⟩) * k = g
  have hu : au ⟨(g.val, k), hpair⟩ = b := Units.ext heq
  rw [hu, hgb]

/-- A matrix test vanishing at zero cuts a coefficient supported in a compact
central saturation down to compact support on GL. -/
theorem hasCompactSupport_test_mul_of_scalarSaturation
    (Φ : MatrixTestFunction n F) (hΦ0 : Φ 0 = 0)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (K : Set (Langlands.GeneralLinear (n + 1) F)) (hK : IsCompact K)
    (hf : Function.support f ⊆ scalarSaturation K) :
    HasCompactSupport (fun g => Φ g.val * f g) := by
  have hs : IsClosed (Function.support (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ)) :=
    (Φ.locallyConstant.isOpen_fiber 0).isClosed_compl
  have hΦzero : (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) ∉
      tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) := by
    change 0 ∉ closure (Function.support (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ))
    rw [hs.closure_eq]
    exact fun h => h hΦ0
  obtain ⟨C, hC, hc⟩ := exists_isCompact_cover_scalarSaturation K hK
    (tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ)) Φ.hasCompactSupport hΦzero
  apply HasCompactSupport.intro hC
  intro g hg
  by_contra hn
  exact hg (hc g (hf (right_ne_zero_of_mul hn))
    (subset_tsupport _ (left_ne_zero_of_mul hn)))

end Langlands.GodementJacquet
