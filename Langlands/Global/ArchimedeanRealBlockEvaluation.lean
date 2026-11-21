import Langlands.Global.ArchimedeanCompactBlockEvaluation
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Normalized block tensor evaluations of the original-order real standard module -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean
open Archimedean.RealLeviSlices (flat sz emb emb_eq realPositionCharacter_flat
  realInducedBlockAt_flat)
open Archimedean.RealLeviChart (start pos val_pos cls cls_pos blockDiagGL blockDiagGL_mem_unitaryCompact
  blockDiagGL_val blockDiagHom_pos_pos_self blockDiagHom_pos_pos_of_ne start_succ_le)
open Archimedean.InductionStages
open AdelicBlockScalarSections (indexedEvaluation)

variable {c : ℕ} (ds : Fin c → List LocalFactor.Archimedean.RealBlock)

local notation "N" => (∑ i, sz ds i)
local notation "G" => Langlands.GeneralLinear
local notation "K" => unitaryCompact ℝ

theorem realBlockBound (i : Fin c) : start (sz ds) i + sz ds i ≤ N := by
  have ht : start (sz ds) c = N := by
    rw [start, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => dite_eq_left j.isLt
  exact ht ▸ start_succ_le (sz ds) i.isLt i.isLt

private theorem realBlockIndex (i : Fin c) (a : Fin (sz ds i)) :
    idx (realBlockBound ds i) a = pos (sz ds) i a :=
  Fin.ext ((val_pos (sz ds) i a).symm)

private theorem realBlockOutside {i j : Fin c} (hij : j ≠ i) (a : Fin (sz ds j)) :
    ¬ IsMid (start (sz ds) i) (sz ds i) (pos (sz ds) j a) := by
  intro h
  obtain ⟨b, hb⟩ := exists_idx_of_isMid (realBlockBound ds i) h
  rw [realBlockIndex] at hb
  exact hij ((cls_pos (sz ds) j a).symm.trans
    ((congrArg (cls (sz ds)) hb).trans (cls_pos (sz ds) i b)))

theorem realBlockEmbedding_eq (i : Fin c) (g : G (sz ds i) ℝ) :
    blockEmb (realBlockBound ds i) g = emb (sz ds) i g := by
  classical
  apply Units.ext
  refine Matrix.ext fun p q => ?_
  obtain ⟨⟨j, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨l, b⟩, rfl⟩ := finSigmaFinEquiv.surjective q
  change blockMat N (start (sz ds) i) (sz ds i) g.val (pos (sz ds) j a) (pos (sz ds) l b) =
    (emb (sz ds) i g).val (pos (sz ds) j a) (pos (sz ds) l b)
  rw [emb_eq, blockDiagGL_val]
  by_cases hjl : j = l
  · subst l
    rw [blockDiagHom_pos_pos_self]
    by_cases hji : j = i
    · subst j
      rw [← realBlockIndex ds i a, ← realBlockIndex ds i b,
        blockMat_apply_idx (realBlockBound ds i), Pi.mulSingle_eq_same]
    · rw [blockMat_apply_of_not_isMid_left _ (realBlockOutside ds hji a),
        Pi.mulSingle_eq_of_ne hji]
      simp only [Matrix.one_apply, Units.val_one]
      simp only [show pos (sz ds) j a = pos (sz ds) j b ↔ a = b by simp [pos]]
  · rw [blockDiagHom_pos_pos_of_ne _ _ hjl]
    have hne : pos (sz ds) j a ≠ pos (sz ds) l b := by
      intro h
      exact hjl ((cls_pos (sz ds) j a).symm.trans
        ((congrArg (cls (sz ds)) h).trans (cls_pos (sz ds) l b)))
    by_cases hji : j = i
    · subst j
      rw [blockMat_apply_of_not_isMid_right _ _ (realBlockOutside ds (Ne.symm hjl) b)]
      simp [hne]
    · rw [blockMat_apply_of_not_isMid_left _ (realBlockOutside ds hji a)]
      simp [hne]

/-- The actual block diagonal compact embedding in the given order. -/
def realCompactEmbedding : (∀ i, K (sz ds i)) →* K N where
  toFun q := ⟨blockDiagGL (sz ds) fun i => (q i).val, blockDiagGL_mem_unitaryCompact q⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' q t := Subtype.ext (map_mul (blockDiagGL (sz ds)) (fun i => (q i).val) fun i => (t i).val)

theorem realCompactEmbedding_single (i : Fin c) (x : K (sz ds i)) :
    (realCompactEmbedding ds (Pi.mulSingle i x)).val = emb (sz ds) i x.val := by
  classical
  rw [emb_eq]
  change blockDiagGL (sz ds) (fun j =>
    (Pi.mulSingle (M := fun l => ↥(K (sz ds l))) i x j).val) = _
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    rfl

/-- Normalized slice in any one of the ordered real blocks. -/
def realBlockSlice (i : Fin c) (g : K N) : KFin N (flat ds) →ₗ[ℂ] KFin (sz ds i) (ds i) :=
  ((slice (realBlockBound ds i) g.val).comp (KFin N (flat ds)).subtype).codRestrict _ (fun f => by
    refine ⟨?_, ?_⟩
    · refine ⟨slice_mem_principalSeries (realBlockBound ds i)
        (fun a => realPositionCharacter_flat ds i a a.isLt)
        (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) g.val f.2.1.1, ?_⟩
      intro p d hd k hk t
      have hp : p + 1 < sz ds i := realInducedBlockAt_lt hd
      have hh := realInducedBlockAt_flat ds i p (by omega : p < sz ds i)
      rw [LinearMap.comp_apply, Submodule.subtype_apply, blockFourierCoefficient_slice _ hp,
        f.2.1.2 _ _ (hh.trans hd) k hk, mul_zero]
    · exact slice_mem_kFiniteVectors (realBlockBound ds i) g.property f.2.2)

/-- On a compact block argument the normalized slice simply evaluates the
original standard function at the embedded block times the base point. -/
theorem realBlockSlice_compact (i : Fin c) (g : K N) (f : KFin N (flat ds))
    (x : K (sz ds i)) :
    (realBlockSlice ds i g f).val x.val = f.val (emb (sz ds) i x.val * g.val) := by
  change slice (realBlockBound ds i) g.val f.val x.val = _
  rw [slice_apply, sliceFactor_of_mem_unitaryCompact x.property, one_mul, realBlockEmbedding_eq]

/-- The compact subgroup acts on the real standard functions by right translation. -/
abbrev realCompactAction (n : ℕ) (d : List LocalFactor.Archimedean.RealBlock) :
    Representation ℂ (K n) (KFin n d) :=
  (realStandardRep n d).comp (toUnitary n)

theorem realCompactAction_apply (n : ℕ) (d : List LocalFactor.Archimedean.RealBlock)
    (k : K n) (f : KFin n d) (g : G n ℝ) :
    (realCompactAction n d k f).val g = f.val (g * k.val) :=
  kRep_apply_coe n d k f g

private theorem realCompactAction_isFiniteVector (f : KFin N (flat ds)) :
    FiniteVectors.IsFiniteVector (realCompactAction N (flat ds)) f := by
  let R := realStandardRep N (flat ds)
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan R f) :=
    (isRealGKModule_realStandardModule N (flat ds)).1 f
  apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan R f)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan R (toUnitary N k) f

/-- Restrict a real block standard function to its orthogonal compact subgroup. -/
def realBlockRestriction (i : Fin c) :
    KFin (sz ds i) (ds i) →ₗ[ℂ] (K (sz ds i) → ℂ) :=
  Archimedean.RealLeviProducts.resK _ _

theorem realBlockRestriction_injective (i : Fin c) :
    Function.Injective (realBlockRestriction ds i) := by
  intro f g h
  apply Subtype.ext
  exact eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1 g.2.1.1
    (fun x hx => congrFun h ⟨x, hx⟩)

private def realValueAtOne : KFin N (flat ds) →ₗ[ℂ] ℂ :=
  (LinearMap.proj 1).comp (KFin N (flat ds)).subtype

private theorem realBlockSlice_one_value (i : Fin c) (x : K (sz ds i)) (f : KFin N (flat ds)) :
    realBlockRestriction ds i (realBlockSlice ds i 1 f) x =
      realValueAtOne ds (realCompactAction N (flat ds)
        (realCompactEmbedding ds (Pi.mulSingle i x)) f) := by
  change (realBlockSlice ds i 1 f).val x.val = (realCompactAction N (flat ds)
    (realCompactEmbedding ds (Pi.mulSingle i x)) f).val 1
  rw [realCompactAction_apply, one_mul, realBlockSlice_compact,
    realCompactEmbedding_single]
  change f.val (emb (sz ds) i x.val * 1) = _
  rw [mul_one]

/-- The actual real standard module evaluated as a tensor of the block standard modules. -/
def realEvaluation (k : K N) : KFin N (flat ds) →ₗ[ℂ] (⨂[ℂ] i, KFin (sz ds i) (ds i)) :=
  evaluation (realCompactEmbedding ds) (realCompactAction N (flat ds)) (realValueAtOne ds)
    (realBlockRestriction ds) (fun i => realBlockSlice ds i 1) (realBlockSlice_one_value ds)
    (realBlockRestriction_injective ds) (realCompactAction_isFiniteVector ds) k

theorem realEvaluation_value (k : K N) (f : KFin N (flat ds)) (q : ∀ i, K (sz ds i)) :
    indexedEvaluation (realBlockRestriction ds) (realEvaluation ds k f) q =
      f.val ((realCompactEmbedding ds q).val * k.val) := by
  rw [realEvaluation, evaluation_value]
  change (realCompactAction N (flat ds) (realCompactEmbedding ds q * k) f).val 1 = _
  rw [realCompactAction_apply, one_mul]
  rfl

theorem realEvaluation_right (k h : K N) (f : KFin N (flat ds)) :
    realEvaluation ds k (realCompactAction N (flat ds) h f) = realEvaluation ds (k * h) f := by
  apply evaluation_right

theorem realEvaluation_left (q : ∀ i, K (sz ds i)) (k : K N) (f : KFin N (flat ds)) :
    realEvaluation ds (realCompactEmbedding ds q * k) f =
      PiTensorProduct.map (fun i => realCompactAction (sz ds i) (ds i) (q i))
        (realEvaluation ds k f) := by
  apply evaluation_left
  intro i p t f'
  exact realCompactAction_apply (sz ds i) (ds i) p f' t.val

theorem realEvaluation_separates (f : KFin N (flat ds))
    (hf : ∀ k, realEvaluation ds k f = 0) : f = 0 := by
  apply Subtype.ext
  apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1
  intro g hg
  have h := realEvaluation_value ds ⟨g, hg⟩ f 1
  simpa only [hf, map_zero, Pi.zero_apply, Submonoid.coe_one, map_one, one_mul] using h.symm

end Langlands.Global.ArchimedeanCompactBlocks
