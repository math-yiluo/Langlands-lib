import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth
import Langlands.Cohomology.CechCup

/-! # Ordered actual-unit cocycles presenting line bundles -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard.UnitCechPresentation

open Langlands.Cohomology Cech

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- Encode overlap units as an ordered one-cochain of the actual unit presheaf. -/
def transitionCochain (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ) :
    C (NilpotentUnitReduction.unitsPresheaf X.presheaf) U 1 :=
  fun σ => res (le_inf (inter_le_apply σ 0) (inter_le_apply σ 1))
    (Additive.ofMul (g (σ 0) (σ 1)))

lemma res_transitionCochain (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ) (i j : ι)
    {W : X.Opens} (hW : W ≤ U i ⊓ U j) :
    res (hW.trans (Cech.inter_two (U := U) i j).ge) (transitionCochain U g ![i, j]) =
      res hW (Additive.ofMul (g i j)) := by
  dsimp only [transitionCochain]
  rw [res_res]
  rfl

/-- Restricting the encoded cochain back to pairs recovers the actual overlap units. -/
lemma transitionCochain_pair (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ) (i j : ι) :
    (res (Cech.inter_two (U := U) i j).ge (transitionCochain U g ![i, j])).toMul =
      g i j := by
  have h := res_transitionCochain U g i j le_rfl
  rw [res_self] at h
  exact congrArg Additive.toMul h

/-- Encoding and restricting are inverse on all ordered one-cochains. -/
lemma transitionCochain_pairRestriction
    (z : C (NilpotentUnitReduction.unitsPresheaf X.presheaf) U 1) :
    transitionCochain U (fun i j =>
      (res (Cech.inter_two (U := U) i j).ge (z ![i, j])).toMul) = z := by
  funext σ
  have hσ : ![σ 0, σ 1] = σ := by
    funext i
    fin_cases i <;> rfl
  change res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
      (le_inf (inter_le_apply σ 0) (inter_le_apply σ 1))
      (res (Cech.inter_two (U := U) (σ 0) (σ 1)).ge (z ![σ 0, σ 1])) = z σ
  rw [res_res]
  rw [Cech.res_congr (NilpotentUnitReduction.unitsPresheaf X.presheaf) U hσ z _ le_rfl]
  exact res_self _ _

/-- Multiplicative transition cocycles become closed ordered actual-unit cochains. -/
lemma d_transitionCochain (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ)
    (hg : CocycleGluing.IsCocycle g) :
    d (NilpotentUnitReduction.unitsPresheaf X.presheaf) U 1 (transitionCochain U g) = 0 := by
  funext τ
  have h :
      res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
        (le_inf (inter_le_apply τ 0) (inter_le_apply τ 1))
          (Additive.ofMul (g (τ 0) (τ 1))) +
        res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
          (le_inf (inter_le_apply τ 1) (inter_le_apply τ 2))
          (Additive.ofMul (g (τ 1) (τ 2))) =
      res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
        (le_inf (inter_le_apply τ 0) (inter_le_apply τ 2))
          (Additive.ofMul (g (τ 0) (τ 2))) := by
    apply congrArg Additive.ofMul
    apply Units.ext
    exact CocycleGluing.cocycle_res g hg (τ 0) (τ 1) (τ 2) _ _ _
  rw [d_apply, Fin.sum_univ_three]
  simp only [transitionCochain, res_res, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, neg_one_sq, one_smul, neg_smul, Pi.zero_apply]
  change res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
      (le_inf (inter_le_apply τ 1) (inter_le_apply τ 2))
      (Additive.ofMul (g (τ 1) (τ 2))) +
    -res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
      (le_inf (inter_le_apply τ 0) (inter_le_apply τ 2))
      (Additive.ofMul (g (τ 0) (τ 2))) +
    res (P := NilpotentUnitReduction.unitsPresheaf X.presheaf)
      (le_inf (inter_le_apply τ 0) (inter_le_apply τ 1))
      (Additive.ofMul (g (τ 0) (τ 1))) = 0
  rw [← h]
  abel

/-- Closedness of the encoding is equivalent to the original transition cocycle equation. -/
lemma d_transitionCochain_eq_zero_iff (g : ∀ i j : ι, (Γ(X, U i ⊓ U j))ˣ) :
    d (NilpotentUnitReduction.unitsPresheaf X.presheaf) U 1 (transitionCochain U g) = 0 ↔
      CocycleGluing.IsCocycle g := by
  refine ⟨?_, d_transitionCochain U g⟩
  intro hz i j k
  have h := Cech.cocycle_add hz i j k
    ((inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j).trans
      (Cech.inter_two (U := U) i j).ge)
    ((le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      U i ⊓ U j ⊓ U k ≤ U j ⊓ U k).trans (Cech.inter_two (U := U) j k).ge)
    ((le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      U i ⊓ U j ⊓ U k ≤ U i ⊓ U k).trans (Cech.inter_two (U := U) i k).ge)
  rw [res_transitionCochain, res_transitionCochain, res_transitionCochain] at h
  exact congrArg (fun a => (a.toMul : (Γ(X, U i ⊓ U j ⊓ U k))ˣ).val) h

/-- Finite full affine-cover transition data whose glued sheaf is the given module sheaf. -/
structure FinitePresentation (M : X.Modules) where
  cover : X.OrderedAffineCover
  transitions : ∀ i j : cover.ι, (Γ(X, cover.U i ⊓ cover.U j))ˣ
  cocycle : CocycleGluing.IsCocycle transitions
  iso : M ≅ CocycleGluing.glued transitions

namespace FinitePresentation

variable {M : X.Modules} (D : FinitePresentation M)

/-- The actual-unit ordered cocycle of a finite presentation. -/
def cochain : C (NilpotentUnitReduction.unitsPresheaf X.presheaf) D.cover.U 1 :=
  transitionCochain D.cover.U D.transitions

lemma closed :
    d (NilpotentUnitReduction.unitsPresheaf X.presheaf) D.cover.U 1 D.cochain = 0 :=
  d_transitionCochain D.cover.U D.transitions D.cocycle

lemma cochain_pair (i j : D.cover.ι) :
    (res (Cech.inter_two (U := D.cover.U) i j).ge (D.cochain ![i, j])).toMul =
      D.transitions i j :=
  transitionCochain_pair D.cover.U D.transitions i j

/-- The module is recovered by gluing the pair restrictions of its closed ordered cochain. -/
def cochainIso : M ≅ CocycleGluing.glued (fun i j =>
    (res (Cech.inter_two (U := D.cover.U) i j).ge (D.cochain ![i, j])).toMul) := by
  simpa only [D.cochain_pair] using D.iso

include D in
/-- Every such presentation is an actual locally free rank-one sheaf. -/
lemma isLocallyFreeRankOne : IsLocallyFreeRankOne M :=
  (CocycleGluing.isLocallyFreeRankOne_glued D.transitions D.cover.iSup_eq_top D.cocycle).of_iso
    D.iso.symm

end FinitePresentation

/-- Every actual line bundle on a compact scheme has a finite affine ordered-unit
cocycle presentation, with its underlying sheaf recovered by the gluing isomorphism. -/
lemma exists_finitePresentation [CompactSpace X] {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) : Nonempty (FinitePresentation M) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := Langlands.AlgebraicGeometry.Modules.BiCech.exists_frameCover hM
  choose e he using h𝒰
  exact ⟨{
    cover := 𝒰
    transitions := CocycleGluing.frameCocycle e he
    cocycle := CocycleGluing.isCocycle_of_isTransition he
      (CocycleGluing.isTransition_frameCocycle he)
    iso := CocycleGluing.frameIso he (CocycleGluing.isTransition_frameCocycle he)
      𝒰.iSup_eq_top }⟩

lemma nonempty_finitePresentation_iff [CompactSpace X] (M : X.Modules) :
    Nonempty (FinitePresentation M) ↔ IsLocallyFreeRankOne M :=
  ⟨fun ⟨D⟩ => D.isLocallyFreeRankOne, exists_finitePresentation⟩

end Langlands.AlgebraicGeometry.Picard.UnitCechPresentation
