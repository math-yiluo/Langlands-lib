import Langlands.LinearAlgebra.RootPairingChambers
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! # Cartan comparison of bases of finite rational root systems -/

noncomputable section

namespace Langlands.LinearAlgebra.RootPairingBaseComparison

variable {J M N : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]
  (P : RootPairing J ℚ M N) [P.IsRootSystem]

/-- The covector taking value one on each simple root of a supplied base. -/
def heightCovector (b : P.Base) : N :=
  P.flip.toPerfPair.symm (b.toWeightBasis.constr ℚ (fun _ => (1 : ℚ)))

/-- Evaluation on the height covector is the integer height, cast to rationals. -/
theorem root_heightCovector (b : P.Base) (i : J) :
    P.root' i (heightCovector P b) = (b.height i : ℚ) := by
  let ℓ := b.toWeightBasis.constr ℚ (fun _ => (1 : ℚ))
  have hℓ (j : J) (hj : j ∈ b.support) : ℓ (P.root j) = 1 := by
    rw [← b.toWeightBasis_apply ⟨j, hj⟩]
    exact Module.Basis.constr_basis _ _ _ _
  have hval : P.root' i (heightCovector P b) = ℓ (P.root i) := by
    change (P.flip.toPerfPair (P.flip.toPerfPair.symm ℓ)) (P.root i) = _
    rw [LinearEquiv.apply_symm_apply]
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  rw [hval, hf, map_sum, b.height_eq_sum hf, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, hℓ j hj]
  simp

/-- The base height covector is regular for the full root set. -/
theorem regular_heightCovector (b : P.Base) :
    RootPairingChambers.Regular P (heightCovector P b) := by
  intro i
  rw [root_heightCovector]
  exact_mod_cast b.height_ne_zero i

/-- Positive roots are exactly those with positive evaluation on the height covector. -/
theorem isPos_iff_heightCovector (b : P.Base) (i : J) :
    b.IsPos i ↔ 0 < P.root' i (heightCovector P b) := by
  rw [root_heightCovector, RootPairing.Base.isPos_iff]
  exact_mod_cast (Iff.rfl : 0 < b.height i ↔ 0 < b.height i)

variable [Finite J] [P.IsCrystallographic]

omit [P.IsRootSystem] in
/-- Simple roots are precisely the positive roots that are not sums of two positive roots. -/
theorem mem_support_iff_positive_indecomposable (b : P.Base) (i : J) :
    i ∈ b.support ↔ b.IsPos i ∧
      ∀ j l, b.IsPos j → b.IsPos l → P.root i ≠ P.root j + P.root l := by
  constructor
  · intro hi
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    intro j l hj hl heq
    have hh := b.height_add heq
    rw [b.height_one_of_mem_support hi] at hh
    change 0 < b.height j at hj
    change 0 < b.height l at hl
    omega
  · rintro ⟨hi, hindecomp⟩
    have h : i ∈ b.support ∨ ∃ j l, b.IsPos j ∧ b.IsPos l ∧
        P.root i = P.root j + P.root l := by
      apply hi.induction_on_add
      · intro j hj
        exact Or.inl hj
      · intro j l z hz hj hl
        apply Or.inr
        refine ⟨j, l, ?_, b.isPos_of_mem_support hl, hz⟩
        rcases hj with hj | ⟨a, c, ha, hc, hac⟩
        · exact b.isPos_of_mem_support hj
        · exact ha.add hc hac
    rcases h with h | ⟨j, l, hj, hl, heq⟩
    · exact h
    · exact False.elim (hindecomp j l hj hl heq)

omit [P.IsRootSystem] in
/-- A root-system automorphism identifying positive sets also identifies their simple supports. -/
theorem mem_support_equiv_iff_of_isPos (b c : P.Base) (e : P.Aut)
    (hpos : ∀ i, c.IsPos (e.indexEquiv i) ↔ b.IsPos i) (i : J) :
    e.indexEquiv i ∈ c.support ↔ i ∈ b.support := by
  rw [mem_support_iff_positive_indecomposable P c,
    mem_support_iff_positive_indecomposable P b, hpos]
  have hf (j : J) : e.weightEquiv (P.root j) = P.root (e.indexEquiv j) :=
    e.toHom.root_weightMap_apply P P j
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    intro j l hj hl heq
    apply h (e.indexEquiv j) (e.indexEquiv l) ((hpos j).mpr hj) ((hpos l).mpr hl)
    rw [← hf, ← hf, ← hf, heq, map_add]
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    intro j l hj hl heq
    apply h (e.indexEquiv.symm j) (e.indexEquiv.symm l)
      ((hpos (e.indexEquiv.symm j)).mp (by simpa using hj))
      ((hpos (e.indexEquiv.symm l)).mp (by simpa using hl))
    apply e.weightEquiv.injective
    rw [map_add, hf, hf, hf]
    simpa using heq

variable [Fintype J]

/-- Some Weyl-group element sends the support of either supplied base to the other. -/
theorem exists_weylGroup_maps_support (b c : P.Base) :
    ∃ w : P.weylGroup, ∀ i,
      w.val.indexEquiv i ∈ c.support ↔ i ∈ b.support := by
  obtain ⟨w, hw⟩ := RootPairingChambers.exists_weylGroup_sameChamber P
    (regular_heightCovector P b) (regular_heightCovector P c)
  refine ⟨w, mem_support_equiv_iff_of_isPos P b c w.val ?_⟩
  intro i
  rw [isPos_iff_heightCovector, isPos_iff_heightCovector]
  have he := w.val.root'_coweightEquiv i (w.val.coweightEquiv (heightCovector P c))
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [he]
  exact (hw i).symm

/-- A chosen Weyl identification of the simple supports of two bases. -/
def baseEquiv (b c : P.Base) : b.support ≃ c.support :=
  Equiv.subtypeEquiv (exists_weylGroup_maps_support P b c).choose.val.indexEquiv
    (fun i => ((exists_weylGroup_maps_support P b c).choose_spec i).symm)

/-- The chosen simple-root equivalence preserves every integer Cartan entry. -/
theorem cartanMatrix_baseEquiv (b c : P.Base) (i j : b.support) :
    c.cartanMatrix (baseEquiv P b c i) (baseEquiv P b c j) = b.cartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℚ
  simp only [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    RootPairing.algebraMap_pairingIn]
  exact (exists_weylGroup_maps_support P b c).choose.val.toHom.pairing

variable {K M₂ N₂ : Type*} [Fintype K]
  [AddCommGroup M₂] [Module ℚ M₂] [AddCommGroup N₂] [Module ℚ N₂]
  (Q : RootPairing K ℚ M₂ N₂) [Q.IsRootSystem] [Q.IsCrystallographic]

open Classical in
/-- A full-root linear equivalence identifies the Cartan matrices of any two supplied bases. -/
def rootTransportBaseEquiv (b : P.Base) (c : Q.Base)
    (f : M ≃ₗ[ℚ] M₂) (e : J ≃ K)
    (hf : ∀ i, f (P.root i) = Q.root (e i)) : b.support ≃ c.support :=
  let E := RootPairing.Equiv.mk' P Q f e hf
  (b.supportMapEquiv E).trans (baseEquiv Q (b.map E) c)

omit [Finite J] [Fintype J] in
/-- Cartan comparison needs full-root linear transport, without a prescribed simple-base map. -/
theorem cartanMatrix_rootTransportBaseEquiv (b : P.Base) (c : Q.Base)
    (f : M ≃ₗ[ℚ] M₂) (e : J ≃ K)
    (hf : ∀ i, f (P.root i) = Q.root (e i)) (i j : b.support) :
    c.cartanMatrix (rootTransportBaseEquiv P Q b c f e hf i)
      (rootTransportBaseEquiv P Q b c f e hf j) = b.cartanMatrix i j := by
  classical
  let E := RootPairing.Equiv.mk' P Q f e hf
  change c.cartanMatrix (baseEquiv Q (b.map E) c (b.supportMapEquiv E i))
    (baseEquiv Q (b.map E) c (b.supportMapEquiv E j)) = _
  rw [cartanMatrix_baseEquiv, b.map_equiv_cartanMatrix E]
  simp

end Langlands.LinearAlgebra.RootPairingBaseComparison
