import Langlands.BushnellKutzko.FiniteMatrixGaussOperators
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Injectivity of the finite matrix Gauss operator

Additive character orthogonality and induction on the matrix rank prove
`FiniteMatrixGaussInjectivityStatement` on arbitrary complex representations.
-/

namespace Langlands.BushnellKutzko

open Matrix
open scoped BigOperators Classical

universe uK uV

noncomputable section

variable {k : Type uK} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite k] : Fintype (GL ι k) :=
  Fintype.ofFinite _

private theorem sum_char_of_surjective {A : Type*} [AddGroup A] [Fintype A]
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (f : A →+ k) (hf : Function.Surjective f) :
    ∑ a : A, ψ (f a) = 0 := by
  change ∑ a : A, ψ.compAddMonoidHom f a = 0
  apply AddChar.sum_eq_zero_iff_ne_zero.mpr
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨a, rfl⟩ := hf x
  exact AddChar.ne_zero_iff.mpr ⟨a, hx⟩

private theorem sum_trace_mul [Fintype k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (B : Matrix ι κ k) (hB : B ≠ 0) :
    ∑ A : Matrix κ ι k, ψ (trace (A * B)) = 0 := by
  let f : Matrix κ ι k →+ k :=
    { toFun := fun A => trace (A * B)
      map_zero' := by rw [Matrix.zero_mul, trace_zero]
      map_add' := fun A C => by rw [Matrix.add_mul, trace_add] }
  apply sum_char_of_surjective ψ hψ f
  have hentry : ∃ i j, B i j ≠ 0 := by
    contrapose! hB
    exact Matrix.ext hB
  obtain ⟨i, j, hij⟩ := hentry
  intro x
  refine ⟨Matrix.single j i (x / B i j), ?_⟩
  change trace (Matrix.single j i (x / B i j) * B) = x
  rw [trace_single_mul, smul_eq_mul, div_mul_cancel₀ _ hij]

section Fourier

variable [Fintype k]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ψ : AddChar k ℂ) (ρ : Representation ℂ (GL ι k) V)

/-- The matrix trace Fourier coefficient with the representation as its weight. -/
private def gaussSum (A : Matrix ι ι k) : V →ₗ[ℂ] V :=
  ∑ g : GL ι k, ψ (trace (A * g.val)) • ρ g

private theorem gaussSum_apply (A : Matrix ι ι k) (v : V) :
    gaussSum ψ ρ A v = ∑ g : GL ι k, ψ (trace (A * g.val)) • ρ g v := by
  simp [gaussSum, LinearMap.sum_apply]

private theorem gaussSum_one_apply (v : V) :
    gaussSum ψ ρ 1 v = ∑ g : GL ι k, ψ (trace g.val) • ρ g v := by
  simp only [gaussSum_apply, Matrix.one_mul]

private theorem gaussSum_translate (A : Matrix ι ι k) (h : GL ι k) (v : V) :
    ρ h (gaussSum ψ ρ (A * h.val) v) = gaussSum ψ ρ A v := by
  simp only [gaussSum_apply, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  change ψ (trace (A * h.val * g.val)) • ρ (h * g) v =
    ψ (trace (A * (h * g).val)) • ρ (h * g) v
  rw [Units.val_mul, Matrix.mul_assoc]

private theorem gaussSum_one_comm (h : GL ι k) (v : V) :
    gaussSum ψ ρ 1 (ρ h v) = ρ h (gaussSum ψ ρ 1 v) := by
  rw [gaussSum_one_apply ψ ρ (ρ h v), gaussSum_one_apply ψ ρ v, map_sum]
  simp only [map_smul, ← Module.End.mul_apply, ← map_mul]
  refine Fintype.sum_equiv (M := V) ((Equiv.mulLeft h⁻¹).trans (Equiv.mulRight h)) _ _ fun g => ?_
  change ψ (trace g.val) • ρ (g * h) v =
    ψ (trace ((h⁻¹ * g * h).val)) • ρ (h * (h⁻¹ * g * h)) v
  rw [Units.val_mul, Units.val_mul, trace_units_conj']
  rw [← mul_assoc h (h⁻¹ * g), ← mul_assoc h h⁻¹, mul_inv_cancel, one_mul]

private theorem gaussSum_preserves_kernel (A : Matrix ι ι k) {v : V}
    (hv : gaussSum ψ ρ 1 v = 0) : gaussSum ψ ρ 1 (gaussSum ψ ρ A v) = 0 := by
  simp only [gaussSum_apply ψ ρ A v, map_sum, map_smul, gaussSum_one_comm, hv, map_zero,
    smul_zero, Finset.sum_const_zero]

private theorem gaussSum_fourier (hψ : ψ ≠ 1) (v : V) :
    (∑ A : Matrix ι ι k, ψ (-trace A) • gaussSum ψ ρ A v) =
      (Fintype.card (Matrix ι ι k) : ℂ) • v := by
  calc
    _ = ∑ g : GL ι k, (∑ A : Matrix ι ι k, ψ (trace (A * (g.val - 1)))) • ρ g v := by
      simp only [gaussSum_apply, Finset.smul_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun A _ => ?_
      rw [smul_smul, mul_comm, ← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one,
        trace_sub, sub_eq_add_neg]
    _ = _ := by
      rw [Finset.sum_eq_single (1 : GL ι k)]
      · simp
      · intro g _ hg
        have hg' : g.val - 1 ≠ 0 := by
          intro hz
          exact hg (Units.ext (sub_eq_zero.mp hz))
        rw [sum_trace_mul ψ hψ _ hg', zero_smul]
      · simp

end Fourier

private theorem exists_zero_first_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hA : A.det = 0) (first : ι) :
    ∃ h : GL ι k, ∀ i, (A * h.val) i first = 0 := by
  obtain ⟨x, hx, hAx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  have hentry : ∃ j, x j ≠ 0 := by
    contrapose! hx
    exact funext hx
  obtain ⟨j, hj⟩ := hentry
  let C := (1 : Matrix ι ι k).updateCol j x
  have hC : C.det = x j := by
    simpa [C, Matrix.one_apply, mul_ite] using Matrix.det_updateCol_sum (1 : Matrix ι ι k) j x
  let σ := Equiv.swap first j
  have hdet : (C.submatrix id σ).det ≠ 0 := by
    have hsign : IsUnit (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k) :=
      (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom k)
    rw [Matrix.det_permute' σ, hC]
    exact mul_ne_zero hsign.ne_zero hj
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, C, σ] using congrFun hAx i

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem trace_blocks (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) k) :
    trace M = M (Sum.inl ()) (Sum.inl ()) + trace M.toBlocks₂₂ := by
  simp [trace, Fintype.sum_sum_type, Matrix.toBlocks₂₂]

/-- An invertible two-block upper triangular matrix with a one-dimensional first block. -/
private def blockUpper (a : kˣ) (X : Matrix Unit ι k) (D : GL ι k) : GL (Unit ⊕ ι) k :=
  GeneralLinearGroup.mkOfDetNeZero (fromBlocks (Matrix.scalar Unit (a : k)) X 0 D.val) (by
    rw [det_fromBlocks_zero₂₁, det_unique, Matrix.scalar_apply, diagonal_apply_eq]
    exact mul_ne_zero a.ne_zero D.det_ne_zero)

private theorem trace_blockUpper (a : kˣ) (X : Matrix Unit ι k) (D : GL ι k) :
    trace (blockUpper a X D).val = (a : k) + trace D.val := by
  rw [trace_blocks]
  simp [blockUpper, Matrix.scalar_apply]

/-- The block embedding that acts as the identity on the first coordinate line. -/
private def lowerBlock : GL ι k →* GL (Unit ⊕ ι) k where
  toFun D := blockUpper 1 0 D
  map_one' := Units.ext (by simp [blockUpper])
  map_mul' D E := Units.ext (by simp [blockUpper, fromBlocks_multiply])

private theorem blockUpper_factor (a : kˣ) (X : Matrix Unit ι k) (D : GL ι k) :
    lowerBlock D * blockUpper a X 1 = blockUpper a X D := by
  apply Units.ext
  simp [lowerBlock, blockUpper, fromBlocks_multiply]

private def blockUpperEquiv :
    (GL ι k × (Matrix Unit ι k × kˣ)) ≃ {g : GL (Unit ⊕ ι) k // g.val.toBlocks₂₁ = 0} :=
  Equiv.ofBijective (fun p => ⟨blockUpper p.2.2 p.2.1 p.1, rfl⟩) (by
    constructor
    · rintro ⟨D, X, a⟩ ⟨E, Y, b⟩ h
      have hv := congrArg (fun g : {g : GL (Unit ⊕ ι) k // g.val.toBlocks₂₁ = 0} => g.val.val) h
      obtain ⟨hab, hXY, -, hDE⟩ := fromBlocks_inj.mp hv
      have hab' : a = b := Units.ext (by
        simpa [Matrix.scalar_apply] using congrArg (fun M : Matrix Unit Unit k => M () ()) hab)
      exact Prod.ext (Units.ext hDE) (Prod.ext hXY hab')
    · rintro ⟨g, hg⟩
      let a := g.val.toBlocks₁₁ () ()
      let D := g.val.toBlocks₂₂
      have hblocks : g.val = fromBlocks (Matrix.scalar Unit a) g.val.toBlocks₁₂ 0 D := by
        have ha : Matrix.scalar Unit a = g.val.toBlocks₁₁ := by
          ext i j
          cases i
          cases j
          simp [a, Matrix.scalar_apply]
        rw [ha, ← hg, fromBlocks_toBlocks]
      have hdet := g.det_ne_zero
      rw [hblocks, det_fromBlocks_zero₂₁, det_unique, Matrix.scalar_apply, diagonal_apply_eq] at hdet
      refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero D (right_ne_zero_of_mul hdet),
        g.val.toBlocks₁₂, Units.mk0 a (left_ne_zero_of_mul hdet)⟩, ?_⟩
      exact Subtype.ext (Units.ext hblocks.symm))

private theorem trace_mul_shear (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) k)
    (X : Matrix Unit ι k) :
    trace (M * (blockUpper 1 X 1).val) = trace M + trace (X * M.toBlocks₂₁) := by
  have hmul :
      M * (blockUpper 1 X 1).val =
        fromBlocks M.toBlocks₁₁ (M.toBlocks₁₁ * X + M.toBlocks₁₂) M.toBlocks₂₁
          (M.toBlocks₂₁ * X + M.toBlocks₂₂) := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    simp [blockUpper, fromBlocks_multiply]
  rw [hmul, trace_blocks, trace_blocks M, toBlocks_fromBlocks₂₂, trace_add,
    trace_mul_comm X M.toBlocks₂₁]
  simp [add_comm, add_assoc, Matrix.toBlocks₁₁]

private theorem mul_blockUpper_of_zero_column {A : Matrix (Unit ⊕ ι) (Unit ⊕ ι) k}
    (hA : ∀ i, A i (Sum.inl ()) = 0) (a : kˣ) (X : Matrix Unit ι k) :
    A * (blockUpper a X 1).val = A := by
  have h₁₁ : A.toBlocks₁₁ = 0 := by
    ext i j
    cases j
    exact hA _
  have h₂₁ : A.toBlocks₂₁ = 0 := by
    ext i j
    cases j
    exact hA _
  rw [← A.fromBlocks_toBlocks, h₁₁, h₂₁]
  simp [blockUpper, fromBlocks_multiply]

variable [Fintype k]
variable (ψ : AddChar k ℂ) (ρ : Representation ℂ (GL (Unit ⊕ ι) k) V)

private theorem sum_char_units (hψ : ψ ≠ 1) : ∑ a : kˣ, ψ (a : k) = -1 := by
  have hk : ∑ a : k, ψ a = 0 :=
    AddChar.sum_eq_zero_iff_ne_zero.mpr (AddChar.ne_zero_iff.mpr (AddChar.ne_one_iff.mp hψ))
  have hne : (∑ a : kˣ, ψ (a : k)) = ∑ a ∈ Finset.univ.erase (0 : k), ψ a := by
    calc
      _ = ∑ a : {a : k // a ≠ 0}, ψ a.val :=
        Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_subtype _ (fun a => by simp) fun a => ψ a).symm
  apply eq_neg_of_add_eq_zero_left
  rw [hne, ← ψ.map_zero_eq_one, add_comm]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))).trans hk

/-- Averaging over the shears keeps precisely the upper triangular block matrices. -/
private theorem gaussSum_eq_upperTriangular (hψ : ψ ≠ 1) (v : V)
    (hv : ∀ X : Matrix Unit ι k, ρ (blockUpper 1 X 1) v = v) :
    gaussSum ψ ρ 1 v =
      ∑ g : {g : GL (Unit ⊕ ι) k // g.val.toBlocks₂₁ = 0},
        ψ (trace g.val.val) • ρ g.val v := by
  let c : ℂ := Fintype.card (Matrix Unit ι k)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have htranslate (X : Matrix Unit ι k) :
      (∑ g : GL (Unit ⊕ ι) k, ψ (trace (g.val * (blockUpper 1 X 1).val)) • ρ g v) =
        gaussSum ψ ρ 1 v := by
    rw [gaussSum_one_apply]
    refine Fintype.sum_equiv (Equiv.mulRight (blockUpper 1 X 1)) _ _ fun g => ?_
    change ψ (trace (g.val * (blockUpper 1 X 1).val)) • ρ g v =
      ψ (trace (g.val * (blockUpper 1 X 1).val)) • ρ (g * blockUpper 1 X 1) v
    rw [map_mul, Module.End.mul_apply, hv X]
  have havg :
      (∑ X : Matrix Unit ι k, ∑ g : GL (Unit ⊕ ι) k,
        ψ (trace (g.val * (blockUpper 1 X 1).val)) • ρ g v) = c • gaussSum ψ ρ 1 v := by
    simp only [htranslate, Finset.sum_const, Finset.card_univ, c, Nat.cast_smul_eq_nsmul]
  have hweight (g : GL (Unit ⊕ ι) k) :
      (∑ X : Matrix Unit ι k, ψ (trace (g.val * (blockUpper 1 X 1).val)) • ρ g v) =
        if g.val.toBlocks₂₁ = 0 then c • (ψ (trace g.val) • ρ g v) else 0 := by
    simp only [trace_mul_shear, AddChar.map_add_eq_mul]
    simp_rw [mul_comm (ψ (trace g.val)), ← smul_smul, ← Finset.sum_smul]
    by_cases hg : g.val.toBlocks₂₁ = 0
    · simp [hg, c]
    · rw [ite_eq_right hg, sum_trace_mul ψ hψ _ hg, zero_smul]
  rw [Finset.sum_comm] at havg
  simp_rw [hweight] at havg
  rw [← Finset.sum_filter, ← Finset.smul_sum, ← Finset.sum_subtype_eq_sum_filter,
    Finset.subtype_univ] at havg
  exact smul_right_injective V hc havg.symm

/-- On vectors fixed by `[a X; 0 I]`, the first diagonal block contributes `-1`. -/
private theorem gaussSum_on_fixed (hψ : ψ ≠ 1) (v : V)
    (hv : ∀ (a : kˣ) (X : Matrix Unit ι k), ρ (blockUpper a X 1) v = v) :
    gaussSum ψ ρ 1 v =
      -(Fintype.card (Matrix Unit ι k) : ℂ) • gaussSum ψ (ρ.comp lowerBlock) 1 v := by
  rw [gaussSum_eq_upperTriangular ψ ρ hψ v (hv 1), ← (blockUpperEquiv (ι := ι) (k := k)).sum_comp]
  simp only [Fintype.sum_prod_type, gaussSum_one_apply]
  have hterm (D : GL ι k) (X : Matrix Unit ι k) (a : kˣ) :
      ψ (trace (blockUpper a X D).val) • ρ (blockUpper a X D) v =
        (ψ (a : k) * ψ (trace D.val)) • ρ (lowerBlock D) v := by
    rw [trace_blockUpper, AddChar.map_add_eq_mul, ← blockUpper_factor a X D, map_mul,
      Module.End.mul_apply, hv a X]
  change (∑ D : GL ι k, ∑ X : Matrix Unit ι k, ∑ a : kˣ,
    ψ (trace (blockUpper a X D).val) • ρ (blockUpper a X D) v) = _
  simp_rw [hterm, ← smul_smul, ← Finset.sum_smul, sum_char_units ψ hψ,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul, smul_eq_mul, mul_neg_one, Finset.smul_sum, MonoidHom.comp_apply]

private theorem gaussSum_injective_block (hψ : ψ ≠ 1)
    (hsmall : ∀ σ : Representation ℂ (GL ι k) V, Function.Injective (gaussSum ψ σ 1)) :
    Function.Injective (gaussSum ψ ρ 1) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  have hfixed (w : V) (hw : gaussSum ψ ρ 1 w = 0)
      (hfix : ∀ (a : kˣ) (X : Matrix Unit ι k), ρ (blockUpper a X 1) w = w) : w = 0 := by
    rw [gaussSum_on_fixed ψ ρ hψ w hfix] at hw
    have hcard : -(Fintype.card (Matrix Unit ι k) : ℂ) ≠ 0 := by
      exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    apply hsmall (ρ.comp lowerBlock)
    rw [map_zero]
    exact (smul_eq_zero_iff_right hcard).mp hw
  intro v hv
  have hvanish (A : Matrix (Unit ⊕ ι) (Unit ⊕ ι) k) : gaussSum ψ ρ A v = 0 := by
    by_cases hA : A.det = 0
    · obtain ⟨h, hh⟩ := exists_zero_first_column A hA (Sum.inl ())
      have hfix (a : kˣ) (X : Matrix Unit ι k) :
          ρ (blockUpper a X 1) (gaussSum ψ ρ (A * h.val) v) = gaussSum ψ ρ (A * h.val) v := by
        simpa only [mul_blockUpper_of_zero_column hh] using
          gaussSum_translate ψ ρ (A * h.val) (blockUpper a X 1) v
      rw [← gaussSum_translate ψ ρ A h v,
        hfixed _ (gaussSum_preserves_kernel ψ ρ _ hv) hfix, map_zero]
    · let h : GL (Unit ⊕ ι) k := GeneralLinearGroup.mkOfDetNeZero A hA
      have htranslate := gaussSum_translate ψ ρ h.val h⁻¹ v
      rw [Units.mul_inv, hv, map_zero] at htranslate
      exact htranslate.symm
  have hfourier := gaussSum_fourier ψ ρ hψ v
  simp only [hvanish, smul_zero, Finset.sum_const_zero] at hfourier
  exact (smul_eq_zero_iff_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mp hfourier.symm

end Blocks

section Reindex

variable [Fintype k]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def reindexGL (e : ι ≃ κ) : GL ι k ≃* GL κ k :=
  Units.mapEquiv (reindexRingEquiv k e).toMulEquiv

private theorem gaussSum_reindex (e : ι ≃ κ) (ψ : AddChar k ℂ)
    (ρ : Representation ℂ (GL κ k) V) (v : V) :
    gaussSum ψ (ρ.comp (reindexGL e).toMonoidHom) 1 v = gaussSum ψ ρ 1 v := by
  rw [gaussSum_one_apply, gaussSum_one_apply]
  let f : GL ι k ≃* GL κ k := reindexGL e
  refine Fintype.sum_equiv f.toEquiv _ _ fun g => ?_
  have htrace : trace (f g).val = trace g.val :=
    e.symm.sum_comp (fun i => g.val i i)
  change ψ (trace g.val) • ρ (f g) v = ψ (trace (f g).val) • ρ (f g) v
  rw [htrace]

end Reindex

/-- The finite matrix Gauss operator is injective in every rank. -/
theorem finiteMatrixGaussInjectivity : FiniteMatrixGaussInjectivityStatement.{uK, uV} := by
  intro k _ _ n ψ hψ V _ _ ρ
  suffices h : Function.Injective (gaussSum ψ ρ 1) by
    intro v w hvw
    apply h
    simpa only [gaussSum_one_apply] using hvw
  induction n with
  | zero =>
      have : Subsingleton (GL (Fin 0) k) :=
        ⟨fun g h => Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
      have h (v : V) : gaussSum ψ ρ 1 v = v := by
        rw [gaussSum_one_apply, Fintype.sum_subsingleton _ (1 : GL (Fin 0) k)]
        simp
      exact fun v w hvw => (h v).symm.trans (hvw.trans (h w))
  | succ n ih =>
      let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
        ((Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) (Equiv.refl (Fin n))).trans
          finSumFinEquiv).trans (finCongr (Nat.add_comm 1 n))
      have hinj := gaussSum_injective_block ψ (ρ.comp (reindexGL e).toMonoidHom) hψ ih
      intro v w hvw
      apply hinj
      simpa only [gaussSum_reindex e ψ ρ] using hvw

end

end Langlands.BushnellKutzko
