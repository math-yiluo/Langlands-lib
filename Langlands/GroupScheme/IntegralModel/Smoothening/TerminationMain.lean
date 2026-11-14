import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationCore
import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationSmooth
import Langlands.GroupScheme.IntegralModel.Smoothening.SmoothSections
import Langlands.GroupScheme.IntegralModel.IntegralFunctions

/-! # The integral functions are finitely generated

This module proves `IntegralFunctionsFiniteTypeStatement`: over a Henselian discrete valuation ring
`R` with algebraically closed residue field, the integral functions `B` of a flat finitely generated
commutative Hopf algebra `A` with smooth generic fibre form a finitely generated `R`-algebra.

The members `C n` of the smoothening sequence inside `B` are finitely generated Hopf algebras.
Their defects `δ n` (the length of the torsion of the cotangent module) satisfy
`δ (n + 1) + ν n ≤ δ n`, where `ν n ≠ 0` while `δ n ≠ 0`. Hence some `δ N` vanishes. Then the
cotangent module of `C N` is torsion-free, so `C N` is smooth. A smooth member containing `A` is all
of `B`, because divisibility of the values at all `R`-points implies divisibility for smooth
algebras. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing Coalgebra Bialgebra HopfAlgebra

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

section Members

variable {R : Type u} {K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {A : Type u} [CommRing A] [HopfAlgebra R A]

/-- **Lemma S for subalgebras of the integral functions.** The algebra structure of `C` and the
Hopf structure are passed separately, together with the equation between the two algebra
structures. This keeps all hypotheses in terms of the given algebra structure. -/
theorem smooth_of_torsion_eq_bot_of_le [IsAlgClosed (ResidueField R)]
    [Algebra.FormallySmooth K (K ⊗[R] A)] {C : Type u} [CommRing C] [instC : Algebra R C]
    (inst : HopfAlgebra R C) (hinst : inst.toAlgebra = instC) [Algebra.FiniteType R C]
    [Module.Flat R C] (ι : C →ₐ[R] K ⊗[R] A)
    (hι : Function.Injective ι) (hloc : ∀ e : K ⊗[R] A, ∃ s : R, s ≠ 0 ∧ ∃ c : C, s • e = ι c)
    (ε : C →ₐ[R] R) (hε : ∀ c, ε c = @counitAlgHom R C _ _ inst.toBialgebra c)
    (heE : ∀ c, genericEval R K A (counitAlgHom R A) (ι c) = algebraMap R K (ε c))
    (htors : Submodule.torsion R (Cot ε) = ⊥) : Algebra.Smooth R C := by
  subst hinst
  obtain rfl : ε = counitAlgHom R C := AlgHom.ext hε
  exact smooth_of_torsion_eq_bot ι hι hloc _ heE htors

/-- A smooth member of the smoothening sequence containing `A` is all of `B`. -/
theorem eq_top_of_smooth [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    (S : Subalgebra R (integralFunctions R K A)) (hS : (incl R K A).range ≤ S)
    (hsm : Algebra.Smooth R S) : S = ⊤ := by
  rw [eq_top_iff]
  intro b _
  obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A (b : K ⊗[R] A)
  have hsb : s • b ∈ S := by
    have : s • b = incl R K A a := Subtype.ext (by rw [coe_incl, ← hsa]; rfl)
    rw [this]
    exact hS ⟨a, rfl⟩
  obtain ⟨c', hc'⟩ := exists_eq_smul_of_smooth_algebra S hs ⟨s • b, hsb⟩ fun χ => by
    have hχ : χ = (point (K := K) (χ.comp (inclSub S hS))).comp S.val := by
      apply algHom_ext_sub S hS
      ext a
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Subalgebra.coe_val,
        val_inclSub, point_incl, AlgHom.comp_apply]
    rw [hχ, AlgHom.comp_apply, Subalgebra.coe_val, point_smul]
    exact dvd_mul_right _ _
  have hbc : b = c' := by
    apply smul_right_injective (integralFunctions R K A) hs
    have := congrArg Subtype.val hc'
    exact this
  rw [hbc]
  exact c'.2

end Members

/-- **The integral functions are finitely generated** (KP Theorem A.6.2, BLR 3.3 Prop. 5). -/
theorem integralFunctions_finiteType : IntegralFunctionsFiniteTypeStatement.{u} := by
  intro R _ _ _ _ _ K _ _ _ A _ _ _ _ hsm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let εB := counitAlgHom R (integralFunctions R K A)
  let δ : ℕ → ℕ∞ := fun n =>
    defect R (Cot (C := chain R K A ϖ n) (subPoint εB (chain R K A ϖ n)))
  let ν : ℕ → ℕ∞ := fun n =>
    torsionByLength R (Cot (C := chain R K A ϖ n) (subPoint εB (chain R K A ϖ n))) ϖ
  have h0 : δ 0 ≠ ⊤ := by
    have : Algebra.FiniteType R (chain R K A ϖ 0) :=
      (Subalgebra.fg_iff_finiteType _).mp (chain_fg hϖ 0)
    have := Algebra.FiniteType.isNoetherianRing R (chain R K A ϖ 0)
    have := cot_finite (C := chain R K A ϖ 0) (subPoint εB (chain R K A ϖ 0))
    exact defect_ne_top
  have hstep : ∀ n, δ (n + 1) + ν n ≤ δ n := fun n => by
    have h := core_step hϖ (chain R K A ϖ n) (range_incl_le_chain ϖ n)
      (fun _ hs => comul_mem_pureSpan hϖ n hs) (fun _ hs => antipodeInt_mem n hs) (chain_fg hϖ n)
    rw [← chain_succ] at h
    exact h
  have hpos : ∀ n, δ n ≠ 0 → ν n ≠ 0 := fun n h => torsionByLength_ne_zero hϖ h
  obtain ⟨N, hN⟩ := exists_eq_zero_of_drop δ ν h0 hstep hpos
  have hS := range_incl_le_chain (K := K) (A := A) ϖ N
  have htors : Submodule.torsion R
      (Cot (C := chain R K A ϖ N) (subPoint εB (chain R K A ϖ N))) = ⊥ := by
    have h : defect R (Cot (C := chain R K A ϖ N) (subPoint εB (chain R K A ϖ N))) = 0 := hN
    rw [defect, Module.length_eq_zero_iff] at h
    exact Submodule.eq_bot_of_subsingleton
  have hft : Algebra.FiniteType R (chain R K A ϖ N) :=
    (Subalgebra.fg_iff_finiteType _).mp (chain_fg hϖ N)
  have hsmS : Algebra.Smooth R (chain R K A ϖ N) :=
    smooth_of_torsion_eq_bot_of_le (C := chain R K A ϖ N) (chainHopf hϖ N) rfl
      ((integralFunctions R K A).val.comp (chain R K A ϖ N).val)
      (Subtype.val_injective.comp Subtype.val_injective)
      (fun e => by
        obtain ⟨s, a, hs, hsa⟩ := exists_smul_eq_one_tmul K A e
        exact ⟨s, hs, ⟨incl R K A a, hS ⟨a, rfl⟩⟩, by rw [hsa]; exact (coe_incl (R := R) (K := K) a).symm⟩)
      (subPoint εB (chain R K A ϖ N)) (fun _ => rfl)
      (fun c => (algebraMap_point _ _).symm) htors
  have htop := eq_top_of_smooth (chain R K A ϖ N) hS hsmS
  have hfg := chain_fg (K := K) (A := A) hϖ N
  rw [htop] at hfg
  exact ⟨hfg⟩

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
