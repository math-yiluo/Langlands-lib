import Langlands.BaseChange.TwistedCharacter.BlockDegeneration
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Projection

/-! # Semisimple powers in semilinear conjugacy-orbit closures -/

noncomputable section

namespace Langlands.BaseChange

open Module Polynomial Set

variable {F E V : Type*} [NontriviallyNormedField F] [PerfectField F]
  [CommRing E] [Algebra F E] [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- Restrict an endomorphism of the coefficient module to the base field. -/
def restrictCoefficientEnd : End E V →ₐ[F] End F V where
  toFun a := a.restrictScalars F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- An endomorphism which is semilinear over the coefficient algebra, with a fixed
coefficient automorphism and the underlying module over the base field. -/
def IsCoefficientSemilinear (σ : E ≃ₐ[F] E) (T : End F V) : Prop :=
  ∀ (a : E) (v : V), T (a • v) = σ a • T v

omit [PerfectField F] [IsScalarTower F E V] in
theorem IsCoefficientSemilinear.pow {σ : E ≃ₐ[F] E} {T : End F V}
    (hT : IsCoefficientSemilinear σ T) (m : ℕ) : IsCoefficientSemilinear (σ ^ m) (T ^ m) := by
  intro a v
  induction m with
  | zero => rfl
  | succ m ihm =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ihm, hT]
    rfl

variable [FiniteDimensional F V] [IsSemisimpleModule E V]
  [TopologicalSpace (End F V)] [ContinuousAdd (End F V)] [ContinuousSMul F (End F V)]

omit [PerfectField F] [FiniteDimensional F V] in
private theorem exists_semisimple_power_of_nilpotent_bound
    (σ : E ≃ₐ[F] E) (l : ℕ) (hσ : σ ^ l = 1)
    (C : Set (End F V)) (hC : IsClosed C)
    (hconj : ∀ (g : (End E V)ˣ) (T : End F V), T ∈ C →
      restrictCoefficientEnd g.val * T * restrictCoefficientEnd (g⁻¹ : (End E V)ˣ).val ∈ C)
    (P Q : F[X]) (hQ : Squarefree Q) (r : ℕ) :
    ∀ T ∈ C, IsUnit T → IsCoefficientSemilinear σ T →
      (aeval (T ^ l) (X - P)) ^ (r + 1) = 0 → aeval (aeval (T ^ l) P) Q = 0 →
      ∃ S ∈ C, IsUnit S ∧ IsCoefficientSemilinear σ S ∧ Module.End.IsSemisimple (S ^ l) := by
  induction r with
  | zero =>
    intro T hTC hunit hT hN hS
    refine ⟨T, hTC, hunit, hT, Module.End.isSemisimple_of_squarefree_aeval_eq_zero hQ ?_⟩
    simp only [Nat.zero_add, pow_one, map_sub, aeval_X, sub_eq_zero] at hN
    exact hN.symm ▸ hS
  | succ r ih =>
    intro T hTC hTunit hT hN hS
    let j : End E V →ₐ[F] End F V := restrictCoefficientEnd
    have hTl := hT.pow l
    rw [hσ] at hTl
    let Tₗ : End E V :=
      { toFun := fun x => (T ^ l : End F V) x
        map_add' := map_add (T ^ l : End F V)
        map_smul' := fun a v => hTl a v }
    have hTl_eq : j Tₗ = T ^ l := rfl
    let Nₗ := aeval Tₗ (X - P)
    let N := aeval (T ^ l) (X - P)
    have hN_eq : j Nₗ = N := by rw [← aeval_algHom_apply, hTl_eq]
    have hNv (v : V) : N v = Nₗ v := congrArg (fun a : End F V => a v) hN_eq.symm
    let K := LinearMap.ker Nₗ
    obtain ⟨L, hKL⟩ := exists_isCompl K
    let p := K.projection L hKL
    let p₀ := j p
    let q₀ := 1 - p₀
    have hp := Submodule.isIdempotentElem_projection hKL
    have hpp (v : V) : p₀ v ∈ K := Submodule.projection_apply_mem hKL v
    have hpK {v : V} (hv : v ∈ K) : p₀ v = v := Submodule.projection_apply_of_mem_left hKL hv
    have hqK {v : V} (hv : v ∈ K) : q₀ v = 0 := by
      change v - p₀ v = 0
      rw [hpK hv, sub_self]
    have hcomm : Commute T N :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute
        (show N ∈ Algebra.adjoin F {T ^ l} by
          rw [Algebra.adjoin_singleton_eq_range_aeval]
          exact ⟨X - P, rfl⟩) ((Commute.refl T).pow_right l)
    have htri (A : End F V) (hA : Commute A N) : q₀ * A * p₀ = 0 := by
      apply LinearMap.ext
      intro v
      change q₀ (A (p₀ v)) = 0
      apply hqK
      change Nₗ (A (p₀ v)) = 0
      rw [← hNv]
      have h0 : N (p₀ v) = 0 := (hNv (p₀ v)).trans (LinearMap.mem_ker.mp (hpp v))
      rw [show N (A (p₀ v)) = A (N (p₀ v)) from
        LinearMap.congr_fun hA.eq.symm (p₀ v), h0, map_zero]
    let A := upperBlockAlgebra F p₀ (hp.map j)
    let f := diagonalBlockHom F p₀ (hp.map j)
    let a : A := ⟨T, htri T hcomm⟩
    let T' := f a
    have hT'C : T' ∈ C :=
      closure_minimal (range_subset_iff.mpr fun g => hconj g T hTC) hC
        (diagonalBlock_mem_closure_conjugates j p hp a)
    have hT'unit : IsUnit T' := by
      obtain ⟨u, hu⟩ := hTunit
      have hh : Commute u.val N := by rwa [hu]
      let u' : Aˣ :=
        ⟨a, ⟨(u⁻¹ : (End F V)ˣ).val, htri _ hh.units_inv_left⟩,
          Subtype.ext (by change T * (u⁻¹ : (End F V)ˣ).val = 1; rw [← hu]; exact u.val_inv),
          Subtype.ext (by change (u⁻¹ : (End F V)ˣ).val * T = 1; rw [← hu]; exact u.inv_val)⟩
      exact (Units.map f.toMonoidHom u').isUnit
    have hT'semi : IsCoefficientSemilinear σ T' := by
      intro e v
      have pq (b : E) (w : V) : p₀ (b • w) = b • p₀ w := p.map_smul b w
      have qq (b : E) (w : V) : q₀ (b • w) = b • q₀ w := by
        change b • w - p₀ (b • w) = b • (w - p₀ w)
        rw [pq, smul_sub]
      change p₀ (T (p₀ (e • v))) + q₀ (T (q₀ (e • v))) =
        σ e • (p₀ (T (p₀ v)) + q₀ (T (q₀ v)))
      rw [pq, qq, hT, hT, pq, qq, smul_add]
    let nn := aeval (a ^ l) (X - P)
    let ss := aeval (a ^ l) P
    have hcoe (p : F[X]) : (aeval (a ^ l) p : A).val = aeval (T ^ l) p := by
      change A.val (aeval (a ^ l) p) = _
      rw [← aeval_algHom_apply, map_pow]
      rfl
    have hmap (p : F[X]) : f (aeval (a ^ l) p) = aeval (T' ^ l) p := by
      rw [← aeval_algHom_apply, map_pow]
    have hnil' : (aeval (T' ^ l) (X - P)) ^ (r + 1) = 0 := by
      rw [← hmap, ← map_pow]
      apply LinearMap.ext
      intro v
      change p₀ ((A.val (nn ^ (r + 1))) (p₀ v)) + q₀ ((A.val (nn ^ (r + 1))) (q₀ v)) = 0
      rw [map_pow, show A.val nn = N from hcoe (X - P)]
      have hz : N (p₀ v) = 0 := (hNv _).trans (LinearMap.mem_ker.mp (hpp v))
      have hmem : (N ^ (r + 1)) (q₀ v) ∈ K := by
        change Nₗ ((N ^ (r + 1)) (q₀ v)) = 0
        rw [← hNv, ← Module.End.mul_apply, ← pow_succ' N (r + 1)]
        exact LinearMap.congr_fun hN _
      rw [hqK hmem, pow_succ N r, Module.End.mul_apply, hz, map_zero, map_zero, add_zero]
    have hann' : aeval (aeval (T' ^ l) P) Q = 0 := by
      rw [← hmap, aeval_algHom_apply]
      have hzero : aeval ss Q = 0 := by
        apply Subtype.ext
        change A.val (aeval ss Q) = 0
        rw [← aeval_algHom_apply, show A.val ss = aeval (T ^ l) P from hcoe P]
        exact hS
      rw [hzero, map_zero]
    exact ih T' hT'C hT'unit hT'semi hnil' hann'

/-- A closed set stable under conjugation by coefficient-linear units and containing an
invertible semilinear operator contains one with semisimple `l`th power, where the
coefficient automorphism has `l`th power the identity. -/
theorem exists_semisimple_power_in_closed_conjugacyInvariant
    (σ : E ≃ₐ[F] E) (l : ℕ) (hσ : σ ^ l = 1)
    (C : Set (End F V)) (hC : IsClosed C)
    (hconj : ∀ (g : (End E V)ˣ) (T : End F V), T ∈ C →
      restrictCoefficientEnd g.val * T * restrictCoefficientEnd (g⁻¹ : (End E V)ˣ).val ∈ C)
    {T : End F V} (hTC : T ∈ C) (hTunit : IsUnit T) (hT : IsCoefficientSemilinear σ T) :
    ∃ S ∈ C, IsUnit S ∧ IsCoefficientSemilinear σ S ∧ Module.End.IsSemisimple (S ^ l) := by
  obtain ⟨n, _, s, hs, hn, hss, hsum⟩ := (T ^ l).exists_isNilpotent_isSemisimple
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
  obtain ⟨P, hP⟩ := hs
  change aeval (T ^ l) P = s at hP
  let Q := minpoly F s
  have hN : aeval (T ^ l) (X - P) = n := by
    rw [map_sub, aeval_X, hP, hsum, add_sub_cancel_right]
  obtain ⟨r, hr⟩ := hn
  have hr' : (aeval (T ^ l) (X - P)) ^ (r + 1) = 0 := by
    rw [hN, pow_succ, hr, zero_mul]
  have hQ : aeval (aeval (T ^ l) P) Q = 0 := by rw [hP]; exact minpoly.aeval F s
  exact exists_semisimple_power_of_nilpotent_bound σ l hσ C hC hconj P Q
    hss.minpoly_squarefree r T hTC hTunit hT hr' hQ

/-- In characteristic zero a unit with a semisimple positive power is semisimple. -/
theorem isSemisimple_of_isUnit_of_pow {k W : Type*} [Field k] [CharZero k]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {T : End k W}
    (hT : IsUnit T) {l : ℕ} (hl : 0 < l) (hs : Module.End.IsSemisimple (T ^ l)) :
    Module.End.IsSemisimple T := by
  let p := minpoly k (T ^ l)
  let q := p.comp (X ^ l)
  have hp : p.Separable := PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have hp0 : p.coeff 0 ≠ 0 :=
    LinearMap.minpoly_coeff_zero_of_injective
      ((Module.End.isUnit_iff (T ^ l)).mp (hT.pow l)).injective
  have hq0 : q.coeff 0 ≠ 0 := by
    change (p.comp (X ^ l)).coeff 0 ≠ 0
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_pow, eval_X, zero_pow hl.ne',
      ← coeff_zero_eq_eval_zero]
    exact hp0
  have hx : IsCoprime q (X : k[X]) :=
    (irreducible_X.coprime_iff_not_dvd.mpr fun h => hq0 (X_dvd_iff.mp h)).symm
  have hc : IsCoprime q (C (l : k)) := by
    refine ⟨0, C ((l : k)⁻¹), ?_⟩
    rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hl.ne'), map_one]
  have hd : IsCoprime q (p.derivative.comp (X ^ l)) :=
    IsCoprime.map hp (compRingHom (X ^ l))
  have hsep : q.Separable := by
    rw [separable_def]
    change IsCoprime q (derivative (p.comp (X ^ l)))
    rw [derivative_comp, derivative_X_pow]
    exact (hc.mul_right (hx.pow_right (n := l - 1))).mul_right hd
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  change aeval T (p.comp (X ^ l)) = 0
  rw [aeval_comp, map_pow, aeval_X]
  exact minpoly.aeval k (T ^ l)

/-- Over a characteristic-zero base, a closed conjugation-invariant set containing an
invertible semilinear operator also contains an invertible semisimple one with the same
coefficient automorphism, provided the automorphism has finite order. -/
theorem exists_semisimple_in_closed_conjugacyInvariant [CharZero F]
    (σ : E ≃ₐ[F] E) (l : ℕ) (hl : 0 < l) (hσ : σ ^ l = 1)
    (C : Set (End F V)) (hC : IsClosed C)
    (hconj : ∀ (g : (End E V)ˣ) (T : End F V), T ∈ C →
      restrictCoefficientEnd g.val * T * restrictCoefficientEnd (g⁻¹ : (End E V)ˣ).val ∈ C)
    {T : End F V} (hTC : T ∈ C) (hTunit : IsUnit T) (hT : IsCoefficientSemilinear σ T) :
    ∃ S ∈ C, IsUnit S ∧ IsCoefficientSemilinear σ S ∧ Module.End.IsSemisimple S := by
  obtain ⟨S, hSC, hSunit, hS, hSsem⟩ :=
    exists_semisimple_power_in_closed_conjugacyInvariant σ l hσ C hC hconj hTC hTunit hT
  exact ⟨S, hSC, hSunit, hS, isSemisimple_of_isUnit_of_pow hSunit hl hSsem⟩

end Langlands.BaseChange
