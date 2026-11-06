import Langlands.FieldTheory.HenselianIntegerAddValuation
import Mathlib.FieldTheory.IsSepClosed

/-! # Functorial normalized integer valuations on separable extensions -/

noncomputable section

universe u v w

namespace Langlands.FieldTheory

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)

section Galois

variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Conjugate algebraic elements have the same normalized additive value. -/
theorem henselianIntegerAddValuation_eq_of_minpoly_eq {x y : Ω}
    (hxy : minpoly K x = minpoly K y) :
    henselianIntegerAddValuation v hH Ω x = henselianIntegerAddValuation v hH Ω y := by
  have hr : Polynomial.aeval x (minpoly K y) = 0 := by
    rw [← hxy]
    exact minpoly.aeval K x
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root
    (Algebra.IsAlgebraic.isAlgebraic (R := K) y) hr
  rw [← hσ, henselianIntegerAddValuation_invariant]

end Galois

variable (L : Type v) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

omit [Algebra.IsSeparable K L] in
/-- All embeddings into the fixed separable closure give the same value. -/
theorem henselianIntegerAddValuation_embeddings_eq
    (f g : L →ₐ[K] SeparableClosure K) (x : L) :
    henselianIntegerAddValuation v hH (SeparableClosure K) (f x) =
      henselianIntegerAddValuation v hH (SeparableClosure K) (g x) := by
  apply henselianIntegerAddValuation_eq_of_minpoly_eq
  rw [minpoly.algHom_eq f f.injective, minpoly.algHom_eq g g.injective]

/-- A normalized additive valuation on any separable extension of the base field. -/
def henselianSeparableAddValuation : AddValuation L (WithTop ℝ) :=
  (henselianIntegerAddValuation v hH (SeparableClosure K)).comap
    (IsSepClosed.lift : L →ₐ[K] SeparableClosure K).toRingHom

/-- The construction can be computed using any embedding into the separable closure. -/
theorem henselianSeparableAddValuation_apply
    (f : L →ₐ[K] SeparableClosure K) (x : L) :
    henselianSeparableAddValuation v hH L x =
      henselianIntegerAddValuation v hH (SeparableClosure K) (f x) :=
  henselianIntegerAddValuation_embeddings_eq v hH L _ f x

variable {L} (M : Type w) [Field M] [Algebra K M] [Algebra.IsSeparable K M]

/-- Every algebra embedding over the henselian base preserves the normalized value. -/
theorem henselianSeparableAddValuation_algHom (f : L →ₐ[K] M) (x : L) :
    henselianSeparableAddValuation v hH M (f x) =
      henselianSeparableAddValuation v hH L x := by
  let g : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [henselianSeparableAddValuation_apply v hH M g,
    henselianSeparableAddValuation_apply v hH L (g.comp f)]
  rfl

variable (L)

/-- In particular every base-field algebra automorphism preserves the value. -/
theorem henselianSeparableAddValuation_invariant (σ : L ≃ₐ[K] L) (x : L) :
    henselianSeparableAddValuation v hH L (σ x) =
      henselianSeparableAddValuation v hH L x :=
  henselianSeparableAddValuation_algHom v hH L σ.toAlgHom x

/-- Exact normalization on nonzero embedded base elements. -/
theorem henselianSeparableAddValuation_base {x : K} (hx : x ≠ 0) :
    henselianSeparableAddValuation v hH L (algebraMap K L x) =
      (((-WithZero.log (v x) : ℤ) : ℝ) : WithTop ℝ) := by
  let f : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  rw [henselianSeparableAddValuation_apply v hH L f, f.commutes]
  exact henselianIntegerAddValuation_base v hH (SeparableClosure K) hx

open IntermediateField

set_option maxHeartbeats 800000 in
/-- The actual field norm calibrates values by the degree even without normality. -/
theorem henselianSeparableAddValuation_norm [FiniteDimensional K L] (x : L) :
    henselianSeparableAddValuation v hH L (algebraMap K L (Algebra.norm K x)) =
      Module.finrank K L • henselianSeparableAddValuation v hH L x := by
  classical
  let Ω := SeparableClosure K
  let f : L →ₐ[K] Ω := IsSepClosed.lift
  let w := henselianIntegerAddValuation v hH Ω
  have hx := Algebra.IsSeparable.isIntegral K x
  have hs : ((minpoly K x).map (algebraMap K Ω)).Splits :=
    IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)
  have hval : ∀ y ∈ (minpoly K x).aroots Ω, w y = w (f x) := by
    intro y hy
    apply henselianIntegerAddValuation_eq_of_minpoly_eq
    apply minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic (R := K) (f x))
    rw [minpoly.algHom_eq f f.injective]
    exact (Polynomial.mem_aroots.mp hy).2
  have hprod : ∀ s : Multiset Ω, (∀ y ∈ s, w y = w (f x)) →
      w s.prod = s.card • w (f x) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | @cons y s ih =>
        intro h
        rw [Multiset.prod_cons, AddValuation.map_mul, h y (by simp),
          ih (fun z hz => h z (by simp [hz])), Multiset.card_cons]
        simp [add_nsmul, add_comm]
  have hcard : ((minpoly K x).aroots Ω).card = Module.finrank K K⟮x⟯ := by
    rw [Polynomial.aroots_def, ← hs.natDegree_eq_card_roots,
      Polynomial.natDegree_map, adjoin.finrank hx]
  rw [henselianSeparableAddValuation_apply v hH L f,
    henselianSeparableAddValuation_apply v hH L f, f.commutes,
    Algebra.norm_eq_prod_roots Ω hs, AddValuation.map_pow, hprod _ hval, hcard,
    smul_smul, Nat.mul_comm, Module.finrank_mul_finrank]

/-- Nonzero values lie in the inverse-degree integer lattice. -/
theorem henselianSeparableAddValuation_exists_lattice_value [FiniteDimensional K L]
    {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, henselianSeparableAddValuation v hH L x =
      ((n : ℝ) / Module.finrank K L : ℝ) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    ((henselianSeparableAddValuation v hH L).ne_top_iff.mpr hx)
  have hn := henselianSeparableAddValuation_norm v hH L x
  rw [henselianSeparableAddValuation_base v hH L
    (Algebra.norm_ne_zero_iff.mpr hx), ← hr, ← WithTop.coe_nsmul, WithTop.coe_inj,
    nsmul_eq_mul] at hn
  refine ⟨-WithZero.log (v (Algebra.norm K x)), ?_⟩
  rw [← hr]
  congr 1
  exact (eq_div_iff (Nat.cast_ne_zero.mpr
    (ne_of_gt (Module.finrank_pos (R := K) (M := L))))).mpr
      (by simpa only [mul_comm] using hn.symm)

end Langlands.FieldTheory
