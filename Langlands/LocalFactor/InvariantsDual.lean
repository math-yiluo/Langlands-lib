import Langlands.Weil.Representation.Invariants
import Langlands.Weil.Representation.Dual
import Langlands.Weil.Local.ContinuityProof
import Langlands.LocalFactor.Euler
import Mathlib.LinearAlgebra.Determinant

/-! # Duals of finite-inertia invariant spaces -/

noncomputable section

universe uK uG uV uF

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]
  (I : Subgroup G) [I.Normal] (A : FiniteRepresentation.{uK, uG, uV} K G)

/-- Restrict an inertia-invariant functional to the inertia-fixed subspace. -/
def invariantsDualRestriction :
    (invariants I (dual A)).representation.IntertwiningMap
      (dual (invariants I A)).representation where
  toLinearMap :=
    { toFun := fun ℓ => ℓ.val.comp (invariantSubspace A I).subtype
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    ext ℓ
    rfl

/-- Finite inertia image makes restriction of invariant functionals bijective. -/
theorem invariantsDualRestriction_bijective [CharZero K]
    (hfinite : (Set.range (A.representation.comp I.subtype)).Finite) :
    Function.Bijective (invariantsDualRestriction I A) := by
  classical
  change Function.Bijective
    (fun ℓ : Representation.invariants (A.representation.dual.comp I.subtype) =>
      ℓ.val.comp (invariantSubspace A I).subtype)
  let ρ := A.representation.comp I.subtype
  let Q := I ⧸ ρ.ker
  let τ : Representation K Q A := QuotientGroup.lift ρ.ker ρ le_rfl
  have hr (q : Q) : τ q ∈ Set.range ρ := by
    induction q using QuotientGroup.induction_on with
    | H i => exact ⟨i, rfl⟩
  let := hfinite.to_subtype
  let : Finite Q := Finite.of_injective
    (fun q : Q => (⟨τ q, hr q⟩ : Set.range ρ)) (by
      intro a b h
      exact (QuotientGroup.injective_lift_iff ρ.ker ρ le_rfl).mpr rfl
        (congrArg Subtype.val h))
  let : Fintype Q := Fintype.ofFinite Q
  let : Invertible (Fintype.card Q : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hq (v : A) : v ∈ τ.invariants ↔ v ∈ invariantSubspace A I := by
    constructor
    · intro h i
      exact h (QuotientGroup.mk i)
    · intro h q
      induction q using QuotientGroup.induction_on with
      | H i => exact h i
  let P : A →ₗ[K] invariantSubspace A I :=
    τ.averageMap.codRestrict _ fun v =>
      (hq (τ.averageMap v)).mp (τ.averageMap_invariant v)
  have hP (i : I) (v : A) : P (ρ i v) = P v := by
    apply Subtype.ext
    change τ.averageMap (τ (QuotientGroup.mk i) v) = τ.averageMap v
    rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
      ← Module.End.mul_apply, ← map_mul, GroupAlgebra.mul_average_right]
  have hℓ (ℓ : Representation.invariants (A.representation.dual.comp I.subtype))
      (i : I) (v : A) : ℓ.val (ρ i v) = ℓ.val v := by
    change ℓ.val (A.representation (i : G) v) = ℓ.val v
    have h := congrArg (fun L : Module.Dual K A => L v) (ℓ.property i⁻¹)
    change ℓ.val (A.representation ((i⁻¹ : I) : G)⁻¹ v) = ℓ.val v at h
    simpa only [Subgroup.coe_inv, inv_inv] using h
  have havg (ℓ : Representation.invariants (A.representation.dual.comp I.subtype))
      (v : A) : ℓ.val (τ.averageMap v) = ℓ.val v := by
    have ht (q : Q) : ℓ.val (τ q v) = ℓ.val v := by
      induction q using QuotientGroup.induction_on with
      | H i => exact hℓ ℓ i v
    simp [Representation.averageMap, GroupAlgebra.average, map_sum, ht,
      ← Nat.cast_smul_eq_nsmul K]
  constructor
  · intro ℓ ℓ' heq
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rw [← havg ℓ v, ← havg ℓ' v]
    exact congrArg (fun L : Module.Dual K (invariants I A) => L (P v)) heq
  · intro L
    let ℓ : Module.Dual K A := L.comp P
    have hfix : ℓ ∈ invariantSubspace (dual A) I := by
      intro i
      apply LinearMap.ext
      intro v
      change L (P (ρ i⁻¹ v)) = L (P v)
      exact congrArg L (hP i⁻¹ v)
    refine ⟨⟨ℓ, hfix⟩, ?_⟩
    apply LinearMap.ext
    intro x
    change L (P x.val) = L x
    congr 1
    apply Subtype.ext
    exact τ.averageMap_id x.val ((hq x.val).mpr x.property)

/-- The canonical representation equivalence is restriction of functionals. -/
def invariantsDualEquiv [CharZero K]
    (hfinite : (Set.range (A.representation.comp I.subtype)).Finite) :
    Equiv (invariants I (dual A)) (dual (invariants I A)) where
  toLinearEquiv := LinearEquiv.ofBijective
    (invariantsDualRestriction I A).toLinearMap
    (invariantsDualRestriction_bijective I A hfinite)
  isIntertwining' := (invariantsDualRestriction I A).isIntertwining'

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor

variable {K : Type uK} {G : Type uG} [Field K] [CharZero K] [Group G]
  (I : Subgroup G) [I.Normal] (A : FiniteRepresentation.{uK, uG, uV} K G)

/-- The Frobenius operator on the dual fixed space is conjugate to the
transpose of the inverse operator on the original fixed space. -/
theorem eulerPolynomial_invariants_dual
    (hfinite : (Set.range (A.representation.comp I.subtype)).Finite) (g : G) :
    eulerPolynomial ((FiniteRepresentation.invariants I
      (FiniteRepresentation.dual A)).representation g) =
      eulerPolynomial (((FiniteRepresentation.invariants I A).representation g⁻¹).dualMap) := by
  have h := eulerPolynomial_conj
    (FiniteRepresentation.invariantsDualEquiv I A hfinite).toLinearEquiv
    ((FiniteRepresentation.invariants I (FiniteRepresentation.dual A)).representation g)
  rw [Representation.Equiv.conj_apply_self] at h
  exact h.symm

/-- Evaluation of the dual-invariant Euler polynomial is the determinant of
one minus the inverse Frobenius operator on the original invariant space. -/
theorem eulerPolynomial_invariants_dual_eval
    (hfinite : (Set.range (A.representation.comp I.subtype)).Finite) (g : G) (z : K) :
    (eulerPolynomial ((FiniteRepresentation.invariants I
      (FiniteRepresentation.dual A)).representation g)).eval z =
      LinearMap.det (1 - z •
        (FiniteRepresentation.invariants I A).representation g⁻¹) := by
  rw [eulerPolynomial_invariants_dual I A hfinite g, eulerPolynomial_eval]
  convert LinearMap.det_dualMap
    (1 - z • (FiniteRepresentation.invariants I A).representation g⁻¹) using 1
  congr 1
  ext ℓ v
  simp

end Langlands.LocalFactor

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (A : LocalWeilRepresentation.{uF, uV} F)

/-- Continuity supplies the finite-inertia premise of the canonical dual
invariant-space equivalence for the actual local Weil group. -/
def continuousInvariantsDualEquiv (hA : A.IsContinuous) :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.invariants (localInertia F) (FiniteRepresentation.dual A))
      (FiniteRepresentation.dual (FiniteRepresentation.invariants (localInertia F) A)) :=
  FiniteRepresentation.invariantsDualEquiv (localInertia F) A
    ((localWeilContinuity F A).2.2.2.2.mp
      ((localWeilContinuity F A).2.2.1.mp hA)).1

end Langlands.Weil.Local
