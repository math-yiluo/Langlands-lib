import Langlands.CommutativeAlgebra.SmoothEtaleCompletionApproximationStatement
import Langlands.CommutativeAlgebra.PointedEtaleLocalSections
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Smooth.AdicCompletion

/-! # Finite-order etale specialization of a smooth algebra -/

universe u

open scoped TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.SmoothEtaleCompletion

open Algebra

/-- Polynomial parameters can be specialized in the base while preserving a
specified point over any quotient of the base. -/
theorem exists_etale_factor_of_polynomial_quotient {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Etale (MvPolynomial (Fin n) R) S]
    (I : Ideal R) (φ : S →ₐ[R] R ⧸ I) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), Etale R E ∧
      ∃ (ψ : S →ₐ[R] E) (ρ : E →ₐ[R] R ⧸ I), ρ.comp ψ = φ := by
  classical
  let Q := MvPolynomial (Fin n) R
  let c : Fin n → R ⧸ I := fun i => φ (algebraMap Q S (MvPolynomial.X i))
  choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)
  let θ : Q →ₐ[R] R := MvPolynomial.aeval a
  let : Algebra Q R := θ.toRingHom.toAlgebra
  have : IsScalarTower R Q R := .of_algebraMap_eq fun r => (θ.commutes r).symm
  have hθ : (Ideal.Quotient.mk I).comp θ.toRingHom =
      φ.toRingHom.comp (algebraMap Q S) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Ideal.Quotient.mk I (θ (MvPolynomial.C r)) =
        φ (algebraMap Q S (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, θ.commutes,
        ← IsScalarTower.algebraMap_apply R Q S, φ.commutes]
      rfl
    · intro i
      change Ideal.Quotient.mk I (θ (MvPolynomial.X i)) = c i
      dsimp only [θ]
      rw [MvPolynomial.aeval_X]
      exact ha i
  let βQ : R →ₐ[Q] R ⧸ I := Ideal.Quotient.mkₐ Q I
  let φQ : S →ₐ[Q] R ⧸ I :=
    ⟨φ.toRingHom, fun q => (congrArg (fun h : Q →+* R ⧸ I => h q) hθ).symm⟩
  let E := R ⊗[Q] S
  let ψ : S →ₐ[R] E :=
    (Algebra.TensorProduct.includeRight (R := Q) (A := R)).restrictScalars R
  let ρ : E →ₐ[R] R ⧸ I :=
    (Algebra.TensorProduct.lift βQ φQ (fun _ _ => Commute.all _ _)).restrictScalars R
  refine ⟨E, inferInstance, inferInstance, inferInstance, ψ, ρ, ?_⟩
  ext x
  change Algebra.TensorProduct.lift βQ φQ (fun _ _ => Commute.all _ _)
    (1 ⊗ₜ[Q] x) = φ x
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- The kernel of reduction from a positive ideal power is nilpotent. -/
theorem isNilpotent_ker_factor_pow {R : Type u} [CommRing R]
    (I : Ideal R) {N : ℕ} (hN : N ≠ 0) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hN : I ^ N ≤ I))) := by
  rw [Ideal.Quotient.factor_ker]
  exact ⟨N, by simp [← Ideal.map_pow]⟩

/-- Reduction of an element of a completion is compatible with its residue. -/
theorem factor_evalₐ {R : Type u} [CommRing R] (I : Ideal R) {N : ℕ}
    (hN : N ≠ 0) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_self hN : I ^ N ≤ I)
      (AdicCompletion.evalₐ I N x) = AdicCompletion.evalOneₐ I x := by
  induction x using AdicCompletion.induction_on I R with
  | _ a =>
    simp only [AdicCompletion.evalₐ_mk, AdicCompletion.evalOneₐ,
      AlgHom.comp_apply, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
    simpa only [Ideal.Quotient.factor_mk] using
      congrArg (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp))
        (AdicCompletion.Ideal.mk_eq_mk (I := I) (Nat.one_le_iff_ne_zero.mpr hN) a)

/-- A quotient-valued point of an etale algebra lifts to the completion with
its entire specified finite-order value preserved. -/
theorem exists_lift_quotient {R E : Type u} [CommRing R] [CommRing E]
    [Algebra R E] [Etale R E] (I : Ideal R) {N : ℕ} (hN : N ≠ 0)
    (ρ : E →ₐ[R] R ⧸ I ^ N) :
    ∃ (ι : E →ₐ[R] AdicCompletion I R), (AdicCompletion.evalₐ I N).comp ι = ρ := by
  let π : R ⧸ I ^ N →ₐ[R] R ⧸ I :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_self hN)
  obtain ⟨ι, hι⟩ :=
    Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq (π.comp ρ)
  refine ⟨ι, Algebra.FormallyUnramified.lift_unique_of_ringHom π.toRingHom
    (isNilpotent_ker_factor_pow I hN) _ _ ?_⟩
  ext x
  change Ideal.Quotient.factor (Ideal.pow_le_self hN)
    (AdicCompletion.evalₐ I N (ι x)) = π (ρ x)
  rw [factor_evalₐ I hN]
  exact AlgHom.congr_fun hι x

/-- Finite-order etale specialization of a smooth algebra at positive order. -/
theorem exists_etale_approximation_of_smooth_pos {R B : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Smooth R B]
    (f : B →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R)
    {N : ℕ} (hN : N ≠ 0) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E), Etale R E ∧
      ∃ (g : B →ₐ[R] E)
        (ι : E →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R),
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N).comp (ι.comp g) =
          (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N).comp f := by
  let I := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let φ : B →ₐ[R] R ⧸ I := (AdicCompletion.evalOneₐ I).comp f
  let p : Ideal B := RingHom.ker φ.toRingHom
  have : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨b, hb, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let Bg := Localization.Away b
  let : IsLocalHom (AdicCompletion.evalOneₐ I).toRingHom :=
    IsLocalHom.of_surjective _ (AdicCompletion.evalOneₐ_surjective I)
  have hbu : IsUnit (f b) := by
    apply isUnit_of_map_unit (AdicCompletion.evalOneₐ I).toRingHom
    apply isUnit_iff_ne_zero.mpr
    exact hb
  let fgRing : Bg →+* AdicCompletion I R := IsLocalization.Away.lift b hbu
  have hfg : fgRing.comp (algebraMap B Bg) = f.toRingHom :=
    IsLocalization.lift_comp _
  let fg : Bg →ₐ[R] AdicCompletion I R :=
    ⟨fgRing, fun r => by
      rw [IsScalarTower.algebraMap_apply R B Bg]
      change (fgRing.comp (algebraMap B Bg)) (algebraMap R B r) = _
      rw [hfg]
      exact f.commutes r⟩
  obtain ⟨E, _, _, hE, ψ, ρ, hρ⟩ :=
    exists_etale_factor_of_polynomial_quotient (n := n) (I ^ N)
      ((AdicCompletion.evalₐ I N).comp fg)
  let : Etale R E := hE
  obtain ⟨ι, hι⟩ := exists_lift_quotient I hN ρ
  refine ⟨E, inferInstance, inferInstance, hE,
    ψ.comp (IsScalarTower.toAlgHom R B Bg), ι, ?_⟩
  ext x
  have h₁ := AlgHom.congr_fun hι (ψ (algebraMap B Bg x))
  have h₂ := AlgHom.congr_fun hρ (algebraMap B Bg x)
  have h₃ := RingHom.congr_fun hfg x
  exact h₁.trans (h₂.trans (congrArg (AdicCompletion.evalₐ I N) h₃))

end Langlands.CommutativeAlgebra.SmoothEtaleCompletion

namespace Langlands.CommutativeAlgebra

/-- A smooth algebra admits finite-order etale approximation in the completion. -/
theorem smoothEtaleCompletionApproximation :
    SmoothEtaleCompletionApproximationStatement.{u} := by
  intro R _ _ _ B _ _ _ f N
  by_cases hN : N = 0
  · obtain ⟨E, _, _, hE, g, ι, _⟩ :=
      SmoothEtaleCompletion.exists_etale_approximation_of_smooth_pos f
        (N := 1) one_ne_zero
    refine ⟨E, inferInstance, inferInstance, hE, g, ι, ?_⟩
    subst N
    have : Subsingleton (R ⧸ IsLocalRing.maximalIdeal R ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Subsingleton.elim _ _
  · exact SmoothEtaleCompletion.exists_etale_approximation_of_smooth_pos f hN

end Langlands.CommutativeAlgebra
