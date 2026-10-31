import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Langlands.Representation.Whittaker.EntrywiseCharacter

/-!
# The top derivative surjects onto the standard upper-unipotent coinvariants

For a smooth representation `A` of `GL_N(F)`, `0 < N`, and a continuous nontrivial unitary
additive character `ψ`, the actual top derivative
`(generalLinearDerivative T ψ N N _).obj A = Ψ⁻ (Φ⁻)^(N-1) (A|P_N)` is an iterated
quotient of `A`. The quotient map from `A` onto the actual character-localized coinvariants
`A_(U_N, θ_ψ)`, with `θ_ψ(u) = ψ(∑ u_(i,i+1))`, factors through it. Hence finite
dimensionality of the top derivative implies finite dimensionality of `A_(U_N, θ_ψ)`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Whittaker.TopDerivativeComparison

open GeneralLinear HarmonicAnalysis Derivative Derivative.Mirabolic
open GeneralLinear.Mirabolic (radical successor radicalToUpperUnipotent rankOne_eq_one)
open Classification.SupercuspidalDerivativeVanishing (iterateQuotient)
open UpperUnipotentCharacter (successorUnipotent successorUnipotent_first
  successorUnipotent_last)

universe uF uV uW

/-! ## The entrywise character on radicals and successors -/

section Characters

variable {K : Type uF} [Field K] [TopologicalSpace K]

/-- On radical columns the entrywise character is the mirabolic character `θ_ψ`. -/
theorem entrywiseCharacter_radical (ψ : UnitaryAdditiveCharacter K) (n : ℕ)
    (r : radical (n + 1) K) :
    (entrywiseCharacter ψ.complex (n + 2) (radicalToUpperUnipotent r) : ℂ) =
      (theta ψ n r : ℂ) := by
  rw [entrywiseCharacter_apply_sum, theta_apply, ← superdiagonalSum_radical n r]
  rfl

omit [TopologicalSpace K] in
/-- The successor embedding preserves the entrywise character. -/
theorem entrywiseCharacter_successor (ψ : AddChar K ℂ) (n : ℕ)
    (u : upperUnipotent (n + 1) K) :
    (entrywiseCharacter ψ (n + 2) (successorUnipotent n u) : ℂ) =
      (entrywiseCharacter ψ (n + 1) u : ℂ) := by
  rw [entrywiseCharacter_apply_sum, entrywiseCharacter_apply_sum, Fin.sum_univ_castSucc]
  congr 1
  rw [Fin.succ_last, successorUnipotent_last, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.succ_castSucc, successorUnipotent_first]

end Characters

/-- The determinant normalization of `Φ⁻` is trivial on upper unipotent matrices. -/
theorem phiMinusCharacter_eq_one_of_upper {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (g : mirabolic n F.Carrier)
    (hg : g.val ∈ upperUnipotent (n + 1) F.Carrier) :
    realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
      (-(1 / 2 : ℝ)) g = 1 := by
  have hdet : GeneralLinear.determinant g.val = 1 := by
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i])
  have hnorm : (T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype g = 1 := by
    change T.normalizedAbsUnits (GeneralLinear.determinant g.val) = 1
    rw [hdet, map_one]
  unfold realPowerCharacter
  rw [MonoidHom.comp_apply, hnorm, map_one]

/-! ## Descent through the iterated quotient -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- A linear map out of a representation of `P_(j+1)` which transforms under `U_(j+1)` by
the entrywise character factors through the top mirabolic derivative `Ψ⁻ (Φ⁻)^j`. -/
theorem descend (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] :
    ∀ (j : ℕ), letI := T.topology
      ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (0 + j) F.Carrier)) (f : X →ₗ[ℂ] W),
        (∀ (u : upperUnipotent (0 + j + 1) F.Carrier) (v : X),
          f (X.representation ⟨u.val, upperUnipotent_le_mirabolic u.property⟩ v) =
            (entrywiseCharacter ψ.complex (0 + j + 1) u : ℂ) • f v) →
        ∃ f' : (psiMinus T 0).obj ((phiMinusIterate T ψ 0 j).obj X) →ₗ[ℂ] W,
          f' ∘ₗ (psiMinusQuotient T 0 ((phiMinusIterate T ψ 0 j).obj X) ∘ₗ
            iterateQuotient T ψ 0 j X) = f
  | 0 => fun X f _ => by
      let _ := T.topology
      have h0 : ∀ (r : radical 0 F.Carrier) (v : X),
          f (X.representation (r : mirabolic 0 F.Carrier) v) =
            (((1 : radical 0 F.Carrier →* ℂˣ) r : ℂˣ) : ℂ) • f v := by
        intro r v
        rw [rankOne_eq_one (r : mirabolic 0 F.Carrier), map_one, Module.End.one_apply,
          MonoidHom.one_apply, Units.val_one, one_smul]
      refine ⟨Jacquet.Localization.lift X.representation (radical 0 F.Carrier) 1 f h0, ?_⟩
      apply LinearMap.ext
      intro v
      rfl
  | j + 1 => fun X f hf => by
      let _ := T.topology
      have h1 : ∀ (r : radical (0 + j + 1) F.Carrier) (v : X),
          f (X.representation (r : mirabolic (0 + j + 1) F.Carrier) v) =
            (T.mirabolicTheta ψ (0 + j) r : ℂ) • f v := by
        intro r v
        have hv := hf (radicalToUpperUnipotent r) v
        have hc : (entrywiseCharacter ψ.complex (0 + (j + 1) + 1)
            (radicalToUpperUnipotent r) : ℂ) = (T.mirabolicTheta ψ (0 + j) r : ℂ) :=
          entrywiseCharacter_radical ψ (0 + j) r
        rw [hc] at hv
        exact hv
      let f₁ := Jacquet.Localization.lift X.representation (radical (0 + j + 1) F.Carrier)
        (T.mirabolicTheta ψ (0 + j)) f h1
      have hf₁ : ∀ (u : upperUnipotent (0 + j + 1) F.Carrier)
          (w : (phiMinus T ψ (0 + j)).obj X),
          f₁ (((phiMinus T ψ (0 + j)).obj X).representation
              ⟨u.val, upperUnipotent_le_mirabolic u.property⟩ w) =
            (entrywiseCharacter ψ.complex (0 + j + 1) u : ℂ) • f₁ w := by
        intro u w
        obtain ⟨v, rfl⟩ := phiMinusQuotient_surjective T ψ (0 + j) X w
        rw [phiMinus_action, phiMinusCharacter_eq_one_of_upper T _ u.property, Units.val_one,
          one_smul]
        change f (X.representation (successor
            (⟨u.val, upperUnipotent_le_mirabolic u.property⟩ : mirabolic (0 + j) F.Carrier)) v) =
          (entrywiseCharacter ψ.complex (0 + j + 1) u : ℂ) • f v
        have hv := hf (successorUnipotent (0 + j) u) v
        have hc : (entrywiseCharacter ψ.complex (0 + (j + 1) + 1)
            (successorUnipotent (0 + j) u) : ℂ) =
            (entrywiseCharacter ψ.complex (0 + j + 1) u : ℂ) :=
          entrywiseCharacter_successor ψ.complex (0 + j) u
        rw [hc] at hv
        exact hv
      obtain ⟨f', hf'⟩ := descend T ψ W j ((phiMinus T ψ (0 + j)).obj X) f₁ hf₁
      refine ⟨f', ?_⟩
      apply LinearMap.ext
      intro v
      have h := LinearMap.congr_fun hf' (phiMinusQuotient T ψ (0 + j) X v)
      exact h

/-! ## Finite top derivatives give finite coinvariants -/

/-- For `B` on `GL_(0+n+1)`, the coinvariants `B_(U, θ_ψ)` are a quotient of the positive
derivative of order `n + 1`; finite dimensionality passes to them. -/
theorem finite_coinvariants_of_derivativePositive (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      FiniteDimensional ℂ ((generalLinearDerivativePositive T ψ 0 n).obj B) →
        FiniteDimensional ℂ (Jacquet.Localization.Coinvariants B.representation
          (upperUnipotent (0 + n + 1) F.Carrier) (entrywiseCharacter ψ.complex (0 + n + 1))) := by
  let _ := T.topology
  intro B hB
  let X := (generalLinearRestriction T (0 + n)).obj B
  let q := Jacquet.Localization.mk B.representation (upperUnipotent (0 + n + 1) F.Carrier)
    (entrywiseCharacter ψ.complex (0 + n + 1))
  obtain ⟨f', hf'⟩ := descend T ψ _ n X q (by
    intro u v
    exact Jacquet.Localization.mk_apply_subgroup B.representation _ _ u v)
  have hsurj : Function.Surjective f' := by
    intro x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ x
    exact ⟨_, LinearMap.congr_fun hf' v⟩
  have : Module.Finite ℂ ((psiMinus T 0).obj ((phiMinusIterate T ψ 0 n).obj X)) := hB
  exact Module.Finite.of_surjective f' hsurj

private theorem finite_coinvariants_of_cast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N m n : ℕ) (hm : m = 0)
    (h : N = m + n + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      FiniteDimensional ℂ
          ((generalLinearRankCast T h ⋙ generalLinearDerivativePositive T ψ m n).obj A) →
        FiniteDimensional ℂ (Jacquet.Localization.Coinvariants A.representation
          (upperUnipotent N F.Carrier) (entrywiseCharacter ψ.complex N)) := by
  subst hm
  subst h
  exact finite_coinvariants_of_derivativePositive T ψ n

/-- If the actual top derivative of `A` on `GL_N`, `0 < N`, is finite dimensional, so is
the actual quotient of `A` by the span of `A(u)v - θ_ψ(u) v`, `u ∈ U_N`. -/
theorem finite_coinvariants_of_topDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N : ℕ) (hk : N ≤ N)
    (hpos : 0 < N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      FiniteDimensional ℂ ((generalLinearDerivative T ψ N N hk).obj A) →
        FiniteDimensional ℂ (Jacquet.Localization.Coinvariants A.representation
          (upperUnipotent N F.Carrier) (entrywiseCharacter ψ.complex N)) := by
  let _ := T.topology
  intro A hA
  rw [generalLinearDerivative_of_pos T ψ N N hk hpos] at hA
  exact finite_coinvariants_of_cast T ψ N (N - N) (N - 1) (Nat.sub_self N)
    (rank_eq_of_pos_le hk hpos) A hA

end Langlands.Whittaker.TopDerivativeComparison
