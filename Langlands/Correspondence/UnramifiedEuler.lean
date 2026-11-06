import Langlands.Correspondence.UnramifiedNormalization
import Langlands.LocalFactor.UnramifiedDegree
import Langlands.LocalFactor.WeilDeligne

/-!
# Euler polynomials and unramified parameter classes

The actual invariant-kernel Euler polynomial descends to pair classes. Its
maximal-degree criterion agrees with the correspondence's unramified predicate.
-/

noncomputable section

universe uK uG uV uF uP

namespace Langlands.LocalFactor.WeilDeligne

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}

/-- The invariant-kernel Euler polynomial on genuine pair-isomorphism classes. -/
def eulerPolynomialClass (I : Subgroup G) [I.Normal] (Φ : G) :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → Polynomial K :=
  Quotient.lift (fun A => eulerPolynomial A I Φ)
    (fun _ _ ⟨e⟩ => eulerPolynomial_eq_of_equiv I e Φ)

@[simp]
theorem eulerPolynomialClass_classOf
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (Φ : G) :
    eulerPolynomialClass I Φ (WeilDeligneRepresentation.classOf A) =
      eulerPolynomial A I Φ := rfl

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.Correspondence

open Weil.Local WeilDeligneRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The standard arithmetic Euler denominator of an actual parameter class,
using the published geometric Frobenius lift. -/
def parameterEulerPolynomial {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    Polynomial ℂ :=
  LocalFactor.WeilDeligne.eulerPolynomialClass (localInertia F)
    (localGeometricFrobenius F) (parameterForget F D)

/-- Maximal standard Euler degree is precisely the existing class-level
unramified condition. No continuity or additional normalization is assumed. -/
theorem parameterEulerPolynomial_natDegree_eq_rank_iff {n : ℕ+}
    (D : WeilDeligneClass.{uF, uP} F n) :
    (parameterEulerPolynomial F D).natDegree = (n : ℕ) ↔
      IsUnramifiedParameterClass F D := by
  let A := Quotient.out (parameterForget F D)
  have hA : classOf A = parameterForget F D := Quotient.out_eq _
  have hr : A.rank = (n : ℕ) := by
    change classRank (classOf A) = (n : ℕ)
    rw [hA]
    exact D.property
  constructor
  · intro hdeg
    have hdegA :
        (LocalFactor.WeilDeligne.eulerPolynomial A (localInertia F)
          (localGeometricFrobenius F)).natDegree = A.rank := by
      simpa only [parameterEulerPolynomial, ← hA,
        LocalFactor.WeilDeligne.eulerPolynomialClass_classOf, hr] using hdeg
    have hpair := (LocalFactor.wdEulerPolynomial_natDegree_eq_rank_iff
      (localInertia F) A (localGeometricFrobenius F)).mp hdegA
    refine ⟨A.toFiniteRepresentation, hpair.2, ?_⟩
    apply Eq.trans ?_ hA
    apply (classOf_eq_iff _ _).mpr
    refine ⟨⟨.refl A.representation, ?_⟩⟩
    ext v
    change (0 : A) = A.monodromy v
    rw [hpair.1]
    rfl
  · rintro ⟨B, hB, hclass⟩
    have hdeg := (LocalFactor.wdEulerPolynomial_natDegree_eq_rank_iff
      (localInertia F) (zeroMonodromy (localNormCharacter F).toMonoidHom B)
        (localGeometricFrobenius F)).mpr ⟨rfl, hB⟩
    have hRank : (zeroMonodromy (localNormCharacter F).toMonoidHom B).rank =
        (n : ℕ) := by
      change classRank (classOf _) = (n : ℕ)
      rw [hclass]
      exact D.property
    simpa only [parameterEulerPolynomial, ← hclass,
      LocalFactor.WeilDeligne.eulerPolynomialClass_classOf,
      LocalFactor.WeilDeligne.eulerPolynomial, hRank] using hdeg

end Langlands.Correspondence
