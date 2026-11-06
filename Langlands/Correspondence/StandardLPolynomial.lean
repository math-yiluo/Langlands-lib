import Langlands.Correspondence.FullLFactorCompatibility
import Langlands.Correspondence.UnramifiedEuler

/-!
# Extracting the standard Euler polynomial from pair compatibility

Tensoring a Weil–Deligne pair with the trivial scalar character has its actual
right-unitor equivalence. Pair compatibility with rank one therefore specifies
the standard arithmetic Euler polynomial.
-/

noncomputable section

universe uK uG uV uW uX uF uP uA

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}

/-- The trivial scalar Weil–Deligne pair, with zero monodromy. -/
def tensorUnit (ν : G →* Kˣ) : WeilDeligneRepresentation.{uK, uG, uK} K G ν :=
  zeroMonodromy ν (FiniteRepresentation.of
    (Langlands.characterRepresentation (1 : G →* Kˣ)))

/-- The tensor right unitor is an equivalence of actual pairs. -/
def tensorUnitEquiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (tensor A (tensorUnit ν)) A where
  representationEquiv := {
    toLinearEquiv := TensorProduct.rid K A
    isIntertwining' g := by
      apply TensorProduct.ext'
      intro v a
      change K at a
      change ((1 : K) • (a : K)) • A.representation g v =
        A.representation g ((a : K) • v)
      simp only [one_smul, map_smul] }
  comm_monodromy := by
    apply TensorProduct.ext'
    intro v a
    change K at a
    change (TensorProduct.rid K A)
        ((TensorProduct.map A.monodromy (1 : Module.End K K) +
          TensorProduct.map (1 : Module.End K A) (0 : Module.End K K))
            (v ⊗ₜ[K] (a : K))) =
      A.monodromy ((TensorProduct.rid K A) (v ⊗ₜ[K] a))
    simp only [LinearMap.add_apply, TensorProduct.map_tmul, Module.End.one_apply,
      LinearMap.zero_apply, TensorProduct.tmul_zero, add_zero,
      TensorProduct.rid_tmul, map_smul]

/-- Tensoring in the second argument preserves an equivalence between independent
carrier universes. -/
def tensorRightEquiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν} (e : Equiv B C) :
    Equiv (tensor A B) (tensor A C) where
  representationEquiv := {
    toLinearEquiv := TensorProduct.congr (LinearEquiv.refl K A)
      e.representationEquiv.toLinearEquiv
    isIntertwining' := (tensorMap (Hom.id A) e.toHom).intertwiner.isIntertwining' }
  comm_monodromy := (tensorMap (Hom.id A) e.toHom).comm_monodromy

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.WeilDeligne

open WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}

/-- The pair L-factor with the trivial scalar pair is the standard L-factor. -/
theorem pairLFactor_tensorUnit
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (Φ : G) :
    pairLFactor A (tensorUnit ν) I Φ = rationalLFactor A I Φ :=
  rationalLFactor_eq_of_equiv I (tensorUnitEquiv A) Φ

/-- The same identity allows any representative equivalent to the scalar unit,
in a carrier universe independent of the first argument. -/
theorem pairLFactor_eq_of_tensorUnitEquiv
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν)
    (e : WeilDeligneRepresentation.Equiv B (tensorUnit ν))
    (I : Subgroup G) [I.Normal] (Φ : G) :
    pairLFactor A B I Φ = rationalLFactor A I Φ :=
  (rationalLFactor_eq_of_equiv I (tensorRightEquiv A e) Φ).trans
    (pairLFactor_tensorUnit A I Φ)

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.Correspondence

open Weil.Local WeilDeligneRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Against a trivial rank-one parameter, the arithmetic pair factor is the
reciprocal of the standard Euler polynomial. -/
theorem arithmeticPairLFactor_trivial_right {n : ℕ+}
    (D : WeilDeligneClass.{uF, uP} F n)
    (D0 : WeilDeligneClass.{uF, uP} F 1)
    (hD0 : IsRankOneParameterCharacter F 1 D0) :
    arithmeticPairLFactor F (parameterForget F D) (parameterForget F D0) =
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (parameterEulerPolynomial F D))⁻¹ := by
  obtain ⟨B, hB, ⟨eB⟩⟩ := hD0
  let A := Quotient.out (parameterForget F D)
  have hA : classOf A = parameterForget F D := Quotient.out_eq _
  change LocalFactor.WeilDeligne.pairLFactorClass (localInertia F)
    (localGeometricFrobenius F) (parameterForget F D) (parameterForget F D0) = _
  rw [← hA, ← hB, LocalFactor.WeilDeligne.pairLFactorClass_classOf]
  rw [LocalFactor.WeilDeligne.pairLFactor_eq_of_tensorUnitEquiv A B eB.symm]
  rw [parameterEulerPolynomial, ← hA,
    LocalFactor.WeilDeligne.eulerPolynomialClass_classOf]
  rfl

/-- Pair compatibility with a trivial rank-one parameter supplies the actual
standard arithmetic Euler polynomial as the automorphic pair denominator. -/
theorem IsPairLCompatibleAt.standardEulerPolynomial
    (ψ : NontrivialAdditiveCharacter F) {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat}
    {D0 : WeilDeligneClass.{uF, uP} F 1}
    {π : AutomorphicClass.{uF, uA} F r.succPNat}
    {π0 : AutomorphicClass.{uF, uA} F 1}
    (h : IsPairLCompatibleAt F ψ D D0 π π0)
    (hD0 : IsRankOneParameterCharacter F 1 D0)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν) :
    IsAutomorphicPairLPolynomial F ψ ν π π0 (parameterEulerPolynomial F D) := by
  obtain ⟨P, hP, hfactor⟩ := h.2 ν hν
  rw [arithmeticPairLFactor_trivial_right F D D0 hD0] at hfactor
  have hpoly : parameterEulerPolynomial F D = P :=
    RatFunc.algebraMap_injective ℂ (inv_injective hfactor)
  simpa only [hpoly] using hP

end Langlands.Correspondence
