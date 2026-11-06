import Langlands.WeilDeligne.TensorDual
import Langlands.Correspondence.FullGammaCompatibility

/-!
# Gamma compatibility of full families from L, epsilon and duality

The dual of a tensor product of Weil–Deligne pairs is equivalent to the tensor
product of the duals. Hence the reflected arithmetic L-ratio of `X ⊗ Y` is the
quotient of the pair L-factors of `(X, Y)` and `(X^∨, Y^∨)`, and the published
L, epsilon and dual conditions of a full map give its gamma condition.
-/

noncomputable section



namespace Langlands.LocalFactor.WeilDeligne

universe uK uG uV uW

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The reflected L-ratio of a tensor class is the reflected pair L-factor of the
dual classes divided by the pair L-factor of the classes. -/
theorem rationalLRatioClass_tensorClass (I : Subgroup G) [I.Normal] (g : G) (c : Kˣ)
    (X : WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν)
    (Y : WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uW} K G ν) :
    rationalLRatioClass I g c (WeilDeligneRepresentation.tensorClass X Y) =
      RationalReflection.subst c
          (pairLFactorClass I g (WeilDeligneRepresentation.dualClass X)
            (WeilDeligneRepresentation.dualClass Y)) /
        pairLFactorClass I g X Y := by
  induction X, Y using Quotient.inductionOn₂ with
  | h A B =>
    change rationalLRatio (WeilDeligneRepresentation.tensor A B) I g c =
      RationalReflection.subst c (pairLFactor (WeilDeligneRepresentation.dual A)
        (WeilDeligneRepresentation.dual B) I g) / pairLFactor A B I g
    unfold rationalLRatio reflectedDualLFactor pairLFactor
    rw [rationalLFactor_eq_of_equiv I (WeilDeligneRepresentation.tensorDualEquiv A B) g]

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.Correspondence

universe uF uP uA

open Weil.Local LocalFactor LocalFactor.CommonClosure Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Pair L, epsilon and dual compatibility of a full map imply its pair gamma
compatibility for the same system. -/
theorem fullGammaFromFactors : FullGammaFromFactorsStatement.{uF, uP, uA} F := by
  intro eC ε hε c hL hEps hDual ψ r t D D'
  refine ⟨(hL ψ r t D D').1, fun ν hν => ?_⟩
  obtain ⟨E, hDE, hπ⟩ := hDual r.succPNat D
  obtain ⟨E', hDE', hπ'⟩ := hDual t.succPNat D'
  obtain ⟨P, hP, hPar⟩ := (hL ψ r t D D').2 ν hν
  obtain ⟨Pd, hPd, hPdar⟩ := (hL ψ r t E E').2 ν hν
  obtain ⟨e, he, hear⟩ := (hEps ψ r t D D').2 ν hν
  refine ⟨RankinSelberg.rationalGammaExpression (residueReflection F) e.1 e.2 P Pd,
    ⟨c r.succPNat E, c t.succPNat E', P, Pd, e, hπ, hπ', hP, hPd, he, rfl⟩,
    e.1, e.2, hear, ?_⟩
  have hX : parameterForget F E =
      WeilDeligneRepresentation.dualClass (parameterForget F D) := hDE
  have hY : parameterForget F E' =
      WeilDeligneRepresentation.dualClass (parameterForget F D') := hDE'
  have hPar' : WeilDeligne.pairLFactorClass (localInertia F) (localGeometricFrobenius F)
      (parameterForget F D) (parameterForget F D') = (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ :=
    hPar
  have hPdar' : WeilDeligne.pairLFactorClass (localInertia F) (localGeometricFrobenius F)
      (parameterForget F E) (parameterForget F E') = (algebraMap ℂ[X] (RatFunc ℂ) Pd)⁻¹ :=
    hPdar
  rw [WeilDeligne.rationalLRatioClass_tensorClass, ← hX, ← hY, hPar', hPdar', map_inv₀,
    RationalReflection.subst_polynomial, inv_div_inv, RankinSelberg.rationalGammaExpression,
    mul_div_assoc]

end Langlands.Correspondence
