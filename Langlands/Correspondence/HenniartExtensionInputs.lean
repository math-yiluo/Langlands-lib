import Langlands.Correspondence.HenniartStableMapStatement
import Langlands.Correspondence.ArithmeticFactors
import Langlands.VirtualRepresentation.Supercuspidal.Unramified

/-!
# Standard inputs for extending Henniart's stable map

Two standard facts used in Henniart (2000), §4.4, through Henniart (1993),
§§4.3–4.4, stated for the actual class spaces of the correspondence: every
supercuspidal class is an unramified twist of a unitary class with central
character of finite order, and unramified twists act on arithmetic pair factors
by the substitution `X ↦ z z' X` and on epsilon certificates by `(z z') ^ m`.
Proposition definitions only.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap Polynomial

universe uK uW uV

/-- Every supercuspidal class of `GL_n(K)` is the unramified twist of a unitary
class whose central character has finite order (Henniart 1993, §4.3, with the
unitarity of supercuspidal representations with unitary central character). -/
def SupercuspidalUnitaryFiniteOrderTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (π : PadicSupercuspidal.Basis.{uK, uV} K),
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K),
      HasFiniteOrderCentralCharacter K π₀ ∧
        PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val = π

/-- Unramified twists of arithmetic pair factors (Deligne 1973, (3.5.3) and
(5.5.1)–(5.5.2)): twisting the two members of a pair of continuous irreducible
Weil classes by the unramified characters with values `z` and `z'` at geometric
Frobenius substitutes `X ↦ z z' X` in the pair L-factor `1 / P(X)`, and multiplies
every epsilon certificate `c q^(-ms)` of a local-constant system by `(z z') ^ m`. -/
def ArithmeticPairUnramifiedTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{uK, uW} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (r n : ℕ)
    (σ : IrreducibleWeilClass.{uK, uW} K r.succPNat)
    (τ : IrreducibleWeilClass.{uK, uW} K n.succPNat) (z z' : ℂˣ),
    (∀ P : ℂ[X], arithmeticPairLFactor K (weilPairClass K σ) (weilPairClass K τ) =
        (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ →
      arithmeticPairLFactor K
          (weilPairClass K (FiniteRepresentation.continuousIrreducibleTwistEquiv
            (Weil.Local.localUnramifiedCharacter K z) _ σ))
          (weilPairClass K (FiniteRepresentation.continuousIrreducibleTwistEquiv
            (Weil.Local.localUnramifiedCharacter K z') _ τ)) =
        (algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C ((z : ℂ) * z') * X)))⁻¹) ∧
    ∀ (c : ℂˣ) (m : ℤ),
      IsArithmeticPairEpsilonFactor K eC ε hε ψ (weilPairClass K σ) (weilPairClass K τ) c m →
      IsArithmeticPairEpsilonFactor K eC ε hε ψ
        (weilPairClass K (FiniteRepresentation.continuousIrreducibleTwistEquiv
          (Weil.Local.localUnramifiedCharacter K z) _ σ))
        (weilPairClass K (FiniteRepresentation.continuousIrreducibleTwistEquiv
          (Weil.Local.localUnramifiedCharacter K z') _ τ)) (c * (z * z') ^ m) m

end Langlands.Henniart.Extension
