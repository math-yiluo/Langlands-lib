import Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower
import Langlands.Global.HeckeCharacter

/-! # Hecke-family endpoints for supplied isobaric chains

Internal vocabulary for B6 of the operator external-inputs plan, Section 2.2.
The endpoint compares actual attached Euler polynomials with the rank-one
polynomials of actual Hecke characters. It constructs no cuspidal class from a
Hecke character and asserts no transfer or local compatibility theorem.
-/

noncomputable section

open scoped BigOperators

universe uF uK uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Unramified

namespace Unramified.HeckeFamily

variable {K : Type uK} [Field K] [NumberField K] {r s : ℕ}

/-- The product of rank-one Euler denominator polynomials, evaluated on an
actual invertible local element. At an unramified place the endpoint relation uses this at
every local uniformizer. Repeated characters contribute repeated factors. -/
def eulerPolynomial (χ : Fin r → HeckeCharacter K) (v : FinitePlace K)
    (π : (FiniteCompletion K v)ˣ) : Polynomial ℂ :=
  ∏ i : Fin r, (1 - Polynomial.C ((χ i).finiteComponent v π : ℂ) * Polynomial.X)

/-- Equality up to order of the actual continuous local characters at `v`,
with multiplicities. The reindexing may depend on the specified place. -/
def SameFiniteComponentsAt (χ : Fin r → HeckeCharacter K)
    (η : Fin s → HeckeCharacter K) (v : FinitePlace K) : Prop :=
  ∃ e : Fin r ≃ Fin s, ∀ i, (χ i).finiteComponent v = (η (e i)).finiteComponent v

end Unramified.HeckeFamily

namespace IsobaricData

variable {K : Type uK} [Field K] [NumberField K]
  [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-- The actual data have total rank `r` and an attached spectral system whose
Euler polynomials, outside one finite set containing its exceptional places,
are the products for the supplied `r` actual Hecke characters. All characters
are unramified outside that set, and equality holds for every uniformizer. -/
def HasHeckeFamily (D : IsobaricData K) (χ : Fin r → HeckeCharacter K) : Prop :=
  D.rank = r ∧
    ∃ s : SpectralSystem (FinitePlace K) D.rank,
      HasSpectralSystem.{uK, uV} D s ∧
        ∃ (S : Finset (FinitePlace K)) (hS : s.exceptional ⊆ S),
          (∀ i v, v ∉ S → (χ i).IsUnramifiedAt v) ∧
            ∀ (v : FinitePlace K) (hv : v ∉ S)
              (π : (FiniteCompletion K v)ˣ),
              Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
                s.eulerPolynomial v (fun h => hv (hS h)) =
                  Unramified.HeckeFamily.eulerPolynomial χ v π

end IsobaricData

namespace Unramified.PrimeCyclicBaseChangeTower.IsobaricChain

variable {F : Type uF} {K : Type uK} [Field F] [Field K]
  [NumberField F] [NumberField K] [Algebra F K]
  {T : PrimeCyclicBaseChangeTower F K}
  [∀ i, CompactSpace (AdeleQuotient (T.level i))]
  [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-- The chain's terminal datum, transported along `topEquiv.symm` to the actual
top field `K`, has the given Hecke-family Euler product. Unitarity, the start
condition and successive weak base change remain separate predicates. -/
def EndsAtHeckeFamily (D : T.IsobaricChain) (χ : Fin r → HeckeCharacter K) : Prop :=
  IsobaricData.HasHeckeFamily.{uK, uV} D.terminal χ

end Unramified.PrimeCyclicBaseChangeTower.IsobaricChain
end Langlands.Automorphic
