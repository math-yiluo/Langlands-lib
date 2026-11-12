import Langlands.Galois.Local.HodgeTate
import Langlands.Galois.CompatibleFamily
import Langlands.Global.CompletionPadicTower

/-!
# Taylor's removal of the cohomological multiplicity

R. Taylor's argument (letter to L. Clozel, December 1991), as sketched in
Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
§3, printed pp.102-103: a continuous `λ`-adic representation `W` of
`Gal(K̄/K)` whose geometric Frobenius elements have characteristic
polynomials `P_v(X)^m` at almost all places, and which has a Hodge-Tate
decomposition at a place above `ℓ` with `n` distinct twists, each occurring
`m` times, has semisimplification `U^m` for an `n`-dimensional `U` over a
finite extension of the coefficient field.

The statement is an unproved `Prop`. Semisimplifications are compared through
characteristic polynomials of all elements of the Galois group.
-/

noncomputable section

universe uK uL uV

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Global.CompletionPadic

variable {K : Type uK} [Field K] [NumberField K] {L : Type uL} [Field L] [NumberField L]

/-- The restriction of the `λ`-adic representation `A` to a decomposition group at a
place `v` of `K` above the residue characteristic `ℓ` of `λ` has a Hodge-Tate
decomposition with twists `k i`, `i < n`, each occurring `m` times over `L_λ`.
Both completions are `ℚ_ℓ`-algebras through their canonical `ℓ`-adic structures. -/
def HasHodgeTateDecompositionAt (lam : FinitePlace L) (A : LambdaAdic.{uK, uL, uV} K L lam)
    (v : FinitePlace K) (hv : residuePrime v = residuePrime lam) (n m : ℕ) (k : Fin n → ℤ) :
    Prop :=
  letI : Algebra ℚ_[residuePrime lam] (FiniteCompletion K v) := padicAlgebraAt v hv
  letI : Algebra ℚ_[residuePrime lam] (FiniteCompletion L lam) := padicAlgebra lam
  haveI : FiniteDimensional ℚ_[residuePrime lam] (FiniteCompletion K v) :=
    (padicFieldAt v hv).finiteDimensional
  HodgeTate.HasHodgeTateDecomposition (residuePrime lam) (FiniteCompletion K v)
    (FiniteCompletion L lam) (atFinitePlace v A) n m k

/-- Taylor's multiplicity removal (Harris 1997, §3, pp.102-103).

Data: number fields `K` and `L`, a finite place `λ` of `L`, a continuous
representation `A` of `Gal(K̄/K)` on a finite-dimensional `L_λ`-vector space,
natural numbers `n` and `m > 0`, a finite set `T` of places of `K`, polynomials
`P_v ∈ L[X]` and injective twists `k : Fin n → ℤ`.

Hypotheses: for `v ∉ T`, `P_v` is monic of degree `n`; for `v ∉ T` not above the
residue characteristic `ℓ` of `λ`, `A` is unramified at `v` and a geometric
Frobenius acts with characteristic polynomial `P_v(X)^m`, that is with Euler
polynomial `det(1 - ρ(Frob_v) X)` the reverse of `P_v^m`; at some place `v` above
`ℓ`, `A` has a Hodge-Tate decomposition `⊕_{i<n} ((C_v ⊗_{ℚ_ℓ} L_λ)(k i))^m`.

Conclusion: there are a finite extension `Λ` of `L_λ`, with its unique Hausdorff
vector-space topology, and a continuous representation `U` of `Gal(K̄/K)` on an
`n`-dimensional `Λ`-vector space such that for every `g`, the characteristic
polynomial of `A(g)` is the `m`-th power of that of `U(g)` (by Brauer-Nesbitt, the
semisimplification of `A ⊗ Λ` is `U^m` up to semisimplification), and `U` is
unramified at every `v ∉ T` not above `ℓ`, with Euler polynomial the reverse of
`P_v`. -/
def TaylorMultiplicityRemovalStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] (L : Type uL) [Field L] [NumberField L]
    (lam : FinitePlace L) (A : LambdaAdic.{uK, uL, uV} K L lam)
    (n m : ℕ) (T : Finset (FinitePlace K)) (P : FinitePlace K → L[X]) (k : Fin n → ℤ),
    0 < m → Function.Injective k →
    (∀ v ∉ T, (P v).Monic ∧ (P v).natDegree = n) →
    (∀ v ∉ T, residueCharacteristic v ≠ residueCharacteristic lam →
      HasEulerPolynomialAt A v
        (((P v) ^ m).reverse.map (NumberField.FinitePlace.embedding lam))) →
    (∃ (v : FinitePlace K) (hv : residuePrime v = residuePrime lam),
      HasHodgeTateDecompositionAt lam A v hv n m k) →
    ∃ (Λ : Type uL) (fieldΛ : Field Λ),
      letI : Field Λ := fieldΛ
      ∃ (algebraΛ : Algebra (FiniteCompletion L lam) Λ),
        letI : Algebra (FiniteCompletion L lam) Λ := algebraΛ
        letI : TopologicalSpace Λ := moduleTopology (FiniteCompletion L lam) Λ
        FiniteDimensional (FiniteCompletion L lam) Λ ∧
        ∃ U : Objects.{uK, uL, uV} K Λ,
          U.val.rank = n ∧
          (∀ g, (characteristicPolynomial A g).map (algebraMap (FiniteCompletion L lam) Λ) =
            characteristicPolynomial U g ^ m) ∧
          ∀ v ∉ T, residueCharacteristic v ≠ residueCharacteristic lam →
            HasEulerPolynomialAt U v ((P v).reverse.map
              ((algebraMap (FiniteCompletion L lam) Λ).comp
                (NumberField.FinitePlace.embedding lam)))

end Langlands.GaloisRepresentation
