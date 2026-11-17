import Langlands.Global.Arithmetic.ChebotarevStatement
import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Representation.Finite.CharacterTheoryProof

/-!
# Finite Galois Frobenius-trace rigidity

Prime realization makes every Galois automorphism an arithmetic Frobenius above an
unramified prime outside the exceptional set, so the trace hypothesis gives equality
of the two characters at every group element; the finite complex character theorem
`Langlands.FiniteCharacter.isomorphism` then gives an intertwining equivalence.
-/

noncomputable section

universe u v w z

namespace Langlands.Global

open NumberField IsDedekindDomain

/-- Frobenius-trace rigidity for finite Galois groups follows from prime
realization and the finite complex character theorem. -/
theorem finiteGaloisFrobeniusRigidity_of_primeRealization
    (h : ChebotarevPrimeRealizationStatement.{u, v}) :
    FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z} := by
  intro K _ _ L _ _ _ _ V _ _ _ W _ _ _ ρ τ S hS
  have hchar : ρ.character = τ.character := by
    funext σ
    obtain ⟨p, hpS, q, hlies, hunr, hfrob⟩ := h K L σ S
    exact hS p hpS q hlies hunr σ hfrob
  exact (Langlands.FiniteCharacter.isomorphism (G := L ≃ₐ[K] L) ρ τ).mp hchar

/-- Finite-dimensional complex representations of a finite Galois group of number
fields are determined up to isomorphism by their unramified Frobenius traces outside
any finite set of primes. -/
theorem finiteGaloisFrobeniusRigidityStatement :
    FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z} :=
  finiteGaloisFrobeniusRigidity_of_primeRealization chebotarevPrimeRealizationStatement

end Langlands.Global
