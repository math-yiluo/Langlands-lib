# Proof of exclusion of the inducing exponent from proper quotients

Author: Worker 5120.

This module proves
`Langlands.Renard.AlgebraicFamily.inducedTwistQuotientExclusion :
InducedTwistQuotientExclusionStatement.{u, v}`, the exclusion proposition stated in
`InducedTwistQuotientExponentStatements`. The theorem has exactly that type, with
independent field and representation universes and no further hypotheses. It uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

Fix the data of the statement: a split component `a : A → M`, and an irreducible
admissible `ρ`.

1. The published `representedGeometricLemma`, applied with `Q = P`, gives an enumeration
   `c` of the double cosets `P(k)\G(k)/P(k)`, representatives `z i`, intersection data
   `D i`, and the gluing of `r_P ∘ i_P` from the pieces.
2. A parabolic root presentation `pres` of `(p, l, a)` exists
   (`parabolicRootPresentationExistence`), and so does integral reflection data `R` for
   its maximal split torus (`relativeRootReflectionExistence`). The presentation has a
   standard cocharacter, and the relative roots are finite
   (`IsSplitTorus.finite_relativeRoots`). Hence the open chamber is nonempty
   (`restrictedCorootChamber_nonempty`). Its point is realized as the real part of the
   positive unramified character `ψ₀ = leviPositiveUnramifiedCharacter …`
   (`leviUnramifiedRealPart_positiveCharacter`).
3. For each index `i` with `c i ≠ P 1 P`, `exists_polynomial_pieceSeparation` gives a nonzero
   polynomial `F i`. Off its zero set, the piece `D i` at `ρψ` shares no generalized
   `A(k)`-eigencharacter with `ρψ`. The polynomial of the statement is the product over all
   indices, with factor `1` at the identity coset. It is nonzero.
4. For `ψ` in its principal open set, every factor is nonzero at `ψ`
   (`mem_rationalUnramifiedPrincipalOpen_prod`). Twisting preserves irreducibility and
   admissibility (`SmoothRep.isIrreducible_twist_iff`, `SmoothRep.isAdmissible_twist_iff`).
   `not_isGeneralizedEigencharacter_jacquet_quotient_of_pieceSeparation` then gives the
   conclusion for every exponent `χ` of `ρψ` and every nonzero invariant subspace `S`.

## Relation to the source

The statement is the derived exclusion half of the irreducibility argument in Konno 2003,
Theorem 4.2 (pp. 402–405). The implemented proof follows the separation of geometric-lemma
constituents (Claim 4.2.1) and Frobenius reciprocity (the base case of Claim 4.2.3, p. 404).
Claim 4.2.2 is the quotient-Jacquet vanishing criterion. The proof uses a
Zariski-generic separation of central exponents on the split component `A_M` instead of
Konno's analytic neighbourhood.

## Dependencies

The supporting modules are `InducedTwistExclusionChamber`, `InducedTwistExclusionAlgebra`,
`InducedTwistExclusionConcrete` and `InducedTwistExclusionGenericity`. All their inputs are
proved Library theorems; no unproved representation-theoretic statement is assumed.
