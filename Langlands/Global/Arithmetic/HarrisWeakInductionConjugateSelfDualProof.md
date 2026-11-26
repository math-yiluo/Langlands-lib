# Conjugate self-duality of a weak automorphic induction of a conjugate-inverse character

Module `Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualProof`.

- `Langlands.Global.Harris.weakInductionConjugateInverseSelfDual` proves exactly
  `Langlands.Global.Harris.WeakInductionConjugateInverseSelfDualStatement.{uV, uE, uE'}`,
  with independent universes `uE` and `uE'` for the CM fields `E` and `E'` and `uV` for the
  carrier of spectral presentations, and no hypothesis beyond those of the statement.
- `Langlands.Global.Harris.isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse`
  is the core result: for CM fields `E : Type uE`, `E' : Type uE'` with `[Algebra E E']` and
  `CompactSpace (AdeleQuotient E)`, a Hecke character `ξ` of `E'` with
  `IsConjugateInverse ξ`, and a cuspidal class `c` over `E` with
  `c.IsWeakAutomorphicInductionOf.{uE, uE', uV} ξ`, it concludes `c.IsConjugateSelfDual`
  from Euler constituent recovery at the single field `E`: the body of
  `CuspidalEulerConstituentRecoveryStatement.{uE, uV}` with `F := E`.

The general statement applies the core with the third component of its premise
`CuspidalSpectralRigidityStatement.{uE, uV}` at `E`. The module
`Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualTCProof` applies the same
core to the third component of the totally complex premise. The power-trace components of
the premises are not used.

`IsConjugateSelfDual` is the full pairing condition of
`Langlands.Automorphic.ConjugateContragredient`: a representative `S` carries a bilinear
pairing invariant under the operators twisted by the CM involution in the first variable,
whose partial map is injective and onto the contragredient functionals. The proof
constructs this pairing.

## Source

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134 (1998), 177–210 (registered source `harris-1998-local-langlands`),
Proposition 4.8 (printed pp.202–203, `math_9611226v1.tex` lines 1554–1563): the hypothesis
`ξ = ξ⁻¹ ∘ c` is at lines 1558–1559, and the conclusion `Π ∈ 𝒰(n,E)` (line 1561) includes
condition (ii) of Theorem 1.2, `π ≃ π̌ ∘ c` (lines 532 and 565–567). The proof of the prime
orbit (lines 1646–1664) does not argue conjugate self-duality separately. The argument for
it is given in the proof of Lemma 1.6 (lines 741–746): since `χ = χ⁻¹ ∘ c`, the induced
Galois representation is isomorphic to its conjugate contragredient, and strong
multiplicity one gives `π ≃ π̌ ∘ c`. The Lean proof replaces the Galois representation by
the unramified Euler factors of the induction and strong multiplicity one by Euler
constituent recovery.

## Implemented proof of the core result

1. Choose a representative `S` of `c` and a cuspidal realization `Sd` of its
   contragredient (`cuspidalContragredientExistence`).
2. `Sd.isoClass` is a weak automorphic induction of `ξ⁻¹`
   (`IsoClass.isWeakAutomorphicInductionOf_inv_of_isContragredientOf` in
   `Langlands.Automorphic.Unramified.ContragredientWeakInduction`): a spectral presentation
   of `Sd` has the inverse spectrum of a presentation of `S` at almost all places
   (`eigenvalues_eq_map_inv_of_isContragredientOf`), and inverting the eigenvalues inverts
   the coefficients of the induced Euler factors.
3. The CM involutions `fieldConj E` and `fieldConj E'` commute with `E → E'`
   (`HarrisDatum.complexConj_algebraMap`). The arithmetic pullback of weak induction
   (`IsWeakAutomorphicInductionOf.arithmeticComap`) makes the pullback of `Sd.isoClass`
   along `fieldConj E` a weak induction of `HeckeCharacter.comap (fieldConj E') ξ⁻¹`.
   This character is `ξ`: `IsConjugateInverse ξ` says exactly that
   `HeckeCharacter.comap (fieldConj E') ξ = ξ⁻¹`, and `comap` commutes with inversion. The
   pullback of a class along `fieldConj E` is its CM image
   (`IsoClass.arithmeticComap_fieldConj`), so `Sd.complexConj.isoClass` is a weak
   automorphic induction of `ξ`. Here the CM image is the arithmetic pullback of functions,
   not the scalar complex conjugation of their values.
4. Two attached systems weakly induced from `ξ` have the same Euler polynomials outside a
   finite set (`IsWeakInductionOf.sameEulerPolynomials`). Euler constituent recovery on the
   singleton families (`IsoClass.eq_of_sameEulerPolynomials`) gives
   `Sd.complexConj.isoClass = S.isoClass`.
5. `isoClass_isConjugateSelfDual_of_isContragredientOf` (in
   `Langlands.Automorphic.ConjugateSelfDualCriterion`) concludes: `Sd` is then equivalent
   to `S.complexConj`, which therefore realizes the contragredient of `S`, and composing its
   contragredient pairing with the CM image equivalence `S ≃ S.complexConj` gives the
   conjugate-contragredient pairing of `S`, including the injectivity and surjectivity of
   its partial map onto the contragredient functionals.

## Dependencies

`Langlands.Automorphic.ConjugateSelfDualCriterion` and
`Langlands.Automorphic.Unramified.ContragredientWeakInduction`, besides published Library
results: `cuspidalContragredientExistence`, `cuspidalDualPresentationExistence`,
`eigenvalues_eq_map_inv_of_isContragredientOf`,
`IsWeakAutomorphicInductionOf.arithmeticComap` and `HarrisDatum.complexConj_algebraMap`.
