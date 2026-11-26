# Reduction of cyclic stable descent to prime descent: proof

`Langlands.Automorphic.Unramified.cyclicStableDescentReduction` proves
`CyclicStableDescentReductionStatement.{uF, uE, uV, uW}`. It assumes the
nineteen premises of that statement and concludes
`CyclicStableDescentStatement.{uF, uE, uV, uW}` with every quantifier and
bound unchanged. The auxiliary results are in the namespace
`Langlands.Automorphic.Unramified.CyclicStableDescentReduction`. The module
does not prove the totally complex variant
`CyclicStableDescentTCReductionStatement`.

## Comparison of lower attachments

`exists_sameResidueDegreePowers` takes two weak base changes
`IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}` from lower classes `c` and
`c'` to one upper class `d`. It returns attachments `s` of `c` and `s'` of
`c'` in the factor universe `uV` with `SameResidueDegreePowers E s s'`. The two
upper systems are attached to the same class `d`. By
`IsoClass.HasSpectralSystem.eigenvalues_eq` they have the same spectrum at
every place where both are defined, so they have the same Euler polynomials.
This lemma goes through `IsoClass.hasSpectralSystem_iff` and
`CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`.
`IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials` moves the first weak
base change onto the second upper system. It discards the base places below the
finitely many extra upper exceptional places.
`SameResidueDegreePowers.of_common_weakBaseChange` then gives the comparison.

## Exclusion of norm-trivial self-twists

`eq_one_of_selfTwist` concerns a cyclic Galois extension `E/F`, an actual
cusp `S` over `F` and an actual cusp `T` over `E`, both with unitary central
character, and the relation `IsWeakBaseChangeOf T.isoClass S.isoClass`. If
`χ` is trivial on the norms from `E` and the class of `S` is its own twist by
`χ`, then `χ = 1`.

`HeckeCharacter.cyclicNormKernelCharacter` supplies a character `η` whose
kernel is the norm group. It also writes `χ = η ^ i` with `i < [E : F]`. The
proof then applies the pair-multiplicity premise. Both lower data are the
singleton of `S`, and both upper data are the singleton of `T`. These data are
unitary by `isUnitarizable_of_hasUnitaryCentralCharacter`. By
`equalConstituentPairCount_ofCuspidal`, the summand for `j` is `1` exactly
when the twist of `S` by `η ^ j` equals `S`, and `0` otherwise. The right
side equals `1`. The summand for `j = 0` is `1`. If `i ≠ 0`, the summand for
`i` is also `1`, so the sum would be at least `2`. Hence `i = 0`.

## Degree one

`isWeakBaseChangeOf_arithmeticComap_of_finrank_eq_one` uses a ring
isomorphism `e : F ≃+* E` that agrees with `algebraMap F E`. It shows that
`T.arithmeticComap e` is a weak descent of `T`. The attachment premises give
systems of `T` in the factor universes `uV` and `uW`.
`CuspidalSpectralArithmeticComapStatement` transports the `uV` system to the
pullback, reindexed by `finitePlaceEquiv e`. The published
`finitePlaceEquiv_under` shows that every place above `v` is
`(finitePlaceEquiv e).symm v`. Its inertia degree is one by
`inertiaDeg_eq_one_of_finrank_eq_one`. Its ramification index is one by
`ramificationIdx_eq_one_of_finrank_eq_one`, which uses the sum formula
`finitePlacesAbove_sum_ramification_inertia`. The two upper systems agree
there because they are attached to the same class. In degree one the
existence step uses `RingEquiv.ofBijective` with
`Algebra.finrank_eq_one_iff_bijective_algebraMap`. It gets the unitary
central character from `arithmeticComapUnitaryCentralCharacter`.

## The bottom prime step

`exists_descent_of_tower` works with a tower `F ⊆ K ⊆ E`, where `K` and `E`
are in the universe `uE` and `K/F` is cyclic of prime degree `p` with
generator `τ`. Let `σ ∈ Gal(E/F)` restrict to `τ`, and let `T` be a
`σ`-stable unitary cusp over `E`. Suppose `S` is a unitary cusp over `K` with
`IsWeakBaseChangeOf.{uE, uE, uW, uW} T.isoClass S.isoClass`. The lemma then
produces a unitary cusp over `F` that is a weak descent of `T` at
`.{uF, uE, uV, uW}`. The proof has five steps.

1. The equivariance premise for the compatible pair `(τ, σ)`, applied to the
   singletons, shows that the conjugate `τ S` is also a weak descent of `T`,
   because `T` is `σ`-stable.
2. `exists_sameResidueDegreePowers` and the fibre premise over `E/K` give a
   character `χ` of `K` trivial on the norms from `E`, with `τ S`
   isomorphic to `S ⊗ χ`.
3. The norm-character restriction premise makes `χ` invariant under
   `Gal(K/F)`. With `CuspidalDeterminantTwistArithmeticComapStatement`,
   induction on `k` gives that `τ^k S` is the twist of `S` by `χ^k`. Since
   `τ^p = 1`, the class of `S` is its own twist by `χ^p`.
4. `eq_one_of_selfTwist` over `E/K` gives `χ^p = 1`. If `χ ≠ 1`, the
   restriction premise says that `χ` restricted to the idele classes of `F`
   has exactly the norms from `K` as kernel. The twisted obstruction for `K/F`
   and `τ` then excludes the relation of step 2. Hence `χ = 1`, and `S` is
   `τ`-stable.
5. Prime descent for `K/F` uses a norm-kernel character from
   `cyclicNormKernelCharacter`. It gives a unitary cusp over `F` whose
   class lifts to `S`. The tower premise composes this lift with the lift
   from `S` to `T`.

## Existence and the degree induction

`exists_descent_step` assumes descent at `.{uE, uE, uW, uW}` for every
extension `E/K` with `K` in `uE` and `[E : K] < [E : F]`. Under that
assumption it proves descent for `E/F` at `.{uF, uE, uV, uW}`.

- In degree one it uses the lemma above.
- In prime degree it applies the prime descent premise.
- In composite degree `n` it takes `p` to be the least prime factor of `n`.
  It sets `H` to be the subgroup generated by `σ^p` and `K` to be the fixed
  field of `H`.

In the composite case the Galois group is commutative, so `H` is normal and
`K/F` is Galois (`IsGalois.of_fixedField_normal_subgroup`). By
`finrank_fixedField_eq_card` and `orderOf_pow_of_dvd`, `[E : K]` equals the
order of `σ^p`, which is `n / p`, and so `[K : F] = p`. The image of `σ^p`
under `subgroupEquivAlgEquiv` generates `Gal(E/K)`. Its ring isomorphism is
that of `σ^p`, so `T` is stable under it. The restriction
`σ.restrictNormal K` generates `Gal(K/F)` because `restrictNormalHom` is
surjective, and `restrictNormal_commutes` gives the compatibility used in
step 1. The adele quotient of `K` is compact by `compactSpace_adeleQuotient`.

`exists_descent_same` proves descent at `.{uE, uE, uW, uW}` for fields in
`uE` by strong induction on the degree. It feeds the same-universe instances
of the premises to `exists_descent_step`. The main theorem applies
`exists_descent_step` at the mixed levels with this same-universe result for
`E/K`. The descent it obtains is an actual cusp `S` over `F` with unitary
central character.

## All cuspidal descents and distinct twists

The class `c` is `S.isoClass`. For `i < [E : F]` the twist of `c` by `η ^ i`
is `IsoClass.determinantTwist`, and the relation holds by
`isFiniteOrderDeterminantTwist_determinantTwist`.

- Let `c'` lift to `T`. Then `exists_sameResidueDegreePowers` and the fibre
  premise over `E/F` at `.{uF, uE, uV, uV}` make `c'` a twist of `c` by a
  character trivial on norms. `cyclicNormKernelCharacter` writes that
  character as `η ^ i` with `i < [E : F]`. The fibre premise needs no
  unitarity of `c'`.
- `CuspidalWeakBaseChangeNormTwistStatement` gives the converse.
- Suppose `c'` is the twist of `c` by both `η ^ i` and `η ^ j`. Composing
  the two relations gives a self-twist of `c` by `η ^ i * (η ^ j)⁻¹`, which
  is trivial on norms. By `eq_one_of_selfTwist` over `E/F` at
  `.{uF, uE, uV, uW}`, it equals `1`. Hence `η ^ |i - j| = 1`. Since `η` has
  order `[E : F]` and `|i - j| < [E : F]`, `i = j`.

## Premise instances

| Instance | Used for |
| --- | --- |
| `CyclicPrimeStableCuspidalDescentStatement.{uF, uE, uV, uW}`, `CyclicPrimeTwistedCuspidalObstructionStatement.{uF, uE}`, `CyclicPrimeNormCharacterRestrictionStatement.{uF, uE, uE}`, `IsobaricWeakBaseChangeTowerStatement.{uF, uE, uE, uV, uW, uW}` | The mixed prime and bottom prime steps |
| `.{uE, uE, uW, uW}`, `.{uE, uE}`, `.{uE, uE, uE}` and `.{uE, uE, uE, uW, uW, uW}` versions of the same four premises | The same-universe induction |
| `IsobaricWeakBaseChangeEquivarianceStatement.{uE, uE, uW, uW}`, `CuspidalDeterminantTwistArithmeticComapStatement.{uE, uE}`, `CyclicWeakBaseChangePairMultiplicityStatement.{uE, uE, uW, uW}`, `CyclicCuspidalFiberStatement.{uE, uE, uW, uW}` | Every bottom prime step |
| `CuspidalSpectralAttachmentExistenceStatement.{uE, uV}`, `CuspidalSpectralAttachmentExistenceStatement.{uE, uW}`, `CuspidalSpectralArithmeticComapStatement.{uF, uE, uV}` | Degree one at the mixed levels |
| `CuspidalSpectralAttachmentExistenceStatement.{uE, uW}`, `CuspidalSpectralArithmeticComapStatement.{uE, uE, uW}` | Degree one in the same-universe induction |
| `CyclicCuspidalFiberStatement.{uF, uE, uV, uV}`, `CuspidalWeakBaseChangeNormTwistStatement.{uF, uE, uV, uW}`, `CyclicWeakBaseChangePairMultiplicityStatement.{uF, uE, uV, uW}` | The final classification and distinctness |

## Sources

The reduction follows James Arthur and Laurent Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula*, Annals of
Mathematics Studies 120 (1989), Chapter III:

- Theorem 3.1, printed p. 201: fibres of base change.
- Theorem 4.2(d), printed p. 202, with its proof on pp. 206–207: prime
  descent.
- Proposition 4.4(iii), printed p. 210: Galois equivariance of weak lifting.
- Lemma 6.3, printed p. 217: composite cyclic descent, with distinctness from
  the pole count of the self-pair L-function.

The proof of Lemma 6.3 descends first through a prime step `E/E₁` at the
top. Laurent Clozel and C. S. Rajan, *Solvable base change*,
arXiv:1806.02513v1 (2018), note in their introduction (PDF p. 1) that the
general cyclic case of Arthur and Clozel contains a mistake. At the end of §2
(PDF p. 7) they prove that the descendant at such a step is stable under the
Galois group. That proof uses the first part of their Theorem 2, which rests on
their Theorem 1 (PDF p. 2). Theorem 1 excludes a cusp twisted into its Galois
conjugate by a character whose restriction to the base idele classes generates
the characters trivial on norms.

The Lean proof instead descends at the bottom prime step `K/F` and uses the
induction for `E/K`. The stability of the descendant over `K` comes from the
fibre theorem, the character restriction, the self-pair count over `E/K` and
the prime case of Theorem 1 for `K/F`.
