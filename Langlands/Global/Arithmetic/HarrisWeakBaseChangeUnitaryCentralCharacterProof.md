# Unitary central characters descend under arithmetic weak base change

`Langlands.Global.Harris.weakBaseChangeUnitaryCentralCharacter` proves (U),
`Langlands.Global.Harris.WeakBaseChangeUnitaryCentralCharacterStatement`, in
[HarrisProposition48SingletonDescentStatement](HarrisProposition48SingletonDescentStatement.md).
For number fields `F` and `E` with an `F`-algebra structure on `E` and compact
additive adele quotients, take actual cuspidal realizations `S` over `F` and `T`
over `E` of rank `r + 1`. Assume that `T` has a unitary central character and
that `T.isoClass` is arithmetic weak base change of `S.isoClass`. The theorem
produces a unitary Hecke character giving the central action on `S`. The field
universes and the two presentation universes are independent.

## Implemented proof

1. Use `OperatorRealization.existsUnique_hasCentralCharacter` with irreducibility
   to obtain the central character `ω` of `S`. Write `ξ` for the given unitary
   central character of `T`. The equivalence `isWeakBaseChangeOf_isoClass_iff`
   gives presentations `P` and `Q` of these very realizations whose spectral
   systems satisfy the cofinite arithmetic comparison.
2. At a place outside a presentation's exceptional set, take a nonzero
   spherical vector. The top standard spherical Hecke operator acts on it by
   the local scalar matrix of the chosen uniformizer
   (`standardHecke_cornerAction_last` and `standardDiagonal_last`). The global
   central character evaluates this action at the idele with that uniformizer
   in the given component. The same Hecke operator acts by the product of the
   Satake parameters (`standardHeckeScalar_last` and
   `elementaryCoefficient_rank`). Cancel the nonzero vector to identify the
   uniformizer value of the central character with that product in `ℂˣ`.
   The private lemma `finiteUniformizerValue_eq_satakeProduct` adapts the
   scalar comparison in
   [CyclicCuspidalCommonNormalization](../../Automorphic/Unramified/CyclicCuspidalCommonNormalization.md).
3. For each finite `v` where the comparison holds, take `w = placeAbove E v`.
   Its residue degree `f = f(w|v)` is positive. The Satake multiset at `w` is
   the image of the multiset at `v` under the `f`-th power map. Taking products
   retains all multiplicities and gives `ξ(ϖ_w) = ω(ϖ_v)^f`, where each value
   denotes evaluation on the corresponding uniformizer idele class.
   Taking complex norms gives `‖ω(ϖ_v)‖^f = 1`; injectivity of the positive
   natural power on nonnegative reals yields `‖ω(ϖ_v)‖ = 1`.
4. Discard also the finite set supplied by
   `HeckeFunctionalEquation.exists_finset_isUnramifiedAt` for `ω`.
   At every remaining finite place, `ω` is trivial on integral units.
   The subgroup `H` of ideles on which the pullback `ω.onIdeles` has norm one
   is closed by continuity and contains the principal ideles. Its preimage
   in each remaining local multiplicative group contains the integral units
   and the chosen uniformizer, so it is the whole local group by
   `CompletionPadic.subgroup_eq_top_of_uniformizer_mem`. Thus
   `IdeleDensity.eq_top_of_isClosed` gives `H = ⊤`. Surjectivity of the
   idele-class quotient then gives `ω.IsUnitary`.

## Provenance and scope

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989, `arthur-clozel-1989-base-change`), Chapter III, (1.1)
and Definition 1.1, printed p. 199 (PDF p. 213), give the unramified power
rule and use it in weak base change in the cyclic setting. This derived proof
uses the arithmetic power comparison already supplied by the hypothesis for
`E/F`. It requires no Galois, cyclic or CM assumption, no ramified base-change
comparison, and no base-change existence theorem.

The result supplies the downstairs unitary central character used in the
Library's singleton route for Harris, *The local Langlands conjecture for
GL(n) over a p-adic field, n < p* (1998, `harris-1998-local-langlands`),
Proposition 4.8, singleton case, printed p. 203 (PDF p. 27, TeX lines
1666–1674), where Harris invokes the argument of Lemma 1.6. This is a
separate consequence, not a formalization of all of that descent argument.
The Lean proof uses closed-subgroup density instead of factoring the modulus
through the idelic norm as described in the statement's paired Markdown.
