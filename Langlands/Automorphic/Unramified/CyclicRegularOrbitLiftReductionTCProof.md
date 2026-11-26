# Reduction of cyclic regular orbit lifting over a totally complex base

`Langlands.Automorphic.Unramified.cyclicRegularOrbitLiftReductionTC` proves
`CyclicRegularOrbitLiftReductionTCStatement.{uF,uE,uV,uW}`, keeping the
four independent universe parameters. Its premises are the totally complex
regular-induction existence statement
`CyclicRegularInductionExistenceTCStatement`, the forward comparison
`WeakInductionOrbitBaseChangeStatement` from weak induction to full-orbit
weak base change, and the totally complex constituent-pair statement
`CyclicWeakBaseChangePairMultiplicityTCStatement`. Its conclusion is
`CyclicRegularOrbitLiftTCStatement`. An `example` at the end of the module
instantiates the theorem at `.{0,0,uV,uV}`.

The proof introduces the base field `F` with its
`NumberField.IsTotallyComplex F` instance. Instance resolution uses that
instance when the proof applies the two totally complex premises to `F` and
`E`. The forward comparison has no totally complex hypothesis. The
supplied generator `σ` makes the automorphism group cyclic, which gives the
`IsCyclic` instance that the pair statement requires.

Two private lemmas of the module handle the upper orbit. For a regular
upper cusp, the map sending an automorphism `τ` to the `τ`-conjugate of the
cusp is injective. If two
automorphisms give the same conjugate, their quotient fixes the cusp. That
quotient is a power of `σ` with exponent less than the extension degree,
because the order of `σ` is `[E:F]`. Regularity forces the exponent to be
zero. So the orbit, a multiset over all automorphisms, has no repeated
constituent. Arithmetic pullback carries a unitary central character to each
conjugate, and `isUnitarizable_of_hasUnitaryCentralCharacter` makes every
orbit constituent unitarizable. Since the constituents are distinct, the
orbit has exactly `[E:F]` equal pairs with itself.

The existence premise supplies an actual lower cusp `S` of the multiplied
rank with unitary central character, so its singleton is unitary. The
comparison premise turns the weak induction of `S` into weak base change from
this singleton to the upper orbit. The pair statement, applied to this
singleton with itself and the orbit on both sides, gives
`∑_{0 ≤ i < [E:F]} (count of S ⊗ (η^i ∘ det) in {S}) = [E:F]`.
Each summand is at most one, so each equals one, and each twist
`S ⊗ (η^i ∘ det)` is the class of `S`. In degree greater than one this
includes the twist by `η` itself. In degree one, `η = 1` by
`HeckeCharacter.IsTrivialOnNorm.pow_finrank_eq_one`, and twisting by the trivial character
fixes every class. Either way the class of `S` is its own finite-order
determinant twist by `η`.

Let `DF` be a unitary lower datum with weak base change equal to the upper
orbit. The pair statement, applied to the singleton of `S` and `DF`, gives a
sum of `[E:F]` summands. Each summand is the multiplicity of the class of `S`
in `DF`, because every twist equals that class. The sum is `[E:F]`, so
cancelling the positive degree gives multiplicity one. Both weak base-change
relations preserve total rank, so `DF` has the rank of the singleton. After
erasing one copy of the class of `S` from `DF`, the remaining datum has rank
zero. Every constituent has positive rank, so that datum is empty and `DF`
is the singleton. Conversely, equality with the singleton gives the required
weak base change by the comparison premise.

The argument follows the unrestricted proof
`Langlands.Automorphic.Unramified.cyclicRegularOrbitLiftReduction` step for
step, under the totally complex premises. It formalizes the pair-count step
of Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula* (1989), Chapter III, Lemma 6.4, printed pp. 217–218.
The pair formula uses III.3.1, p. 201, and III.4.3, p. 204.

[Statement](CyclicRegularOrbitLiftReductionStatement.md)
