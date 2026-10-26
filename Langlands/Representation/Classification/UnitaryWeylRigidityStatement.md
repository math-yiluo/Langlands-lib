# Real determinant exponents under unitary Weyl association

Author: Worker 497.

`Langlands.GLUnitaryWeylRealExponentRigidityStatement` is a derived
proposition definition for actual standard product Levis of positive-rank
GL_n over a `PadicField` with compatible `TopologicalData`. It groups the
coordinate geometry, real-exponent rigidity, and the resulting generic
self-association assertion into one focused proof target. This file states
the proposition; it does not prove it.

## Exact assertions

The first clause says that a permutation `w` conjugating the entire embedded
Levi of `B` onto that of `C` preserves their coordinate block equivalence
relations in both directions:

```text
blockIndex C (w a) = blockIndex C (w b)
  iff blockIndex B a = blockIndex B b.
```

It also asserts equality of the corresponding block sizes. Thus a source
block is carried bijectively onto a target block. These are conclusions of
`CuspidalSupport.ConjugatesLevi`, which is equality of actual matrix
subgroups after permutation-matrix conjugation. They are not additional
geometric hypotheses on the representation-theoretic clauses.

The second clause takes arbitrary actual representations `ω` and `η` of
`B.Levi F.Carrier` and `C.Levi F.Carrier`, on independent complex module
carriers `V` and `W`. Both are irreducible, admissible, and unitarizable.
For real determinant vectors `s` and `t`, it assumes an actual intertwining
linear equivalence, expressed by `Nonempty`,

```text
transport B C w hw (T.leviRealPowerTwist B s ω)
  ≃ T.leviRealPowerTwist C t η.
```

Its conclusion is the coordinate equality

```text
t(blockIndex C (w a)) = s(blockIndex B a)     for every a : Fin n.
```

The direction matches the existing `transport`: its action pulls back along
`(leviConjugation B C w hw).symm`. A target block containing `w a` therefore
pulls back to the source block containing `a`. There is no supplied tensor
factorization, central character, scalar-action certificate, invariant form,
or norm on either carrier. `IsUnitarizable` only asserts existence of an
invariant positive definite Hermitian form.

The third clause fixes a refinement `S` of a coarse shape `B` and puts
`C = B.flatten S`. For every irreducible admissible unitarizable actual
representation `ω` of the fine product Levi, arbitrary real `v₀`, and
`IsRelativeGenericParameter C B v₀ t`, it uses exactly the exponent

```text
e(k) = -v₀(k) + t(((B.flattenBlockEquiv S).symm k).1).
```

Every permutation conjugating the entire fine Levi onto itself and giving
an actual self-equivalence of this twist belongs to `blockWeyl B`. The clause
quantifies all such permutations; hence it also applies to the underlying
permutations of the existing minimal associating-permutation subtypes.
Partition preservation is not an extra premise. The first clause supplies
it from actual fine-Levi conjugation.

## Original sources and derived provenance

Allan J. Silberger, *The Langlands quotient theorem for p-adic groups*,
Math. Ann. 236 (1978), 95–104, provides the motivating stabilizer comparison.
Printed pp.96–99 give the real exponent spaces, normalized twists,
inverse-conjugation transport, and the setup of genericity; Lemma 5.2 is on
pp.99–100. The displayed equality of ambient and coarse Weyl stabilizer
cardinalities in the proof of Lemma 5.3, p.100, is the use isolated here.

- Registered source ID:
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`.
- Original: `/home/taskhub/pilot/literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
- PDF SHA-256:
  `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
- Reading for this contribution: printed pp.96–100 (PDF pages 2–6);
  p.100 also checked visually, including the stabilizer display.

Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter II, *Smooth representations*, revision June 16, 2019,
Proposition II.1.6, p.4, and Proposition II.2.1 with its preceding
admissibility assumption and proof, p.5, supply the Schur/central-character
input. The literal II.1.6 omits necessary hypotheses in its Hom formula;
we use irreducibility and admissibility explicitly, as in the corrected
published `AdmissibleSchurStatement` and its proved central-character helper.

- Registered source ID: `casselman-2019-smooth-representations`.
- Original: `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.
- PDF SHA-256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Reading for this contribution: printed/PDF pp.3–5, including both
  propositions and the central-character proof.

No errata file for either source is present in the current Library notes.
The present target is derived content, not a claim that either source states
this exact GL_n theorem or its full generality. In particular it neither
states nor proves the multiplicity assertions of Lemma 5.3. The reviewed
scope limitation in `notes/jacquet/silberger-lemma53-scope.md` remains
applicable to that separate comparison.

## Blockwise derivation and normalization

The geometric assertion is internal standard matrix geometry. Conjugation
by the permutation matrix carries matrix entries at `(a,b)` to `(w a,w b)`.
Membership in an embedded block-diagonal Levi detects whether two
coordinates share a block. Conjugating onto, and then conjugating back,
gives the two implications. The permutation restricts to a bijection of
corresponding coordinate blocks, so their sizes agree. Existing proved
Library helpers include
`CuspidalSupport.blockIndex_eq_of_conjugatesLevi` and
`CuspidalSupport.blockIndex_eq_of_conjugatesLevi_apply` in
`CuspidalSupport.BlockPermutation`; the proposition does not assume them
as input certificates.

Here is the mathematical justification for the rigidity target, to be
implemented separately. Irreducibility and admissibility give scalar action
of every central element, by Schur's lemma. In an invariant positive form,
a nonzero vector has positive squared length. Invariance under a scalar
central action makes that squared length equal to the squared modulus of the
scalar times the same squared length. Therefore the scalar has modulus one. This must be
deduced from `IsUnitarizable`, not added as a premise.

Fix a source block `i` and its image block `j`. Use the actual
`B.blockScalarLevi F.Carrier a` with `a i` a uniformizer and all other
entries one. It is central in the product Levi, and conjugation carries it
to the analogous target block scalar. The existing formula
`coe_leviRealPowerCharacter_blockScalar` gives real positive twist factors

```text
|varpi|_F ^ (B.size(i) * s(i))
  and |varpi|_F ^ (C.size(j) * t(j)).
```

An actual equivalence identifies the twisted scalar actions. Taking complex
moduli cancels the two unit-modulus central-character factors. Since
`|varpi|_F = q^(-1)` is positive and different from one, real powers identify
the weighted exponents. The equal block sizes are positive, so cancellation
gives `s(i) = t(j)`. Each block can be isolated this way. Testing only the
ambient scalar center would recover only the sum of the weighted exponents
and would not establish the asserted coordinate equalities.

For the final clause, the published `flatten_index` identity identifies the
parent label `((B.flattenBlockEquiv S).symm (blockIndex C a)).1` with
`blockIndex B a`. The rigidity conclusion for the same source and target
twist therefore says that `w` fixes the repeated vector `-v₀ + t`.
Negating this equality gives precisely invariance of `v₀ - t` used by
`IsRelativeGenericParameter C B v₀ t`. Combined with partition preservation
from actual self-conjugation, that predicate gives `w ∈ blockWeyl B`.

This reasoning works for every fine real vector `v₀`. It uses no positivity
or regularity of `v₀`, no positive chamber for `t`, no cuspidality, and no
discrete-series support. Regularity of `t` is only the injectivity already
contained in the existing genericity predicate. No unitary generic
classification or Langlands quotient theorem is assumed.

## Interfaces, universes, and status

The imports are the existing actual Levi transport definitions, the
flattened shape and block-coordinate construction in `MinimalJacquetProof`,
the existing relative-generic predicate, the real determinant twist, and
the invariant-form definition. No existing target pair is edited and no
new reusable construction is introduced. Published constructions and helper
proofs used as interfaces do not prove the new rigidity target.

The statement declares independent `uF`, `uV`, and `uW`. The field is
`PadicField.{uF} p`, and the main rigidity clause quantifies `V : Type uV`
and `W : Type uW` separately. Both module structures are explicit; neither
carrier universe is identified with the field universe or with the other
carrier. The self-association clause uses the actual single source carrier
in `uV` without restricting the two-carrier rigidity clause.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). Development compilation
and exact declaration inspection succeeded with no warnings. Inspection
reported `statement_returns_prop: true`, kind `definition`, and exactly
`[uF, uV, uW]` as its independent level parameters. Its only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The exact proposition-body
fingerprint is
`8dd3b2818f2493dc92e4293a60bfc484b5fb143652615accbe4e7df706409014`.
These checks establish elaboration and scope, not mathematical truth. The proposition
requires a separate exact-target proof. Its proof successor will be published
only after this statement has independent acceptance and current Library
publication.
