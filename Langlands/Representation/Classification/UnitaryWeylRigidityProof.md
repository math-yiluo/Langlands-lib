# Proof of real determinant exponent rigidity under unitary Weyl association

Author: Worker 257.

`Langlands.glUnitaryWeylRealExponentRigidity` proves the published proposition
`Langlands.GLUnitaryWeylRealExponentRigidityStatement.{uF, uV, uW}` from
`Langlands.Representation.Classification.UnitaryWeylRigidityStatement`. All three
conjuncts are proved, for every prime `p`, every `PadicField.{uF} p` with
`TopologicalData`, every positive rank `n` and every block shape `B`. The two
carriers of the rigidity clause stay in the independent universes `uV` and `uW`.
The statement pair and the pairs it imports are unchanged.

The proof is self-contained apart from published Library results. It assumes no
central character, scalar-action certificate, chosen invariant form, tensor
factorization, classification theorem or Langlands quotient theorem. The positive
rank hypothesis `0 < n` is not used.

The helper results are in the namespace `Langlands.UnitaryWeylRigidity`. They are
proved at the generality needed here and are not separate published targets.

## Coordinate geometry (first conjunct)

`blockIndex_iff_of_conjugatesLevi` combines the published
`CuspidalSupport.blockIndex_eq_of_conjugatesLevi_apply` and
`CuspidalSupport.blockIndex_eq_of_conjugatesLevi`. For an actual
`CuspidalSupport.ConjugatesLevi B C w`, it gives
`blockIndex C (w a) = blockIndex C (w b) ↔ blockIndex B a = blockIndex B b`.

`card_blockFiber` proves that the coordinates `a` with `blockIndex B a = i` are
counted by `B.size i`. The map `x ↦ B.index i x` is a bijection from
`Fin (B.size i)` onto this fiber, by `blockIndex_index` and
`exists_index_of_blockIndex_eq`. `size_eq_of_blockIndex_iff` then restricts `w`
by `Equiv.subtypeEquiv` to a bijection from the source fiber of `blockIndex B a`
onto the target fiber of `blockIndex C (w a)`. The two cardinalities, hence the
block sizes, agree. The first conjunct is these two results.

## Unit-modulus scalar action

`norm_eq_one_of_isUnitarizable` takes a representation with `IsUnitarizable ρ`
and an element `g` with `ρ g v = c • v` for all `v`. It obtains an actual
`InvariantPositiveForm` `b` from the existential `IsUnitarizable`. Invariance at
a nonzero vector `v` gives
`conj(c) * c * b.inner v v = b.inner v v`. Linearity in the second argument is
derived from `smul_left` and conjugate symmetry. `b.inner v v` is nonzero by
definiteness, so `conj(c) * c = 1`. This is `Complex.normSq c = 1`, hence
`‖c‖ = 1`.

`exists_norm_one_scalar` applies this to a central element `z` of an
irreducible admissible unitarizable representation. The operator `ρ z` is an
intertwining endomorphism because `z` commutes with every group element. The
published `admissibleSchur_scalarEndomorphism` from `Smooth.Schur.Proof` makes
it scalar. The carrier is nontrivial because irreducibility is simplicity of the
associated module, so it has a nonzero vector. The scalar therefore has modulus
one. These steps use only irreducibility, admissibility and `IsUnitarizable`.

## Block scalars and transport

`leviConjugation_blockScalarLevi` proves the following. Let `a` and `a'` be unit
tuples on the blocks of `B` and `C` with
`a' (blockIndex C (w x)) = a (blockIndex B x)` for every coordinate `x`. Then
`leviConjugation B C w hw` sends `B.blockScalarLevi F a` to
`C.blockScalarLevi F a'`. The proof applies injectivity of the Levi embedding
and `CuspidalSupport.leviConjugation_embedding`, which reduce the claim to
conjugation by the permutation matrix in `GL_n`. It then compares entries with
`permutation_conjugate_entry` and `BlockShape.coe_blockScalar`. Both sides are
diagonal matrices, and their diagonal entries agree at `(x, x)` by the
hypothesis at `w⁻¹ x`.

`coe_leviRealPowerCharacter_mulSingle` specializes the published formula
`coe_leviRealPowerCharacter_blockScalar`. It concerns the block scalar
`Pi.mulSingle i u`, whose entry in block `i` is the unit `u` and whose other
entries are one. On it the real determinant character of exponent `t` takes the
value `‖u‖_F ^ (B.size i * t i)`, with `‖·‖_F` the normalized absolute value
`T.normalizedAbs`. All other factors of the product are `1`.
`normalizedAbs_uniformizer_pos_ne_one` uses `T.normalizedAbs_uniformizer`
(value `q⁻¹`) and `T.residueCardinality_gt_one`. It shows that the uniformizer
has positive normalized absolute value different from one. In particular the
uniformizer is nonzero (`uniformizer_ne_zero`) and gives a unit `ϖ`.

## Coordinate rigidity (second conjunct)

`coordinate_exponent_eq` is the second conjunct for one coordinate `a`. Its
field instance is an arbitrary topology on `F.Carrier`; the final theorem uses
`T.topology`. Put `i = blockIndex B a` and `j = blockIndex C (w a)`. Take
`α = Pi.mulSingle i ϖ` on the blocks of `B` and `α' = Pi.mulSingle j ϖ` on the
blocks of `C`. Partition preservation shows that `α'` at `blockIndex C (w x)`
equals `α` at `blockIndex B x` for every `x`. Hence actual Levi conjugation
sends `B.blockScalarLevi α` to `C.blockScalarLevi α'`. Both block scalars are
central (`blockScalarLevi_commute`). `exists_norm_one_scalar` gives unit-modulus
scalars `cω` and `cη` for their actions in `ω` and `η`.

Choose a nonzero vector `v` of the source carrier; its image under the given
equivalence `e` is nonzero. The intertwining property of `e` at
`C.blockScalarLevi α'` is applied to `v`. The transported representation acts
through the inverse of `leviConjugation`, which returns `B.blockScalarLevi α`.
By `leviRealPowerTwist_apply`, the property reads

```text
(χ_{B,s}(B.blockScalarLevi α) * cω) • e v = (χ_{C,t}(C.blockScalarLevi α') * cη) • e v.
```

Here `χ_{B,s}` denotes `T.leviRealPowerCharacter B s`. Since `e v ≠ 0`, the two
complex scalars agree. Taking norms removes `cω` and `cη`. The block-scalar
formula gives
`‖ϖ‖_F ^ (B.size i * s i) = ‖ϖ‖_F ^ (C.size j * t j)` of nonnegative reals.
Injectivity of real powers of a positive base different from one
(`Real.rpow_right_inj`) gives `B.size i * s i = C.size j * t j`. The first
conjunct gives `C.size j = B.size i`, and `B.size i` is positive, so
`t j = s i`.

The final theorem's second conjunct introduces the data and the `Nonempty`
equivalence, then applies `coordinate_exponent_eq` at each coordinate.

## Generic self-association (third conjunct)

`flattenBlockEquiv_symm_blockIndex` proves
`((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S) x)).1 = blockIndex B x`.
Each coordinate has the form `(B.flatten S).index k c`. The proof applies
`blockIndex_index`, the published `BlockShape.flatten_index` and
`blockIndex_index` again.

In the third conjunct, put `C = B.flatten S` and let `e` be the exponent of the
statement. Apply `coordinate_exponent_eq` to the self-equivalence, with
`ω = η`, `B = C` and `s = t = e`. It gives `e (blockIndex C (w a)) = e (blockIndex C a)`
for every coordinate `a`. By the flattened-index identity this reads

```text
-v₀(blockIndex C (w a)) + t(blockIndex B (w a)) = -v₀(blockIndex C a) + t(blockIndex B a),
```

and linear arithmetic gives the invariance of `v₀ - t` required by the second
component of `IsRelativeGenericParameter C B v₀ t`. Its partition hypothesis is
`blockIndex_iff_of_conjugatesLevi` for the self-conjugation `hw`. That component
then gives `w ∈ blockWeyl B`. The argument works for every real `v₀`. It uses no
positivity or regularity of `v₀`, no chamber condition on `t`, no cuspidality and
no support witness. Injectivity of `t`, the first component of the predicate, is
not used.

## Original sources and provenance

The exact statement is derived content, as recorded in the target's Markdown.
The motivating source is Allan J. Silberger, *The Langlands quotient theorem for
p-adic groups*, Math. Ann. 236 (1978), 95–104, printed pp.96–100, in particular
the stabilizer comparison in the proof of Lemma 5.3 on p.100 (registered source
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`).
The Schur/central-character input follows Bill Casselman, *Introduction to
admissible representations of p-adic groups*, Chapter II (revision June 16,
2019), Propositions II.1.6 and II.2.1, pp.4–5, with irreducibility and
admissibility explicit (registered source
`casselman-2019-smooth-representations`). The Lean proof uses the published
`admissibleSchur_scalarEndomorphism` for this step. The block-scalar and
unit-modulus arguments are the implemented forms of the derivation in the
target's Markdown. This proof does not address the multiplicity assertions of
Silberger's Lemma 5.3. The scope note `notes/jacquet/silberger-lemma53-scope.md`
continues to apply to them.

## Checks

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Development compilation had no errors
and no warnings. Declaration inspection of
`Langlands.glUnitaryWeylRealExponentRigidity` reported a theorem with level
parameters `[uF, uV, uW]`. Its only axioms are `propext`, `Classical.choice` and
`Quot.sound`.
