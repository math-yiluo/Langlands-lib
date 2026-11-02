# Positive forms on actual finite-order automorphic Hecke lines

For a supplied finite-order continuous complex Hecke character of a number
field in any universe, this internal construction gives a chosen positive
definite Hermitian form on the actual automorphic determinant-character line.
Every natural matrix rank is allowed. The carrier and the finite, compact
and genuine differential operators remain those of the constructed embedded
line of functions `g ↦ χ(det g) * c`.

`FiniteOrderHeckeRealization.unitaryForm` applies the existing actual
determinant-twist form construction to the explicit form on actual constants.
Finite order gives unit modulus for the determinant character. The underlying
form is the pullback through inverse determinant multiplication of the
constant-line form. Consequently one positive Hermitian core is invariant
under the finite adelic group and the standard infinite compact group, and
is skew invariant for the genuine real infinitesimal directions. These
conditions are inherited from the proved determinant-twist constructor,
rather than assumed as properties of the output.

`unitaryForm_inner_determinantTwistEquiv` specializes the actual multiplier's
isometry formula to constants. Composing with the existing scalar equivalence
gives

```text
B(scalarEquiv c, scalarEquiv d) = d * conjugate(c).
```

Surjectivity of this equivalence proves `unitaryForm_inner` for arbitrary
vectors. The existing inverse-coordinate formula is identity evaluation of
the original represented function, so `unitaryForm_inner_evaluate` gives

```text
B(f,g) = g(1) * conjugate(f(1)).
```

These formulas use the complex inner product convention that is conjugate
linear in its first argument. They retain the actual function embedding.

The chosen form witnesses whole-operator unitarizability of the actual
realization. The existing representative criterion proves the predicate on
its whole-operator isomorphism class. Restriction gives the existing generic
unitarizability predicates for the actual finite and compact actions, and
transport through the faithful finite-image equivalence gives unitarizability
of the actual finite invariant form image.

In rank one, under the same explicit `[CompactSpace (AdeleQuotient F)]`
hypothesis used to construct the existing cuspidal object, that object's
underlying realization is definitionally this character line. It is therefore
unitarizable, and its forgetful whole-operator class has the same property.
No new predicate or equivalence relation on cuspidal objects is introduced.

The provenance is internal: this pair composes the explicit constant-line
form, the actual determinant-twist positive-form construction, the actual
Hecke-line scalar equivalence and the existing class and finite-image
transport results. The coordinate and evaluation formulas follow from their
proved identities. No new original-literature identification is claimed.
The form and all assertions outside the rank-one cuspidal section require no
compact additive adele quotient hypothesis. This construction asserts no
invariant integral formula, continuity for a form-space topology, Hilbert
globalization, spectral occurrence, general-character realization or
classification of cuspidal representations.
