# Regular Langlands block-rank and real-parameter uniqueness

Author: Worker 359.

This module proves the exact published proposition
`Langlands.GLRegularLanglandsParameterUniquenessStatement`, with independent
field and representation universes and the stated maximum-universe carriers.
The target compares ordered block ranks and real determinant exponents; it
makes no assertion about the tempered representation classes.

The proof assembles published results implementing the parameter comparison
in A. J. Silberger, *The Langlands quotient theorem for p-adic groups*,
Math. Ann. 236 (1978), 95–104, Theorem 4.1, printed p.99, and Proposition 6.1,
printed pp.102–103. The registered source is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`.
The normalization and scope references are the paired
[statement](RegularLanglandsParameterStatement.md),
[continuation parameter note](../../../notes/jacquet/silberger-continuation-parameters.md)
and [Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md).

For each datum, form its actual external tensor on the whole product Levi.
Admissibility of each tempered block and the admissible Schur theorem make
each factor's self-intertwiners scalar. `FiniteTensor.isIrreducible_external`
therefore proves tensor irreducibility. `glBlockTensorTempered` proves analytic
temperedness for every Borel Haar realization on the actual central quotient.
These are proved inputs, rather than extra fields or assumptions on the datum.

`standardModuleLeviTwistEquiv` identifies the actual standard module with the
normalized induction of the real determinant twist of this tensor. Compose
its inverse with each given weak quotient map. On the second side, also
compose with the inverse representation equivalence obtained from the given
smooth categorical isomorphism. The resulting maps are actual surjections
to the same irreducible representation. The argument retains the arbitrary
weak quotient witnesses throughout. It never replaces them by distinguished
heads: the published `glSupportedRegularWeylConeComparison` already accepts
arbitrary common irreducible quotients and proves the needed comparison there
by its actual Jacquet and quotient constructions. Thus no passage from a
weak quotient to a head is needed in this assembly.

Apply `glTemperedJointSupport` to the two tensors. It supplies each middle
discrete-series refinement, fine unitary cuspidal support, positive-root
parameter, flattening transport, and all three actual support surjections.
Apply `glSupportedRegularWeylConeComparison` to these two complete telescopes,
the original strictly decreasing parameters and the common quotient maps.
This yields a permutation `w` and, on the full diagonal coordinates,

```
V1(w.symm a) - A1(w.symm a) = V2(a) - A2(a),
```

with both transported closed positive-root cone bounds. Here `Vi` is the
transported fine positive-root parameter repeated on each fine block, while
`Ai` is the original determinant exponent repeated on each coarse block.
The comparison's actual twisted fine-support equivalence has already done
its representation-theoretic work; only its relation and cones are needed
in the remaining numerical step. The original normalization is
`-v + restricted t`. The passage to full diagonal coordinates retains block
size weights on scalar centers.

For each telescope, `supportedRegularWeylParameterNumerics.2.1` supplies the
native cone, orthogonality of `Vi` to `Ai`, and antitonicity of `Ai`.
Apply its two-sided numerical comparison `.2.2` with permutations `w` and
`w.symm`; the reverse relation follows by evaluating the displayed equality
at `w a`. The conclusion is `V1(w.symm a) = V2(a)`. Subtraction in the same
relation yields `A1(a) = A2(w a)`.

Finally `blockParameterPermutationRigidity` converts this matching of the
repeated full-diagonal parameters into an order isomorphism of the original
block index sets preserving both block sizes and determinant exponents.
Its strict-descent hypothesis is exactly the datum's regularity. No weighted
sum condition is imposed on the coarse exponents, so all real central twists
and the one-block case remain covered. No tempered-class recovery or downstream
square-integrable classification is used. The suspect unrestricted wording
of Silberger's Lemma 5.3 and Corollary 5.4 is not used here; analytic comparison
is supplied by the supported published comparison theorem and its dependencies.
