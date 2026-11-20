# Fixed compact normalization for the actual common-Levi tensor

This internal comparison relates the fixed tensor of two compact induction
spaces in `ClosedV31Statement` to the existing compact product section space.
`compactProductRestriction` first changes from positive Levi normalization
to the value-preserving full parabolic normalization. It then restricts the
product section to the compact subgroup and untwists its values. The
smooth-dual untwisting retains the underlying linear functional.

`compactProductTensorEquiv` transports through the actual coefficient fiber
at the trivial parameter. To compare with an arbitrary parameter, the
proof evaluates the transported restriction on pure compact tensors.
Surjectivity of both individual compact restriction equivalences reduces
the evaluation to that of the published tensor induction equivalence.
The same pointwise tensor of the compact factors occurs at each parameter.
Induction on tensors gives the comparison on the whole carrier.

`compactFormalDegreeModel` puts this fixed carrier in the normed space of the
published fixed compact product form. For every unitary parameter the inner
product on the transported coefficient vectors equals the exact
`formalDegreeForm` of `ClosedV31Statement`. The proof uses
`formalDegreeProductInducedCompactEquiv_inner` with the actual normalization
comparison. The compact Haar probabilities, central quotient Haar measure,
and inverse formal degree are those of the given data.

`compactCoefficientAtOne` transports evaluation of the actual coefficient
at the identity through the compact tensor map at the trivial unitary
parameter. The compact integral formula at the identity uses values on the
diagonal of the product compact subgroup. Untwisting preserves their
contraction, so the integral on the fixed compact product space computes
the same transported functional at every unitary parameter.

The constructions supply fixed models for the form and coefficient in
the common-Levi, identity-conjugating-element case of Waldspurger (2003),
Lemma V.3.1, printed p. 295, PDF p. 61. They concern a single parabolic
fiber and give the identities on all its vectors. The preservation
assertions for the comparison between two parabolics require additional
intertwining results.
