# Jacquet quotients of the fixed parabolic support filtration

`PadicParabolicSupportJacquetComparison` is the natural exactness comparison
between two existing constructions. It is a proposition, not its proof.

For every actual finite p-adic extension, compatible supplied topology, rank,
block shapes `B, C`, and actual `OrderedDoubleCosets` datum `s`, the proposition
requires a natural isomorphism at every successive-quotient index `i`. Its source
is exactly `(parabolicJacquetSupportFiltration T B C s).graded i`, the quotient
of successive images of support subspaces in the actual normalized Jacquet
module. Its target first forms
`(parabolicInductionSupportFiltration T B C s).graded i` and then takes
`Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C)`.

Thus the target is the actual radical-coinvariant quotient of the original
successive support quotient, with the Levi section action and inverse positive
half modulus. The support spaces are only representations of `P_C`; no extension
of those subrepresentations to `GL_n` is assumed. Both functors have as their
source the full smooth complex representation category of the source Levi, and
as their target the algebraic representation category of the target Levi.
Field and representation universes are independent. No admissibility,
finite-dimensionality, finite length, minimal representative, intersection
refinement, or positive-rank assumption is needed for this exactness step.

The isomorphism must be natural for every source-Levi intertwiner. The statement
fixes both the support spaces and their images in the ambient quotient; it does
not allow an arbitrary replacement filtration or an added exactness hypothesis.
It supplies neither a compact/smooth induction identification nor the local
orbit comparison with the normalized geometric piece.

## Provenance

This is a derived internal interface for applying exactness to the already
published fixed support-image filtration. The mathematical step appears in
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), sections 5.3–5.4 (printed 461), where exactness identifies localized
support subspaces with subspaces of the ambient localized representation and
then identifies their successive quotients. The registered source is
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Here localization is specialized to ordinary radical coinvariants, followed by
the specified normalizing twist. A proof can use the published generic smooth
coinvariant exactness and finite containment for the actual block radical,
together with the concrete quotient maps and their naturality. It must also
identify the two published presentations of the normalized Levi action. These
are proof obligations; the functor and filtration definitions assert none of
them.
