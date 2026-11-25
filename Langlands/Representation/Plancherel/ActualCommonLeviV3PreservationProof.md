# Exact coefficient and form preservation for the common-Levi tensor

This module supports the proof of the existing actual common-Levi target
`Langlands.Plancherel.ActualCommonLeviV3.ClosedV31Statement`. Its provenance is
Waldspurger (2003), V.3.1 and formula (1), printed p.295 / PDF p.61, with the
source coefficient and inverse-formal-degree normalizations of V.1 and V.2,
printed pp.288–293. The registered original is `waldspurger-2003-plancherel`.
The results below are algebraic transport criteria, not a proof of the closed
analytic target or a new assertion from the original article.

`CompactInduction.leviCoefficientCongrEquiv` constructs an equivalence of the
two actual positive-Levi coefficient representations from an equivalence of
their normalized induced representations. It conjugates the natural
coefficient-tensor transport by the two actual Levi coefficient equivalences.
`leviCoefficientCongrEquiv_square` verifies its canonical tensor square on
every coefficient vector.

`coefficientTensorInvariantForm_congr_of_similitude` proves that a positive
similarity of admissible smooth representations induces an exact isometry of
their coefficient tensors. It combines the published naturality of the actual
smooth-dual Hermitian form with the published cancellation of positive scalar
rescaling between vectors and smooth duals. It assumes neither representation
is irreducible.

`CompactInduction.leviFormalDegreeProductForm_eq_coefficientForm` identifies the
positive-Levi source form with the canonical coefficient-tensor form rescaled
by the same inverse formal degree. It uses the exact compact Haar probability,
central quotient Haar measure, and positive-Levi normalization already present
in `LeviCompactCoefficients`.

`CompactInduction.levi_preserves_of_coefficientTensor_similitude` treats two
actual closed semidirect parabolics with one Levi and one compact open subgroup.
It assumes an intertwiner on their positive-Levi product coefficient objects,
a representation equivalence on the normalized induced representations, the
commuting square with the canonical coefficient-tensor transport, and a
positive similarity of the exact compact induced forms. It concludes
bijectivity, equality of the full coefficient functions for every vector, and
preservation of the exact inverse-formal-degree Hermitian form on every pair
of vectors. The inducing representation is irreducible and square integrable
modulo the displayed central subgroup. No induced irreducibility is used.

The proof obtains bijectivity by conjugating the coefficient-tensor linear
equivalence by the two actual coefficient-model equivalences. The coefficient
identity is the existing pointwise coefficient transport law. The form
identity applies the first lemma and retains the same inverse formal degree
on both sides. Establishing the square and positive similarity for the
particular standard tensor, and producing its algebraic regular extension at
all unitary parameters, are separate obligations, outside this module.
